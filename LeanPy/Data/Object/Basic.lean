/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
syntax Authors Mac Malone
-/
import Std.Data.HashMap
import LeanPy.Data.Object.Id
import LeanPy.Data.HashDict
import LeanPy.Data.AttrName
import LeanPy.Data.IntRef
import LeanPy.Data.StringRef
import LeanPy.Data.MutableRef
import LeanPy.Data.VoidRef
import LeanPy.Util.String

namespace LeanPy

/-! ## Object Data -/

/-- The name of an object's Lean data type. -/
abbrev DataKind := Lean.Name

/-- Dynamic data index by a `DataKind`. -/
structure ObjectData where
  private innerMk ::
    private innerKind : DataKind
    private innerValue : NonScalar
  deriving Nonempty

open TypeName

deriving instance TypeName for Unit

namespace ObjectData

@[inline] private unsafe def mkImpl [TypeName α] (a : α) : ObjectData :=
  unsafeCast a

@[implemented_by mkImpl]
def mk [TypeName α] (a : α) : ObjectData :=
  {innerKind := typeName α, innerValue := unsafe unsafeCast a}

noncomputable def kind (self : ObjectData) : DataKind :=
  self.innerKind

@[simp] theorem kind_mk  [TypeName α] {a : α} : kind (mk a) = typeName α := rfl

@[inline] private unsafe def getImpl
  [Nonempty α] [TypeName α]
  (self : ObjectData) (_ : self.kind = typeName α) : α
:= unsafeCast self

@[implemented_by getImpl]
opaque get
  [Nonempty α] [TypeName α]
  (self : ObjectData) (h : self.kind = typeName α)
: α

end ObjectData

/-! ## Object Type -/

--private def mkTypeName {α : Type u} : TypeName α := sorry

/-- A Python type. -/
structure TypeSpec where
  /-- The type's name -/
  name : String
  /-- The type's documentation string or `none` if undefined. -/
  doc? : Option String := none
  /-- The type's parent. -/
  base? : Option TypeSpec := none
  /--
  Is this type is a legal base for other types.
  If `false`, this type cannot be legally subtyped.

  Equivalent in functionality to CPython's `Py_TPFLAGS_BASETYPE`.
  -/
  isBaseType : Bool := true
  /--
  Is this a subclass of `type`?

  Equivalent in functionality to CPython's `Py_TPFLAGS_TYPE_SUBCLASS`.
  -/
  isTypeSubclass : Bool := false
  /--
  Is this a subclass of `str`?

  Equivalent in functionality to CPython's `Py_TPFLAGS_UNICODE_SUBCLASS`.
  -/
  isStrSubclass : Bool := false
  /--
  Is this a subclass of `int`?

  Equivalent in functionality to CPython's `Py_TPFLAGS_LONG_SUBCLASS`.
  -/
  isIntSubclass : Bool := false
  /-
  Returns whether the field combination could be a valid object of this type.

  This can be an over-approximation. That is, it may hold for objects
  which are not objects of this type.
  -/
  IsValidObject (id : ObjectId) (data : ObjectData) : Prop := True

instance : Nonempty TypeSpec := ⟨{name := default}⟩

namespace TypeSpec

/-- The type's method resolution order. -/
@[inline] def mro (self : TypeSpec) : List TypeSpec :=
  self :: match self with
    | {base? := none, ..} => []
    | {base? := some base, ..} => mro base

@[simp] theorem self_mem_mro : self ∈ mro self := by
  unfold mro; simp

private theorem mem_mro_trans :
  ty₁ ∈ mro ty₂ → ty₂ ∈ mro self → ty₁ ∈ mro self
:= by
  revert ty₂
  match self with
  | {base? := none, ..} =>
    intro ty₂ h₁
    simp only [mro, List.mem_cons, List.not_mem_nil, or_false]
    intro h₂
    simpa [h₂, mro] using h₁
  | {base? := some base, ..} =>
    intro ty₂ h₁
    simp only [mro, List.mem_cons]
    intro h₂
    cases h₂ with
    | inl h₂ => simpa [h₂, mro] using h₁
    | inr h₂ => exact Or.inr <| mem_mro_trans h₁ h₂

def IsSubtype (self other : TypeSpec) : Prop :=
  other ∈ self.mro

instance : HasSubset TypeSpec := ⟨TypeSpec.IsSubtype⟩

theorem subset_iff_mem_mro : a ⊆ b ↔ b ∈ mro a := Iff.rfl

@[simp] theorem subset_rfl {self : TypeSpec} : self ⊆ self :=  self_mem_mro

theorem subset_trans {a b c : TypeSpec} : a ⊆ b → b ⊆ c → a ⊆ c  := by
  simp only [subset_iff_mem_mro]
  exact fun h₁ h₂ => mem_mro_trans h₂ h₁

end TypeSpec

abbrev TypeSpecRef := NonScalarRef TypeSpec

deriving instance TypeName for TypeSpecRef

@[inline] private unsafe def mkTypeSpecRefImpl
  (s : TypeSpec) : BaseIO {r : TypeSpecRef // r.data = s}
:= pure (unsafeCast s)

@[implemented_by mkTypeSpecRefImpl]
opaque mkTypeSpecRef' (s : TypeSpec) : BaseIO {r : TypeSpecRef // r.data = s} :=
  pure ⟨NonScalarRef.null s, NonScalarRef.data_null⟩

@[inline] def mkTypeSpecRef (s : TypeSpec) : BaseIO TypeSpecRef := do
  Subtype.val <$> mkTypeSpecRef' s

/-! ## Builtin types with fast-path type-checking -/

@[reducible] def objectType : TypeSpec where
  name := "object"
  doc? := some "\
    The base class of the class hierarchy.\n\
    \n\
    When called, it accepts no arguments and returns a new featureless\n\
    instance that has no instance attributes and cannot be given any.\n\
  "

@[reducible] def noneType : TypeSpec where
  name := "NoneType"
  base? := some objectType
  IsValidObject id data :=
    id = .none ∧ data = .mk ()

@[reducible] def typeType : TypeSpec where
  name := "type"
  doc? := some "\
    type(object) -> the object's type\n\
    type(name, bases, dict, **kwds) -> a new type\
  "
  isTypeSubclass := true
  base? := some objectType
  IsValidObject id data :=
    id.isNonScalar ∧ data.kind = typeName TypeSpecRef

@[reducible] def strType : TypeSpec where
  name := "str"
  doc? := some "\
    str(object='') -> str\n\
    str(bytes_or_buffer[, encoding[, errors]]) -> str\n\
    \n\
    Create a new string object from the given object. If encoding or\n\
    errors is specified, then the object must expose a data buffer\n\
    that will be decoded using the given encoding and error handler.\n\
    Otherwise, returns the result of object.__str__() (if defined)\n\
    or repr(object).\n\
    encoding defaults to sys.getdefaultencoding().\n\
    errors defaults to 'strict'.\
  "
  isStrSubclass := true
  base? := some objectType
  IsValidObject id data :=
    id.isNonScalar ∧ data.kind = typeName StringRef

@[reducible] def intType : TypeSpec where
  name := "int"
  doc? := some "\
    int([x]) -> integer\n\
    int(x, base=10) -> integer\n\
    \n\
    Convert a number or string to an integer, or return 0 if no arguments\n\
    are given.  If x is a number, return x.__int__().  For floating point\n\
    numbers, this truncates towards zero.\n\
    \n\
    If x is not a number or if base is given, then x must be a string,\n\
    bytes, or bytearray instance representing an integer literal in the\n\
    given base.  The literal can be preceded by '+' or '-' and be surrounded\n\
    by whitespace.  The base defaults to 10.  Valid bases are 0 and 2-36.\n\
    Base 0 means to interpret the base from the string as an integer literal.\n\
    >>> int('0b100', base=0)\n\
    4\
  "
  isIntSubclass := true
  base? := some objectType
  IsValidObject _ data :=
    data.kind = typeName IntRef -- TODO: id.isInt

@[reducible] def boolType : TypeSpec where
  name := "bool"
  doc? := some "\
    bool(x) -> bool\n\
    \n\
    Returns True when the argument x is true, False otherwise.\n\
    The builtins True and False are the only two instances of the class bool.\n\
    The class bool is a subclass of the class int, and cannot be subclassed.\
  "
  base? := some intType
  isIntSubclass := true
  IsValidObject id data :=
    id = .false ∧ data = .mk (0 : IntRef) ∨
    id = .true ∧ data = .mk (1 : IntRef)

/-! ## LawfulType -/

class LawfulType (self : TypeSpec) : Prop where
  isTypeSubclass_iff_subset :
    self.isTypeSubclass ↔ self ⊆ typeType := by
      simp [TypeSpec.subset_iff_mem_mro, TypeSpec.mro]
  isIntSubclass_iff_subset :
    self.isIntSubclass ↔ self ⊆ intType := by
      simp [TypeSpec.subset_iff_mem_mro, TypeSpec.mro]
  isStrSubclass_iff_subset :
    self.isStrSubclass ↔ self ⊆ strType := by
      simp [TypeSpec.subset_iff_mem_mro, TypeSpec.mro]
  isValidObject_mro : ∀ {id data},
    self.IsValidObject id data → ∀ {ty}, self ⊆ ty → ty.IsValidObject id data
  := by simp [TypeSpec.subset_iff_mem_mro, TypeSpec.mro]

namespace TypeSpec
export LawfulType (
  isTypeSubclass_iff_subset isIntSubclass_iff_subset isStrSubclass_iff_subset
  isValidObject_mro
)
end TypeSpec

instance : LawfulType objectType where
instance : LawfulType typeType where
instance : LawfulType noneType where
instance : LawfulType strType where
instance : LawfulType intType where
instance : LawfulType boolType where
  isValidObject_mro := by
    simp only
    rintro _ _ ⟨_ | _⟩
    all_goals simp_all [TypeSpec.subset_iff_mem_mro, TypeSpec.mro]

/-! ## TypeSlotsRef -/

/-- A reference to a `TypeSlots` structure. -/
structure TypeSlotsRef where
  private innerMk ::
    private innerTy : TypeSpec
  deriving Nonempty

noncomputable def TypeSlotsRef.ty (self : TypeSlotsRef) : TypeSpec :=
  self.innerTy

theorem TypeSlotsRef.ty_inj : ty a = ty b ↔ a = b := by
  cases a; cases b; simp [ty]

structure DTypeSlotsRef (ty : TypeSpec) extends TypeSlotsRef where
  ty_eq : toTypeSlotsRef.ty = ty := by rfl

attribute [simp] DTypeSlotsRef.ty_eq

instance : CoeOut (DTypeSlotsRef ty) TypeSlotsRef :=
  ⟨DTypeSlotsRef.toTypeSlotsRef⟩

instance : Nonempty (DTypeSlotsRef ty) := ⟨{innerTy := ty}⟩

/-! ## Object -/

/-- A Python object. -/
structure Object where
  mk' ::
    /--
    The object's id.

    See `ObjectId` for details on how LeanPy encodes object identities.
    -/
    id : ObjectId
    /-- The object's Python type. -/
    ty : TypeSpec
    /-- The type's slots. Used to optimize magic methods. -/
    rawSlots : TypeSlotsRef
    /-- The object's Lean data. -/
    data : ObjectData
    /- Well-formed-ness -/
    [lawful_ty : LawfulType ty]
    lawful_none : id = .none → ty = noneType := by simp
    lawful_slots : rawSlots.ty = ty := by simp
    lawful_object : ty.IsValidObject id data := by simp

instance {self : Object} : LawfulType self.ty := self.lawful_ty

structure PObject (p : TypeSpec → Prop) extends Object where
  property : p ty

instance : CoeOut (PObject p) Object :=
  ⟨PObject.toObject⟩

@[inline] def PObject.cast (self : PObject p) (h : p self.ty → q self.ty) : PObject q :=
  ⟨self.toObject, h self.property⟩

abbrev SubObject (ty : TypeSpec) := PObject (· ⊆ ty)

theorem SubObject.ty_subset (self : SubObject ty) : self.ty ⊆ ty :=
  self.property

@[inline] def SubObject.upcast (self : SubObject ty₁) (h : ty₁ ⊆ ty₂) : SubObject ty₂ :=
  self.cast (TypeSpec.subset_trans · h)

theorem SubObject.lawful_subobject {self : SubObject ty} :
  ty.IsValidObject self.id self.data
:= self.ty.isValidObject_mro self.lawful_object self.ty_subset

abbrev ObjectObject := SubObject objectType

@[inline] def Object.toSubObject (self : Object) : SubObject self.ty :=
  ⟨self, TypeSpec.subset_rfl⟩

/-! `PyM` -/

abbrev AttrDict := HashDict AttrName Object

/-- A Python exception. -/
-- TODO: Derive from `BaseException`
abbrev ErrorObject := Object

/-- Mutable dictionary. -/
abbrev Dict := MutableRef (HashDict Object (MutableRef Object))

/-- Mutable dictionary of variables. -/
abbrev VarDict := MutableRef AttrDict

structure PyContext where
  globals : VarDict
  locals : VarDict := globals

/-- The monad of Python code. -/
abbrev PyM := ReaderT PyContext <| EIO ErrorObject

/-! ## Object Basics -/

namespace Object

def mk
  [TypeName α] (id : ObjectId)
  (ty : TypeSpec) [LawfulType ty]
  (slots : DTypeSlotsRef ty) (data : α)
  (h : ty.IsValidObject id (.mk data) := by simp)
  (h_none : id = .none → ty = noneType := by simp)
: Object where
  id; ty
  rawSlots := slots
  data := ObjectData.mk data
  lawful_slots := slots.ty_eq
  lawful_none := h_none
  lawful_object := h

@[inline] def getData
  [Nonempty α] [TypeName α] (self : Object) (h : self.data.kind = typeName α)
: α := self.data.get h

protected def toString (self : Object) : String :=
  s!"<{self.ty.name} object at 0x{self.id.hex}>"

instance : ToString Object := ⟨Object.toString⟩

end Object

/-! ## Slots -/

/-- Untyped object slots. -/
structure TypeSlots (α : Type u) where
  /-- The type's `__hash__` slot.  -/
  hash (self : α) : PyM Hash
  /-- The type's `==` slot. Unlike `__eq__`, this returns `Bool`.  -/
  beq (self : α) (other : Object) : PyM Bool
  /-- The type's `!=` slot. Unlike `__ne__`, this returns `Bool`. -/
  bne (self : α) (other : Object) : PyM Bool := Bool.not <$> beq self other
  /-- The type's `__bool__` slot.  -/
  bool (self : α) : PyM Bool
  /-- The type's `__repr__` slot.  -/
  repr (self : α) : PyM String
  /-- The type's `__str__` slot.  -/
  str (self : α) : PyM String := repr self
  deriving Nonempty

/-- Slots compatible with instances of types that satisfy `p`. -/
abbrev PTypeSlots (p : TypeSpec → Prop) := TypeSlots (PObject p)

/-- Slots compatible with instances of `ty` or its subtypes. -/
abbrev SubTypeSlots (ty : TypeSpec) := TypeSlots (SubObject ty)

@[inline] private unsafe def TypeSlots.castImpl
  (slots : TypeSlots (PObject p)) (_ : ∀ {ty}, q ty → p ty)
: (PTypeSlots q) := unsafeCast slots

@[implemented_by castImpl]
def TypeSlots.impCast
   (slots : TypeSlots (PObject p)) (h : ∀ {ty}, q ty → p ty)
: (PTypeSlots q) where
  hash self := slots.hash (self.cast h)
  beq self other := slots.beq (self.cast h) other
  bne self other := slots.beq (self.cast h) other
  bool self := slots.bool (self.cast h)
  repr self := slots.repr (self.cast h)
  str self := slots.str (self.cast h)

@[inline] def TypeSlots.downcast
  (h : ty₂ ⊆ ty₁)  (slots : TypeSlots (SubObject ty₁)) : TypeSlots (SubObject ty₂)
:= slots.impCast (fun h' => TypeSpec.subset_trans h' h)

@[inline] def TypeSlots.eqCast
  (h : ty₁ = ty₂)  (slots : TypeSlots (SubObject ty₁)) : TypeSlots (SubObject ty₂)
:= slots.impCast (fun h' => h ▸ h')

@[inline] private unsafe def TypeSlots.mkRefImpl
  (slots : TypeSlots (SubObject ty)) :  BaseIO (DTypeSlotsRef ty)
:= pure (unsafeCast slots)

@[implemented_by mkRefImpl]
opaque TypeSlots.mkRef
  (slots : TypeSlots (SubObject ty)) : BaseIO (DTypeSlotsRef ty)

@[inline] private unsafe def TypeSlotsRef.getImpl
  (self : TypeSlotsRef) : BaseIO (SubTypeSlots self.ty)
:= pure (unsafeCast self)

@[implemented_by getImpl]
opaque TypeSlotsRef.get
  (self : TypeSlotsRef) : BaseIO (SubTypeSlots self.ty)

@[inline] def DTypeSlotsRef.get
  (self : DTypeSlotsRef ty) : BaseIO (SubTypeSlots ty)
:= (·.eqCast self.ty_eq) <$> self.toTypeSlotsRef.get

/-! ## Slot-based Methods -/

@[inline] def Object.slots (self : Object) : DTypeSlotsRef self.ty :=
  ⟨self.rawSlots, self.lawful_slots⟩

@[inline] def Object.hashM (self : Object) : PyM Hash := do
  (← self.slots.get).hash self.toSubObject

@[inline] def Object.beqM (self other : Object) : PyM Bool := do
  (← self.slots.get).beq self.toSubObject other

@[inline] def Object.bneM (self other : Object) : PyM Bool := do
  (← self.slots.get).bne self.toSubObject other

@[inline] def Object.reprM (self : Object) : PyM String := do
  (← self.slots.get).repr self.toSubObject

@[inline] def Object.toStringM (self : Object) : PyM String := do
  (← self.slots.get).str self.toSubObject

@[inline] def Object.toBoolM (self : Object) : PyM Bool := do
  (← self.slots.get).bool self.toSubObject

/-! ## `object` -/

/-- Returns the hash of the object's id. -/
@[inline] protected def Object.hash (self : Object) : Hash :=
  hash self.id

/--
Returns whether two objects are identical (have the same id).

This is equivalent to the Python `self is other`.
-/
@[inline] protected def Object.beq (self other : Object) : Bool :=
  self.id == other.id

/--
Returns whether two objects are not identical (do not have the same id).

This is equivalent to the Python `self is not other`.
-/
@[inline] protected def Object.bne (self other : Object) : Bool :=
  self.id != other.id

def objectTypeSlots : SubTypeSlots objectType where
  hash self := return self.hash
  beq self other := return self.beq other
  bne self other := return self.bne other
  bool _ := return true
  repr self := return self.toString

initialize objectTypeSlotsRef : DTypeSlotsRef objectType ←
  objectTypeSlots.mkRef

def ObjectObject.ofVoidRef (ref : VoidRef) : ObjectObject :=
  Object.mk ref.id objectType objectTypeSlotsRef ref |>.toSubObject

def mkObjectObject : BaseIO ObjectObject := do
  ObjectObject.ofVoidRef <$> mkVoidRef

/-! ## `type` -/

/- An instance of `type` or one of its subtypes. -/
def TypeObject := SubObject typeType

/-- Returns whether this object is an instance of a subtype of `type`. -/
@[inline] def Object.isType (self : Object) : Bool :=
  self.ty.isTypeSubclass

/-- Casts `self` to `TypeObject`. -/
@[inline] def Object.asType (self : Object) (h : self.isType) : TypeObject :=
  ⟨self, self.ty.isTypeSubclass_iff_subset |>.mp h⟩

/--
Casts `self` to `TypeObject` if `self` is instance of a subtype of `type`.
Otherwise, returns `none`.
-/
@[inline] def Object.asType? (self : Object) : Option TypeObject :=
  if h : self.isType then some (self.asType h) else none

namespace TypeObject

instance : Coe TypeObject Object := ⟨PObject.toObject⟩

theorem isType_toObject (self : TypeObject) : self.toObject.isType :=
  self.ty.isTypeSubclass_iff_subset.mpr self.ty_subset

@[inline] def getTypeSpecRef (self : TypeObject) : TypeSpecRef :=
  self.getData (self.lawful_subobject).2

@[inline] def getTypeSpec (self : TypeObject) : TypeSpec :=
  self.getTypeSpecRef.data

def name (self : TypeObject) : String :=
  self.getTypeSpec.name

def repr (self : TypeObject) : String :=
  s!"<class '{self.name}'>"

end TypeObject

def typeTypeSlots : TypeSlots TypeObject where
  hash self := return self.hash
  beq self other := return self.beq other
  bne self other := return self.bne other
  bool _ := return true
  repr self := return self.repr

initialize typeTypeSlotsRef : DTypeSlotsRef typeType ←
  typeTypeSlots.mkRef

def mkTypeObject (spec : TypeSpec) : BaseIO Object := do
  let ref ← mkTypeSpecRef spec
  return .mk ref.id typeType typeTypeSlotsRef ref

/-! ## None -/

/--
Returns whether this object the constant `None`.

Equivalent to the Python `self is None`.
-/
@[inline] def Object.isNone (self : Object) : Bool :=
  self.id == .none

def noneHash : Hash :=
  hash ObjectId.none

def noneTypeSlots : SubTypeSlots noneType where
  hash _ := return noneHash
  beq _ other := return other.id == .none
  bne _ other := return other.id != .none
  bool _ := return false
  repr _ := return "None"

initialize noneTypeSlotsRef : DTypeSlotsRef noneType ←
  noneTypeSlots.mkRef

protected def Object.none : Object :=
  .mk .none noneType noneTypeSlotsRef ()

instance : CoeDep (Option α) none Object := ⟨.none⟩

@[simp] theorem Object.isNone_none : isNone none := rfl

theorem Object.isNone_iff_eq_none : isNone self ↔ self = none := by
  let {lawful_none, lawful_slots, lawful_object, ..} := self
  simp only [Object.none, mk, mk'.injEq]
  simp only [isNone, beq_iff_eq, iff_self_and]
  intro id_eq
  have ty_eq := lawful_none id_eq
  have data_eq := (ty_eq ▸ lawful_object).2
  simp [ty_eq, data_eq, ← TypeSlotsRef.ty_inj, lawful_slots]

instance : Inhabited Object := ⟨none⟩

/-! ## `str` Objects -/

/-- Returns the Python string representation of a `String`. -/
def strRepr (s : String) : String :=
  let q := if s.contains '\'' && !s.contains '"' then '"' else '\''
  go s q 0 ("".push q) |>.push q
where
  go s q p ns : String :=
    if h : s.atEnd p then
      ns
    else
      let c := s.get' p h
      let p' := s.next' p h
      if c == q then
        go s q p' (ns.push '\\' |>.push q)
      else if c == '\\' then
        go s q p' (ns.push '\\' |>.push '\\')
      else if c == '\t' then
        go s q p' (ns.push '\\' |>.push 't')
      else if c == '\r' then
        go s q p' (ns.push '\\' |>.push 'r')
      else if c == '\n' then
        go s q p' (ns.push '\\' |>.push 'n')
      else if c.val < 0x20 || c.val == 0x7f then
        go s q p' (upperHexUInt8 c.val.toUInt8 (ns.push '\\' |>.push 'x'))
      else if c.val < 0x7f || isPrintableUnicode c then
        go s q p' (ns.push c)
      else if c.val < 0x100 then
        go s q p' (upperHexUInt8 c.val.toUInt8 (ns.push '\\' |>.push 'x'))
      else if c.val < 0x10000 then
        go s q p' (upperHexUInt16 c.val.toUInt16 (ns.push '\\' |>.push 'u'))
      else
        go s q p' (upperHexUInt32 c.val (ns.push '\\' |>.push 'U'))
  termination_by s.utf8ByteSize - p.byteIdx
  decreasing_by all_goals
    apply Nat.sub_lt_sub_left
    · simpa [String.atEnd] using h
    · exact String.lt_next' ..
  @[inline] isPrintableUnicode c :=
    -- TODO: Use unicode definition once Lean has support for it
    Lean.isLetterLike c

/- An instance of `str` or one of its subtypes. -/
def StrObject := SubObject strType

/-- Returns whether this object is an instance of a subtype of `str`. -/
@[inline] def Object.isStr (self : Object) : Bool :=
 self.ty.isStrSubclass

/-- Casts `self` to `StrObject`. -/
@[inline] def Object.asStr (self : Object) (h : self.isStr) : StrObject :=
  ⟨self, self.ty.isStrSubclass_iff_subset.mp h⟩

/--
Casts `self` to `StrObject` if `self` is instance of a subtype of `str`.
Otherwise, returns `none`.
-/
@[inline] def Object.asStr? (self : Object) : Option StrObject :=
  if h : self.isStr then some (self.asStr h) else none

namespace StrObject

instance : Coe StrObject Object := ⟨PObject.toObject⟩

theorem isStr_toObject (self : StrObject) : self.toObject.isStr :=
  self.ty.isStrSubclass_iff_subset.mpr self.ty_subset

@[inline] def getStringRef (self : StrObject) : StringRef :=
  self.getData (self.lawful_subobject).2

@[inline] def getString (self : StrObject) : String :=
  self.getStringRef.data

@[inline] protected def toString (self : StrObject) : String :=
  self.getString

@[inline] protected def beq (self other : StrObject) : Bool :=
  self.getString == other.getString

@[inline] protected def bne (self other : StrObject) : Bool :=
  self.getString != other.getString

@[inline] protected def hash (self : StrObject) : Hash :=
  hash self.getString -- TODO: salt hash?

@[inline] def length (self : StrObject) : Nat :=
  self.getString.length

@[inline] def toBool (self : StrObject) : Bool :=
  self.length != 0

@[inline] def repr (self : StrObject) : String :=
  strRepr self.getString

end StrObject

def strTypeSlots : TypeSlots StrObject where
  hash self := return self.hash
  beq self other := return other.asStr?.any self.beq
  bne self other := return other.asStr?.all self.bne
  bool self := return self.toBool
  str self := return self.toString
  repr self := return self.repr

initialize strTypeSlotsRef : DTypeSlotsRef strType ←
  strTypeSlots.mkRef

@[inline] def StrObject.ofStringRef (r : StringRef) : StrObject :=
  Object.mk r.id strType strTypeSlotsRef r |>.toSubObject

@[inline] def mkStrObject (s : String) : BaseIO StrObject := do
  StrObject.ofStringRef <$> mkStringRef s

/-! ## `int` Objects -/

/- An instance of a subclass of `str`. -/
def IntObject := SubObject intType

@[inline] def Object.isInt (self : Object) : Bool :=
  self.ty.isIntSubclass

@[inline] def Object.asInt (self : Object) (h : self.isInt) : IntObject :=
  ⟨self, self.ty.isIntSubclass_iff_subset.mp h⟩

@[inline] def Object.asInt? (self : Object) : Option IntObject :=
  if h : self.isInt then some (self.asInt h) else none

namespace IntObject

instance : Coe IntObject Object := ⟨PObject.toObject⟩

theorem isInt_toObject (self : IntObject) : self.toObject.isInt :=
  self.ty.isIntSubclass_iff_subset.mpr self.ty_subset

@[inline] def getIntRef (self : IntObject) : IntRef :=
  self.getData self.lawful_subobject

@[inline] def getInt (self : IntObject) : Int :=
  self.getIntRef.toInt

@[inline] protected def beq (self other : IntObject) : Bool :=
  self.getInt == other.getInt

@[inline] protected def bne (self other : IntObject) : Bool :=
  self.getInt != other.getInt

@[inline] protected def hash (self : IntObject) : Hash :=
  hash self.getInt

@[inline] def toBool (self : IntObject) : Bool :=
  self.getInt != 0

@[inline] def repr (self : IntObject) : String :=
  toString self.getInt

end IntObject

def intTypeSlots : TypeSlots IntObject where
  hash self := return self.hash
  beq self other := return other.asInt?.any self.beq
  bne self other := return other.asInt?.all self.bne
  bool self := return self.toBool
  str self := return self.toString
  repr self := return self.repr

initialize intTypeSlotsRef : DTypeSlotsRef intType ←
  intTypeSlots.mkRef

@[inline] def IntObject.ofIntRef (n : IntRef) : IntObject :=
  Object.mk n.id intType intTypeSlotsRef n |>.toSubObject

instance : OfNat IntObject 0 := ⟨.ofIntRef 0⟩
instance : OfNat Object 0 := ⟨(0 : IntObject)⟩
instance : Coe IntRef IntObject := ⟨.ofIntRef⟩

theorem IntObject.zero_eq : (0 : IntObject) = .ofIntRef 0 := rfl

@[inline] def mkIntObject (n : Int) : BaseIO IntObject := do
  IntObject.ofIntRef <$> mkIntRef n

/-! ## `bool` Objects -/

theorem boolType_subset_intType : boolType ⊆ intType := by
  simp [boolType, TypeSpec.subset_iff_mem_mro, TypeSpec.mro]

def boolTypeSlots : SubTypeSlots boolType :=
  let repr b := return if b.getInt != 0 then "True" else "False"
  let slots : TypeSlots IntObject := {
    intTypeSlots with
    repr, str := repr
  }
  slots.downcast boolType_subset_intType

initialize boolTypeSlotsRef : DTypeSlotsRef boolType ←
  boolTypeSlots.mkRef

protected def Object.false : Object :=
  .mk .false boolType boolTypeSlotsRef (0 : IntRef)

instance : CoeDep Bool false Object := ⟨Object.false⟩

protected def Object.true : Object :=
  .mk .true boolType boolTypeSlotsRef (1 : IntRef)

instance : CoeDep Bool true Object := ⟨Object.true⟩

def Object.ofBool (b : Bool) : Object :=
  if b then true else false

instance : Coe Bool Object := ⟨Object.ofBool⟩
