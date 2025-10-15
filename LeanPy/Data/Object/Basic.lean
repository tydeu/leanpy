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

instance : TypeName Unit := unsafe (.mk _ ``Unit)

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

instance : TypeName TypeSpecRef := unsafe (.mk _ ``TypeSpecRef)

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
    (id = .false ∨ id = .true) ∧
    (id = .false → data = .mk (0 : IntRef)) ∧
    (id = .true → data = .mk (1 : IntRef)) ∧
    data.kind = typeName IntRef -- redundant, but makes `simp_all` work bellow

/-! ## LawfulType -/

class LawfulType (self : TypeSpec) : Prop where
  subset_objectType : self ⊆ objectType := by
    simp [TypeSpec.subset_iff_mem_mro, TypeSpec.mro]
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
  := by simp_all [TypeSpec.subset_iff_mem_mro, TypeSpec.mro]

namespace TypeSpec
export LawfulType (
  subset_objectType
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

/-- A raw Python object without validity proofs. -/
structure Object.Raw where mk ::
  /--
  The object's id.

  See `ObjectId` for details on how LeanPy encodes object identities.
  -/
  protected id : ObjectId
  /-- The object's Python type. -/
  protected ty : TypeSpec
  /-- The type's slots. Used to optimize magic methods. -/
  innerSlots : TypeSlotsRef
  /-- The object's Lean data. -/
  data : ObjectData

/-- A Python object. -/
structure Object extends raw : Object.Raw where mk' ::
  [lawful_ty : LawfulType ty]
  lawful_none : id = .none → ty = noneType := by simp
  lawful_bool : id = .false ∨ id = .true → ty = boolType := by simp
  lawful_slots : innerSlots.ty = ty := by simp
  lawful_object : ty.IsValidObject id data := by simp

instance {self : Object} : LawfulType self.ty := self.lawful_ty

/-! ## TypeProp -/

/--
A predicate about a type.
Used to encode Python type relations in Lean types.
-/
abbrev TypeProp := TypeSpec → Prop

def TypeProp.Any : TypeProp :=
  fun _ => True

def TypeProp.Subtype (p : TypeProp) (ty : TypeSpec) : TypeProp :=
  fun t => p t ∧ t ⊆ ty

theorem TypeProp.Subtype.property (h : Subtype p ty t) : p t :=
  h.1

theorem TypeProp.Subtype.ty_subset (h : Subtype p ty t) : t ⊆ ty :=
  h.2

theorem TypeProp.Subtype.trans (h : ty₁ ⊆ ty₂) (h₁ : Subtype p ty₁ t) : Subtype p ty₂ t :=
  ⟨h₁.1, TypeSpec.subset_trans h₁.2 h⟩

/-! ## Object Subtypes -/

structure PObject (p : TypeProp) extends Object where
  inner_property : p ty

theorem PObject.property (self : PObject p) : p self.ty :=
  self.inner_property

instance : CoeOut (PObject p) Object :=
  ⟨PObject.toObject⟩

@[inline] def Object.cast (self : Object) (h : p self.ty) : PObject p :=
  ⟨self, h⟩

/-- An object whose type satisfies `p` and is a subtype of `ty`, -/
abbrev PSubObject (p : TypeProp) (ty : TypeSpec) :=
  PObject (p.Subtype ty)

/--
An object whose type satisfies `p` and is a subtype of `subTy`,
which is a subtype of `superTy`.
-/
abbrev PSubSubObject (p : TypeProp) (subTy superTy : TypeSpec) :=
  PSubObject (p.Subtype subTy) superTy

abbrev SubObject (ty : TypeSpec) := PSubObject .Any ty

@[inline] def Object.toPObject (self : Object) : PObject .Any :=
  self.cast .intro

@[inline] def Object.downcast (self : Object) (h : self.ty ⊆ ty) : SubObject ty :=
  self.cast ⟨.intro, h⟩

@[inline] def Object.toSubObject (self : Object) : SubObject self.ty :=
  self.downcast TypeSpec.subset_rfl

@[inline] def PObject.upcast
  (self : PSubObject p subTy) (h : subTy ⊆ superTy)
: PSubSubObject p subTy superTy :=
  self.cast ⟨self.property, TypeSpec.subset_trans self.property.2 h⟩

theorem PObject.ty_subset {self : PSubObject p ty} : self.ty ⊆ ty :=
  self.property.2

theorem Object.lawful_subobject
  {self : Object} (h : self.ty ⊆ ty) : ty.IsValidObject self.id self.data
:= self.ty.isValidObject_mro self.lawful_object h

theorem PObject.lawful_subobject
  {self : PSubObject p ty} : ty.IsValidObject self.id self.data
:= self.toObject.lawful_subobject self.property.ty_subset

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
  (h_bool : id = .false ∨ id = .true → ty = boolType := by simp)
: Object where
  id; ty
  innerSlots := slots
  data := ObjectData.mk data
  lawful_slots := slots.ty_eq
  lawful_none := h_none
  lawful_bool := h_bool
  lawful_object := h

@[inline] def getData
  [Nonempty α] [TypeName α] (self : Object) (h : self.data.kind = typeName α)
: α := self.data.get h

theorem eq_iff (self other : Object) :
  self = other ↔
  self.id = other.id ∧ self.ty = other.ty ∧ self.data = other.data
:= by
  let {lawful_slots := h1, ..} := self
  let {lawful_slots := h2, ..} := other
  simp [mk'.injEq, ← TypeSlotsRef.ty_inj, h1, h2]

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
  (_ : ∀ {ty}, q ty → p ty) (slots : TypeSlots (PObject p))
: (PTypeSlots q) := unsafeCast slots

@[implemented_by castImpl]
def TypeSlots.impCast
  (h : ∀ {ty}, q ty → p ty) (slots : TypeSlots (PObject p))
: (PTypeSlots q) where
  hash self := slots.hash (self.cast (h self.property))
  beq self other := slots.beq (self.cast (h self.property)) other
  bne self other := slots.beq (self.cast (h self.property)) other
  bool self := slots.bool (self.cast (h self.property))
  repr self := slots.repr (self.cast (h self.property))
  str self := slots.str (self.cast (h self.property))

@[inline] def TypeSlots.downcast
  (h : subTy ⊆ superTy) (slots : TypeSlots (PSubObject p superTy))
: TypeSlots (PSubSubObject p subTy superTy) :=
  slots.impCast (fun hp => hp.property.trans h)

@[inline] def TypeSlots.stripCast
  (h : subTy ⊆ superTy) (slots : TypeSlots (PSubSubObject p subTy superTy))
: TypeSlots (PSubObject p subTy) :=
  slots.impCast (fun hp => ⟨hp, TypeSpec.subset_trans hp.ty_subset h⟩)

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

/-! ## Slot-based Methods -/

@[inline] def Object.getSlots (self : Object) : BaseIO (SubTypeSlots self.ty) :=
  (·.eqCast self.lawful_slots) <$> self.innerSlots.get

@[inline] def Object.hashM (self : Object) : PyM Hash := do
  (← self.getSlots).hash self.toSubObject

@[inline] def Object.beqM (self other : Object) : PyM Bool := do
  (← self.getSlots).beq self.toSubObject other

@[inline] def Object.bneM (self other : Object) : PyM Bool := do
  (← self.getSlots).bne self.toSubObject other

@[inline] def Object.reprM (self : Object) : PyM String := do
  (← self.getSlots).repr self.toSubObject

@[inline] def Object.toStringM (self : Object) : PyM String := do
  (← self.getSlots).str self.toSubObject

@[inline] def Object.toBoolM (self : Object) : PyM Bool := do
  (← self.getSlots).bool self.toSubObject

/-! ## `object` -/

/- An instance of a subclass of `object` that satisfies `p`. -/
abbrev PObjectObject (p : TypeProp) := PObject (p.Subtype objectType)

/--
An instance of `object` or one of its subtypes interpreted as an `object`.

Pure Lean operations on this type are their `object` variants,
they do not dispatch to the methods on the object's real type.
For example, given `self : ObjectObject`, the Lean `self.hash`
is `object.__hash__(self)` in Python, not `hash(self)`.
-/
def ObjectObject := PObjectObject .Any

/-- Casts `self` to `ObjectObject` (`object`). -/
@[inline] def Object.asObject (self : Object) : ObjectObject :=
  self.downcast self.ty.subset_objectType

instance : Coe Object ObjectObject := ⟨Object.asObject⟩

namespace ObjectObject

/--
Returns the hash of the object's id.

This is equivalent to the Python `object.__hash__(self)`.
-/
@[inline] protected def hash (self : ObjectObject) : Hash :=
  hash self.id

/--
Returns whether two objects are identical (have the same id).

This is equivalent to the Python `self is other`.
-/
@[inline] protected def beq (self other : ObjectObject) : Bool :=
  self.id == other.id

/--
Returns whether two objects are not identical (do not have the same id).

This is equivalent to the Python `self is not other`.
-/
@[inline] protected def bne (self other : ObjectObject) : Bool :=
  self.id != other.id

/--
Returns a string representation of the object.

This is equivalent to the Python `object.__repr__(self)`.
-/
protected def repr (self : ObjectObject) : String :=
  s!"<{self.ty.name} object at 0x{self.id.hex}>"

end ObjectObject

instance : ToString Object := ⟨(·.asObject.repr)⟩

def objectTypeSlots : TypeSlots ObjectObject where
  hash self := return self.hash
  beq self other := return self.beq other
  bne self other := return self.bne other
  bool _ := return true
  repr self := return self.repr

initialize objectTypeSlotsRef : DTypeSlotsRef objectType ←
  objectTypeSlots.mkRef

def ObjectObject.ofVoidRef (ref : VoidRef) : ObjectObject :=
  Object.mk ref.id objectType objectTypeSlotsRef ref |>.toSubObject

def mkObjectObject : BaseIO ObjectObject := do
  ObjectObject.ofVoidRef <$> mkVoidRef

/-! ## `type` -/

/- An instance of a subclass of `type` that satisfies `p`. -/
abbrev PTypeObject (p : TypeProp) := PSubObject p typeType

/- An instance of `type` or one of its subtypes. -/
def TypeObject := PTypeObject .Any

/-- Returns whether this object is an instance of a subtype of `type`. -/
@[inline] def Object.isType (self : Object) : Bool :=
  self.ty.isTypeSubclass

/-- Casts `self` to `TypeObject`. -/
@[inline] def Object.asType (self : Object) (h : self.isType) : TypeObject :=
  self.downcast (self.ty.isTypeSubclass_iff_subset.mp h)

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
  hash self := return self.asObject.hash
  beq self other := return self.asObject.beq other
  bne self other := return self.asObject.bne other
  bool _ := return true
  repr self := return self.repr

initialize typeTypeSlotsRef : DTypeSlotsRef typeType ←
  typeTypeSlots.mkRef

def mkTypeObject (spec : TypeSpec) : BaseIO Object := do
  let ref ← mkTypeSpecRef spec
  return .mk ref.id typeType typeTypeSlotsRef ref

/-! ## None -/

/- An instance of type `none`. There is only one, `None`. -/
def NoneObject := SubObject noneType

/--
Returns whether this object is the constant `None`.

Equivalent to the Python `self is None`.
-/
@[inline] def Object.isNone (self : Object) : Bool :=
  self.id == .none

/--
Returns whether this object is not the constant `None`.

Equivalent to the Python `self is not None`.
-/
@[inline] def Object.isNotNone (self : Object) : Bool :=
  self.id != .none

namespace NoneObject

instance : Coe NoneObject Object := ⟨PObject.toObject⟩

protected def hash : Hash :=
  hash ObjectId.none

protected def repr : String :=
  "None"

end NoneObject

def noneTypeSlots : SubTypeSlots noneType where
  hash _ := return NoneObject.hash
  beq _ other := return other.isNone
  bne _ other := return other.isNotNone
  bool _ := return false
  repr _ := return NoneObject.repr

initialize noneTypeSlotsRef : DTypeSlotsRef noneType ←
  noneTypeSlots.mkRef

namespace Object

protected def none : NoneObject :=
  Object.mk .none noneType noneTypeSlotsRef () |>.toSubObject

instance : CoeDep (Option α) none Object := ⟨Object.none⟩
instance : CoeDep (Option α) none NoneObject := ⟨Object.none⟩

@[simp] theorem isNone_none : isNone none := rfl

@[simp] theorem id_none : (none : Object).id = .none := rfl
@[simp] theorem ty_none : (none : Object).ty = noneType := rfl
@[simp] theorem data_none : (none : Object).data = .mk () := rfl

theorem isNone_iff_eq_none : isNone self ↔ self = none := by
  simp only [isNone, id_none, eq_iff, beq_iff_eq, iff_self_and]
  intro id_eq
  have ty_eq := self.lawful_none id_eq
  have data_eq := (ty_eq ▸ self.lawful_object).2
  simp [ty_eq, data_eq]

instance : Inhabited Object := ⟨none⟩

end Object

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

/- An instance of a subclass of `str` that satisfies `p`. -/
abbrev PStrObject (p : TypeProp) := PSubObject p strType

/- An instance of a subclass of `str`. -/
def StrObject := PStrObject .Any

/-- Returns whether this object is an instance of a subtype of `str`. -/
@[inline] def Object.isStr (self : Object) : Bool :=
 self.ty.isStrSubclass

/-- Casts `self` to `StrObject`. -/
@[inline] def Object.asStr (self : Object) (h : self.isStr) : StrObject :=
  self.downcast (self.ty.isStrSubclass_iff_subset.mp h)

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

/- An instance of a subtype of `int` that satisfies `p`. -/
def PIntObject (p : TypeProp) := PSubObject p intType

/- An instance of the type `ty` that satisfies `p` and subclasses `int` . -/
abbrev PSubIntObject (p : TypeProp) (ty : TypeSpec) := PIntObject (p.Subtype ty)

/- An instance of a subclass of `int`. -/
abbrev IntObject := PIntObject .Any

@[inline] def Object.isInt (self : Object) : Bool :=
  self.ty.isIntSubclass

theorem Object.isInt_iff_subset : isInt self ↔ self.ty ⊆ intType :=
  self.ty.isIntSubclass_iff_subset

@[inline] def Object.asInt (self : Object) (h : self.isInt) : IntObject :=
  self.downcast (self.ty.isIntSubclass_iff_subset.mp h)

@[inline] def Object.asInt? (self : Object) : Option IntObject :=
  if h : self.isInt then some (self.asInt h) else none

namespace PIntObject

instance : CoeOut (PIntObject p) Object := ⟨PObject.toObject⟩

theorem ty_subset_intType {self : PIntObject p} : self.ty ⊆ intType :=
  self.property.2

theorem isInt_toObject (self : PIntObject p) : self.toObject.isInt :=
  self.isInt_iff_subset.mpr self.ty_subset_intType

@[inline] def getIntRef (self : PIntObject p) : IntRef :=
  self.getData self.lawful_subobject

@[inline] def getInt (self : PIntObject p) : Int :=
  self.getIntRef.toInt

@[inline] protected def beq (self other : PIntObject p) : Bool :=
  self.getInt == other.getInt

@[inline] protected def bne (self other : PIntObject p) : Bool :=
  self.getInt != other.getInt

@[inline] protected def hash (self : PIntObject p) : Hash :=
  hash self.getInt

@[inline] def toBool (self : PIntObject p) : Bool :=
  self.getInt != 0

@[inline] def repr (self : PIntObject p) : String :=
  toString self.getInt

end PIntObject

def intTypeSlots : TypeSlots IntObject where
  hash self := return self.hash
  beq self other := return other.asInt?.any self.beq
  bne self other := return other.asInt?.all self.bne
  bool self := return self.toBool
  repr self := return self.repr

initialize intTypeSlotsRef : DTypeSlotsRef intType ←
  intTypeSlots.mkRef

@[inline] def IntObject.ofIntRef (n : IntRef) : IntObject :=
  Object.mk n.id intType intTypeSlotsRef n |>.toSubObject

instance : OfNat IntObject 0 := ⟨.ofIntRef 0⟩
instance : Coe IntRef IntObject := ⟨.ofIntRef⟩

theorem IntObject.zero_eq : (0 : IntObject) = .ofIntRef 0 := rfl

@[inline] def mkIntObject (n : Int) : BaseIO IntObject := do
  IntObject.ofIntRef <$> mkIntRef n

instance : OfNat Object 0 := ⟨(0 : IntObject)⟩

/-! ## `bool` Objects -/

@[simp] theorem boolType_subset_intType : boolType ⊆ intType := by
  simp [boolType, TypeSpec.subset_iff_mem_mro, TypeSpec.mro]

/-- An instance of a subclass of `bool` that satisfies `p`. -/
def PBoolObject (p : TypeProp) := PSubIntObject p boolType

/-- An instance of a subclass of `bool`. There are only two, `True` and `False`. -/
abbrev BoolObject := PBoolObject .Any

@[inline] def BoolObject.ofSubObject (self : SubObject boolType) : BoolObject :=
  self.upcast boolType_subset_intType

instance : Coe (SubObject boolType) BoolObject := ⟨.ofSubObject⟩

/--
Returns whether this object is the `True` singleton.

This is equivalent to the Python `self is True`.
-/
@[inline] def Object.isTrue (self : Object) : Bool :=
  self.id == .true

/--
Returns whether this object is the `False` singleton.

This is equivalent to the Python `self is False`.
-/
@[inline] def Object.isFalse (self : Object) : Bool :=
  self.id == .false

/--
Returns whether this object is the `True` or `False` singleton.

This is equivalent to the Python `self is True or self is False`.
-/
@[inline] def Object.isBool (self : Object) : Bool :=
  self.isFalse || self.isTrue

theorem Object.ty_eq_of_isBool : isBool self → self.ty = boolType := by
  simp only [isBool, isTrue, isFalse, Bool.or_eq_true, beq_iff_eq]
  intro h
  exact self.lawful_bool h

theorem Object.isBool_iff_subset : isBool self ↔ self.ty ⊆ boolType := by
  apply Iff.intro
  · intro h
    simp [ty_eq_of_isBool h]
  · simp only [isBool, isTrue, isFalse, Bool.or_eq_true, beq_iff_eq]
    exact fun h => self.lawful_subobject h |>.1

/-- Casts `self` to `BoolObject`. -/
@[inline] def Object.asBool (self : Object) (h : self.isBool) : BoolObject :=
  self.downcast (self.isBool_iff_subset.mp h)

/--
Casts `self` to `BoolObject` if `self` is either the `True` or `False` singleton.
Otherwise, returns `none`.
-/
@[inline] def Object.asBool? (self : Object) : Option BoolObject :=
  if h : self.isBool then some (self.asBool h) else none

namespace BoolObject

instance : Coe BoolObject Object := ⟨PObject.toObject⟩

def getBool (self : BoolObject) : Bool :=
  self.getInt != 0

def repr (self : BoolObject) : String :=
  if self.getBool then "True" else "False"

end BoolObject

def boolTypeSlots : TypeSlots BoolObject := {
  intTypeSlots.downcast boolType_subset_intType with
  str self := return self.repr
  repr self := return self.repr
}

initialize boolTypeSlotsRef : DTypeSlotsRef boolType ←
  boolTypeSlots.stripCast boolType_subset_intType |>.mkRef

namespace BoolObject

protected def false : BoolObject := .ofSubObject <|
  Object.mk .false boolType boolTypeSlotsRef (0 : IntRef) |>.toSubObject

instance : CoeDep Bool false BoolObject := ⟨BoolObject.false⟩

protected def true : BoolObject := .ofSubObject <|
  Object.mk .true boolType boolTypeSlotsRef (1 : IntRef) |>.toSubObject

instance : CoeDep Bool true BoolObject := ⟨BoolObject.true⟩

def ofBool (b : Bool) : BoolObject :=
  if b then true else false

instance : Coe Bool BoolObject := ⟨ofBool⟩

end BoolObject

namespace Object

@[simp] theorem id_true : (true : Object).id = .true := rfl
@[simp] theorem ty_true : (true : Object).ty = boolType := rfl
@[simp] theorem data_true : (true : Object).data = .mk (1 : IntRef) := rfl

theorem isTrue_iff_eq_true : isTrue self ↔ self = true := by
  simp only [isTrue, id_true, eq_iff, beq_iff_eq, iff_self_and]
  intro id_eq
  have ty_eq := self.lawful_bool (.inr id_eq)
  have data_eq := (ty_eq ▸ self.lawful_object).2.2.1 id_eq
  simp [ty_eq, data_eq]

@[simp] theorem id_false : (false : Object).id = .false := rfl
@[simp] theorem ty_false : (false : Object).ty = boolType := rfl
@[simp] theorem data_false : (false : Object).data = .mk (0 : IntRef) := rfl

theorem isFalse_iff_eq_false : isFalse self ↔ self = false := by
  simp only [isFalse, id_false, eq_iff, beq_iff_eq, iff_self_and]
  intro id_eq
  have ty_eq := self.lawful_bool (.inl id_eq)
  have data_eq := (ty_eq ▸ self.lawful_object).2.1 id_eq
  simp [ty_eq, data_eq]

end Object
