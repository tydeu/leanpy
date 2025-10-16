/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Std.Data.HashMap
import LeanPy.Data.Object.ObjectTypes2
import LeanPy.Data.HashDict
import LeanPy.Data.AttrName
import LeanPy.Data.VoidRef
import LeanPy.Util.String

namespace LeanPy

/-! ## LawfulType -/

class LawfulType (self : TypeRef) : Prop where
  isNonScalar_addr : self.addr % 2 = 0 := by simp
  subset_objectType : self ⊆ objectTypeRef := by
    simp [TypeRef.subset_iff_mem_mro, TypeRef.mro_def, FrozenRef.eq_iff]
  isTypeSubclass_iff_subset :
    self.isTypeSubclass ↔ self ⊆ typeTypeRef := by
      simp [TypeRef.subset_iff_mem_mro, TypeRef.mro_def, FrozenRef.eq_iff]
  isIntSubclass_iff_subset :
    self.isIntSubclass ↔ self ⊆ intTypeRef := by
      simp [TypeRef.subset_iff_mem_mro, TypeRef.mro_def, FrozenRef.eq_iff]
  isStrSubclass_iff_subset :
    self.isStrSubclass ↔ self ⊆ strTypeRef := by
      simp [TypeRef.subset_iff_mem_mro, TypeRef.mro_def, FrozenRef.eq_iff]
  isValidObject_mro : ∀ {id data},
    self.IsValidObject id data → ∀ {ty}, self ⊆ ty → ty.IsValidObject id data
  := by simp_all [TypeRef.subset_iff_mem_mro, TypeRef.mro_def, TypeRef.mro.go]

namespace TypeRef
export LawfulType (
  subset_objectType
  isTypeSubclass_iff_subset isIntSubclass_iff_subset isStrSubclass_iff_subset
  isValidObject_mro
)
end TypeRef

@[simp] theorem data_objectTypeRef : objectTypeRef.data = objectType := rfl

@[simp] theorem mro_objectTypeRef :
  objectTypeRef.baseMro = []
:= rfl

@[simp] theorem data_typeTypeRef : typeTypeRef.data = typeType := rfl

@[simp] theorem baseMro_typeTypeRef :
  typeTypeRef.baseMro = [objectTypeRef]
:= rfl

@[simp] theorem data_noneTypeRef : noneTypeRef.data = noneType := rfl

@[simp] theorem baseMro_noneTypeRef :
  noneTypeRef.baseMro = [objectTypeRef]
:= rfl

@[simp] theorem data_strTypeRef : strTypeRef.data = strType := rfl

@[simp] theorem baseMro_strTypeRef :
  strTypeRef.baseMro = [objectTypeRef]
:= rfl

@[simp] theorem data_intTypeRef : intTypeRef.data = intType := rfl

@[simp] theorem baseMro_intTypeRef :
  intTypeRef.baseMro = [objectTypeRef]
:= rfl

@[simp] theorem data_boolTypeRef : boolTypeRef.data = boolType := rfl

@[simp] theorem baseMro_boolTypeRef :
  boolTypeRef.baseMro = [intTypeRef, objectTypeRef]
:= rfl

instance : LawfulType objectTypeRef where
instance : LawfulType typeTypeRef where
instance : LawfulType noneTypeRef where
instance : LawfulType strTypeRef where
instance : LawfulType intTypeRef where
instance : LawfulType boolTypeRef where

/-! ## TypeSlotsRef -/

/-- A reference to a `TypeSlots` structure. -/
structure TypeSlotsRef where
  private innerMk ::
    private innerTy : TypeRef
  deriving Nonempty

noncomputable def TypeSlotsRef.ty (self : TypeSlotsRef) : TypeRef :=
  self.innerTy

theorem TypeSlotsRef.ty_inj : ty a = ty b ↔ a = b := by
  cases a; cases b; simp [ty]

structure DTypeSlotsRef (ty : TypeRef) extends TypeSlotsRef where
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
  protected ty : TypeRef
  /-- The type's slots. Used to optimize magic methods. -/
  innerSlots : TypeSlotsRef
  /-- The object's Lean data. -/
  data : ObjectData

/-- A Python object. -/
structure Object extends raw : Object.Raw where mk' ::
  [lawful_ty : LawfulType ty]
  lawful_none : id = .none → ty = noneTypeRef := by simp
  lawful_bool : id = .false ∨ id = .true → ty = boolTypeRef := by simp
  lawful_slots : innerSlots.ty = ty := by simp
  lawful_object : ty.data.IsValidObject id data := by simp

instance {self : Object} : LawfulType self.ty := self.lawful_ty

/-! ## TypeProp -/

/--
A predicate about a type.
Used to encode Python type relations in Lean types.
-/
abbrev TypeProp := TypeRef → Prop

def TypeProp.Any : TypeProp :=
  fun _ => True

def TypeProp.Subtype (p : TypeProp) (ty : TypeRef) : TypeProp :=
  fun t => p t ∧ t ⊆ ty

theorem TypeProp.Subtype.property (h : Subtype p ty t) : p t :=
  h.1

theorem TypeProp.Subtype.ty_subset (h : Subtype p ty t) : t ⊆ ty :=
  h.2

theorem TypeProp.Subtype.trans (h : ty₁ ⊆ ty₂) (h₁ : Subtype p ty₁ t) : Subtype p ty₂ t :=
  ⟨h₁.1, .trans h₁.2 h⟩

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
abbrev PSubObject (p : TypeProp) (ty : TypeRef) :=
  PObject (p.Subtype ty)

/--
An object whose type satisfies `p` and is a subtype of `subTy`,
which is a subtype of `superTy`.
-/
abbrev PSubSubObject (p : TypeProp) (subTy superTy : TypeRef) :=
  PSubObject (p.Subtype subTy) superTy

abbrev SubObject (ty : TypeRef) := PSubObject .Any ty

@[inline] def Object.toPObject (self : Object) : PObject .Any :=
  self.cast .intro

@[inline] def Object.downcast (self : Object) (h : self.ty ⊆ ty) : SubObject ty :=
  self.cast ⟨.intro, h⟩

@[inline] def Object.toSubObject (self : Object) : SubObject self.ty :=
  self.downcast .rfl

@[inline] def PObject.upcast
  (self : PSubObject p subTy) (h : subTy ⊆ superTy)
: PSubSubObject p subTy superTy :=
  self.cast ⟨self.property, .trans self.property.2 h⟩

theorem PObject.ty_subset {self : PSubObject p ty} : self.ty ⊆ ty :=
  self.property.ty_subset

theorem Object.lawful_subobject
  {self : Object} (h : self.ty ⊆ ty) : ty.IsValidObject self.id self.data
:= self.ty.isValidObject_mro self.lawful_object h

theorem PObject.lawful_subobject
  {self : PSubObject p ty} : ty.data.IsValidObject self.id self.data
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
  (ty : TypeRef) [LawfulType ty]
  (slots : DTypeSlotsRef ty) (data : α)
  (h : ty.data.IsValidObject id (.mk data) := by simp)
  (h_none : id = .none → ty = noneTypeRef := by simp)
  (h_bool : id = .false ∨ id = .true → ty = boolTypeRef := by simp)
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
abbrev PTypeSlots (p : TypeProp) := TypeSlots (PObject p)

/-- Slots compatible with instances of `ty` or its subtypes. -/
abbrev SubTypeSlots (ty : TypeRef) := TypeSlots (SubObject ty)

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
  slots.impCast (fun hp => ⟨hp, .trans hp.ty_subset h⟩)

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
abbrev PObjectObject (p : TypeProp) := PObject (p.Subtype objectTypeRef)

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

initialize objectTypeSlotsRef : DTypeSlotsRef objectTypeRef ←
  objectTypeSlots.mkRef

def ObjectObject.ofVoidRef (ref : VoidRef) : ObjectObject :=
  Object.mk ref.id objectTypeRef objectTypeSlotsRef ref |>.toSubObject

def mkObjectObject : BaseIO ObjectObject := do
  ObjectObject.ofVoidRef <$> mkVoidRef

/-! ## `type` -/

/- An instance of a subclass of `type` that satisfies `p`. -/
abbrev PTypeObject (p : TypeProp) := PSubObject p typeTypeRef

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

@[inline] def getTypeRef (self : TypeObject) : TypeRef :=
  self.getData (self.lawful_subobject : typeType.IsValidObject _ _).2

@[inline] def getType (self : TypeObject) : PyType :=
  self.getTypeRef.data

def name (self : TypeObject) : String :=
  self.getType.name

def repr (self : TypeObject) : String :=
  s!"<class '{self.name}'>"

end TypeObject

def typeTypeSlots : TypeSlots TypeObject where
  hash self := return self.asObject.hash
  beq self other := return self.asObject.beq other
  bne self other := return self.asObject.bne other
  bool _ := return true
  repr self := return self.repr

initialize typeTypeSlotsRef : DTypeSlotsRef typeTypeRef ←
  typeTypeSlots.mkRef

def TypeObject.ofDTypeRef (ref : DTypeRef ty) : TypeObject :=
  Object.mk ref.id typeTypeRef typeTypeSlotsRef ref.toTypeRef |>.toSubObject

instance : CoeOut (DTypeRef ty) TypeObject := ⟨TypeObject.ofDTypeRef⟩

def mkTypeObject (ty : PyType) : BaseIO TypeObject := do
  .ofDTypeRef <$> mkDTypeRef ty

/-! ## None -/

/- An instance of type `none`. There is only one, `None`. -/
def NoneObject := SubObject noneTypeRef

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

def noneTypeSlots : TypeSlots NoneObject where
  hash _ := return NoneObject.hash
  beq _ other := return other.isNone
  bne _ other := return other.isNotNone
  bool _ := return false
  repr _ := return NoneObject.repr

initialize noneTypeSlotsRef : DTypeSlotsRef noneTypeRef ←
  noneTypeSlots.mkRef

namespace Object

protected def none : NoneObject :=
  Object.mk .none noneTypeRef noneTypeSlotsRef () |>.toSubObject

instance : CoeDep (Option α) none Object := ⟨Object.none⟩
instance : CoeDep (Option α) none NoneObject := ⟨Object.none⟩

@[simp] theorem isNone_none : isNone none := rfl

@[simp] theorem id_none : (none : Object).id = .none := rfl
@[simp] theorem ty_none : (none : Object).ty = noneTypeRef := rfl
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
abbrev PStrObject (p : TypeProp) := PSubObject p strTypeRef

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

initialize strTypeSlotsRef : DTypeSlotsRef strTypeRef ←
  strTypeSlots.mkRef

@[inline] def StrObject.ofStringRef (r : StringRef) : StrObject :=
  Object.mk r.id strTypeRef strTypeSlotsRef r |>.toSubObject

@[inline] def mkStrObject (s : String) : BaseIO StrObject := do
  StrObject.ofStringRef <$> mkStringRef s

/-! ## `int` Objects -/

/- An instance of a subtype of `int` that satisfies `p`. -/
def PIntObject (p : TypeProp) := PSubObject p intTypeRef

/- An instance of the type `ty` that satisfies `p` and subclasses `int` . -/
abbrev PSubIntObject (p : TypeProp) (ty : TypeRef) := PIntObject (p.Subtype ty)

/- An instance of a subclass of `int`. -/
abbrev IntObject := PIntObject .Any

@[inline] def Object.isInt (self : Object) : Bool :=
  self.ty.isIntSubclass

theorem Object.isInt_iff_subset : isInt self ↔ self.ty ⊆ intTypeRef :=
  self.ty.isIntSubclass_iff_subset

@[inline] def Object.asInt (self : Object) (h : self.isInt) : IntObject :=
  self.downcast (self.ty.isIntSubclass_iff_subset.mp h)

@[inline] def Object.asInt? (self : Object) : Option IntObject :=
  if h : self.isInt then some (self.asInt h) else none

namespace PIntObject

instance : CoeOut (PIntObject p) Object := ⟨PObject.toObject⟩

theorem ty_subset_intType {self : PIntObject p} : self.ty ⊆ intTypeRef :=
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

initialize intTypeSlotsRef : DTypeSlotsRef intTypeRef ←
  intTypeSlots.mkRef

@[inline] def IntObject.ofIntRef (n : IntRef) : IntObject :=
  Object.mk n.id intTypeRef intTypeSlotsRef n |>.toSubObject

instance : OfNat IntObject 0 := ⟨.ofIntRef 0⟩
instance : Coe IntRef IntObject := ⟨.ofIntRef⟩

theorem IntObject.zero_eq : (0 : IntObject) = .ofIntRef 0 := rfl

@[inline] def mkIntObject (n : Int) : BaseIO IntObject := do
  IntObject.ofIntRef <$> mkIntRef n

instance : OfNat Object 0 := ⟨(0 : IntObject)⟩

/-! ## `bool` Objects -/

@[simp] theorem boolTypeRef_subset_intTypeRef : boolTypeRef ⊆ intTypeRef := by
  simp [TypeRef.subset_iff_eq_or_mem_baseMro]

/-- An instance of a subclass of `bool` that satisfies `p`. -/
def PBoolObject (p : TypeProp) := PSubIntObject p boolTypeRef

/-- An instance of a subclass of `bool`. There are only two, `True` and `False`. -/
abbrev BoolObject := PBoolObject .Any

@[inline] def BoolObject.ofSubObject (self : SubObject boolTypeRef) : BoolObject :=
  self.upcast boolTypeRef_subset_intTypeRef

instance : Coe (SubObject boolTypeRef) BoolObject := ⟨.ofSubObject⟩

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

theorem Object.ty_eq_of_isBool : isBool self → self.ty = boolTypeRef := by
  simp only [isBool, isTrue, isFalse, Bool.or_eq_true, beq_iff_eq]
  intro h
  exact self.lawful_bool h

theorem Object.isBool_iff_subset : isBool self ↔ self.ty ⊆ boolTypeRef := by
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
  intTypeSlots.downcast boolTypeRef_subset_intTypeRef with
  str self := return self.repr
  repr self := return self.repr
}

initialize boolTypeSlotsRef : DTypeSlotsRef boolTypeRef ←
  boolTypeSlots.stripCast boolTypeRef_subset_intTypeRef |>.mkRef

namespace BoolObject

protected def false : BoolObject := .ofSubObject <|
  Object.mk .false boolTypeRef boolTypeSlotsRef (0 : IntRef) |>.toSubObject

instance : CoeDep Bool false BoolObject := ⟨BoolObject.false⟩

protected def true : BoolObject := .ofSubObject <|
  Object.mk .true boolTypeRef boolTypeSlotsRef (1 : IntRef) |>.toSubObject

instance : CoeDep Bool true BoolObject := ⟨BoolObject.true⟩

def ofBool (b : Bool) : BoolObject :=
  if b then true else false

instance : Coe Bool BoolObject := ⟨ofBool⟩

end BoolObject

namespace Object

@[simp] theorem id_true : (true : Object).id = .true := rfl
@[simp] theorem ty_true : (true : Object).ty = boolTypeRef := rfl
@[simp] theorem data_true : (true : Object).data = .mk (1 : IntRef) := rfl

theorem isTrue_iff_eq_true : isTrue self ↔ self = true := by
  simp only [isTrue, id_true, eq_iff, beq_iff_eq, iff_self_and]
  intro id_eq
  have ty_eq := self.lawful_bool (.inr id_eq)
  have data_eq := (ty_eq ▸ self.lawful_object).2.2.1 id_eq
  simp [ty_eq, data_eq]

@[simp] theorem id_false : (false : Object).id = .false := rfl
@[simp] theorem ty_false : (false : Object).ty = boolTypeRef := rfl
@[simp] theorem data_false : (false : Object).data = .mk (0 : IntRef) := rfl

theorem isFalse_iff_eq_false : isFalse self ↔ self = false := by
  simp only [isFalse, id_false, eq_iff, beq_iff_eq, iff_self_and]
  intro id_eq
  have ty_eq := self.lawful_bool (.inl id_eq)
  have data_eq := (ty_eq ▸ self.lawful_object).2.1 id_eq
  simp [ty_eq, data_eq]

end Object
---/
