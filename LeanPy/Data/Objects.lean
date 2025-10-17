/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import LeanPy.Data.Object.Slots
import LeanPy.Data.VoidRef
import LeanPy.Util.String

namespace LeanPy

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

def objectTypeRef.slots : TObjectSlots ObjectObject where
  hash self := return self.hash
  beq self other := return self.beq other
  bne self other := return self.bne other
  bool _ := return true
  repr self := return self.repr

@[instance] initialize objectTypeSlotsRef : TypeSlots objectTypeRef ←
  objectTypeRef.slots.mkRef

def ObjectObject.ofVoidRef (ref : VoidRef) : ObjectObject :=
  objectTypeRef.mkObject ref.id  ref

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
  ⟨self.getData (self.lawful_subobject : typeType.IsValidObject _ _).2⟩

@[inline] def getType (self : TypeObject) : PyType :=
  self.getTypeRef.data

def name (self : TypeObject) : String :=
  self.getType.name

def repr (self : TypeObject) : String :=
  s!"<class '{self.name}'>"

end TypeObject

def typeTypeRef.slots : TObjectSlots TypeObject where
  hash self := return self.asObject.hash
  beq self other := return self.asObject.beq other
  bne self other := return self.asObject.bne other
  bool _ := return true
  repr self := return self.repr

@[instance] initialize typeTypeSlotsRef : TypeSlots typeTypeRef ←
  typeTypeRef.slots.mkRef

namespace TypeObject

def ofInitTypeRef (ref : InitTypeRef ty) : TypeObject :=
  typeTypeRef.mkObject ref.id  ref.toTypeRef.toRawTypeRef

instance : CoeOut (InitTypeRef ty) TypeObject := ⟨ofInitTypeRef⟩

def ofTypeRef (ty : TypeRef) [LawfulTypeRef ty] : TypeObject :=
  typeTypeRef.mkObject ty.id  ty.toRawTypeRef

instance [LawfulTypeRef ty] : CoeDep TypeRef ty TypeObject := ⟨ofTypeRef ty⟩
instance [LawfulTypeRef ty] : CoeDep TypeRef ty Object := ⟨ofTypeRef ty⟩

end TypeObject

def mkTypeObject (ty : PyType) : BaseIO TypeObject := do
  -- TODO: figure out how to require lawfulness
  .ofInitTypeRef <$> mkInitTypeRef (ty := ty)

/-! ## None -/

/- An instance of type `none`. There is only one, `None`. -/
def NoneObject := SubObject noneTypeRef

namespace NoneObject

instance : Coe NoneObject Object := ⟨PObject.toObject⟩

-- @[simp] theorem id_eq : (self : NoneObject).id = .none :=
--   self.lawful_subobject.1

-- @[simp] theorem isNone_eq_true : (self : NoneObject).isNone := by
--   simp [Object.isNone]

-- @[simp] theorem ty_eq : (self : NoneObject).ty = noneTypeRef :=
--   self.lawful_none id_eq

-- @[simp] theorem data_eq : (self : NoneObject).data = .mk () :=
--   self.lawful_subobject.2

protected def hash : Hash :=
  hash ObjectId.none

protected def repr : String :=
  "None"

end NoneObject

def noneTypeRef.slots : TObjectSlots NoneObject where
  hash _ := return NoneObject.hash
  beq _ other := return other.isNone
  bne _ other := return other.isNotNone
  bool _ := return false
  repr _ := return NoneObject.repr

@[instance] initialize noneTypeSlotsRef : TypeSlots noneTypeRef ←
  noneTypeRef.slots.mkRef

namespace Object

protected def none : NoneObject :=
  noneTypeRef.mkObject .none ()

instance : CoeDep (Option α) none Object := ⟨Object.none⟩

instance : Inhabited Object := ⟨none⟩

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

namespace NoneObject

instance : CoeDep (Option α) none NoneObject := ⟨Object.none⟩

@[simp] theorem eq_none : (self : NoneObject) = none := by
  suffices h : self.isNone by
    simp [← self.toObject_inj, self.isNone_iff_eq_none.mp h]
  simp [Object.isNone, self.lawful_subobject.1]

end NoneObject

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

def strTypeRef.slots : TObjectSlots StrObject where
  hash self := return self.hash
  beq self other := return other.asStr?.any self.beq
  bne self other := return other.asStr?.all self.bne
  bool self := return self.toBool
  str self := return self.toString
  repr self := return self.repr

@[instance] initialize strTypeSlotsRef : TypeSlots strTypeRef ←
  strTypeRef.slots.mkRef

@[inline] def StrObject.ofStringRef (r : StringRef) : StrObject :=
  strTypeRef.mkObject r.id  r

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

@[inline] nonrec def asInt (self : PIntObject p) : IntObject :=
  self.asInt self.isInt_toObject

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

def intTypeRef.slots : TObjectSlots IntObject where
  hash self := return self.hash
  beq self other := return other.asInt?.any self.beq
  bne self other := return other.asInt?.all self.bne
  bool self := return self.toBool
  repr self := return self.repr

@[instance] initialize intTypeSlotsRef : TypeSlots intTypeRef ←
  intTypeRef.slots.mkRef

@[inline] def IntObject.ofIntRef (n : IntRef) : IntObject :=
  intTypeRef.mkObject n.id  n

instance : OfNat IntObject 0 := ⟨.ofIntRef 0⟩
instance : Coe IntRef IntObject := ⟨.ofIntRef⟩

theorem IntObject.zero_eq : (0 : IntObject) = .ofIntRef 0 := rfl

@[inline] def mkIntObject (n : Int) : BaseIO IntObject := do
  IntObject.ofIntRef <$> mkIntRef n

instance : OfNat Object 0 := ⟨(0 : IntObject)⟩

/-! ## `bool` Objects -/

@[simp] theorem boolTypeRef_subset_intTypeRef : boolTypeRef ⊆ intTypeRef := by
  simp [TypeRef.Subtype.iff_eq_or_mem_baseMro]

/-- An instance of a subclass of `bool` that satisfies `p`. -/
def PBoolObject (p : TypeProp) := PSubIntObject p boolTypeRef

/-- An instance of a subclass of `bool`. There are only two, `True` and `False`. -/
abbrev BoolObject := PBoolObject .Any

@[inline] def BoolObject.ofSubObject (self : SubObject boolTypeRef) : BoolObject :=
  self.upcast boolTypeRef_subset_intTypeRef

instance : Coe (SubObject boolTypeRef) BoolObject := ⟨.ofSubObject⟩

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

@[inline] def getBool (self : BoolObject) : Bool :=
  self.getInt != 0

def repr (self : BoolObject) : String :=
  if self.getBool then "True" else "False"

end BoolObject

def boolTypeRef.slots : TObjectSlots BoolObject := {
  intTypeRef.slots.downcast boolTypeRef_subset_intTypeRef with
  str self := return self.repr
  repr self := return self.repr
}

@[instance] initialize boolTypeSlotsRef : TypeSlots boolTypeRef ←
  boolTypeRef.slots.stripCast boolTypeRef_subset_intTypeRef |>.mkRef

namespace BoolObject

protected def false : BoolObject :=
  boolTypeRef.mkObject .false (0 : IntRef)

instance : CoeDep Bool false BoolObject := ⟨BoolObject.false⟩

protected def true : BoolObject :=
  boolTypeRef.mkObject .true (1 : IntRef)

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
