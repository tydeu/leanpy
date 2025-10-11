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
import LeanPy.Util.String

namespace LeanPy

/-! ## Object Data -/

/-- The name of an object's Lean data type. -/
abbrev DataKind := Lean.Name

private opaque ObjectData.nonemptyType (ty : DataKind) : NonemptyType.{0}

/-- Per-type data. -/
def ObjectData (ty : DataKind) : Type := (ObjectData.nonemptyType ty).type

instance ObjectData.instNonempty : Nonempty (ObjectData ty) :=
  (ObjectData.nonemptyType ty).property

open TypeName

set_option linter.unusedVariables.funArgs false in
@[inline] def ObjectData.mk' [TypeName α] (a : α) (h : typeName α = n) : ObjectData n :=
  unsafe unsafeCast a

@[inline] def ObjectData.mk [TypeName α] (a : α) : ObjectData (typeName α) :=
  mk' a rfl

@[inline] unsafe def ObjectData.getImpl [Nonempty α] [TypeName α] (self : ObjectData n) (_ : typeName α = n) : α :=
  unsafeCast self

@[implemented_by getImpl]
opaque ObjectData.get' [Nonempty α] [TypeName α] (self : ObjectData n) (h : typeName α = n) : α

@[inline] def ObjectData.get [Nonempty α] [TypeName α] (self : ObjectData (typeName α)) : α :=
  self.get' rfl

/-! ## Slots -/

private opaque Slot.nonemptyType (ty : DataKind) (name : Lean.Name) : NonemptyType.{0}

/-- Per-type data. -/
def Slot (ty : DataKind) (name : Lean.Name) : Type :=
  (Slot.nonemptyType ty name).type

instance Slot.instNonempty : Nonempty (Slot ty name) :=
  (Slot.nonemptyType ty name).property

/-- The type of built-in slots for `__bool__`. -/
abbrev BoolSlot (ty : DataKind) := Slot ty decl_name%

/-- The type of built-in slots for `__repr__` and `__str__`. -/
abbrev ReprSlot (ty : DataKind) := Slot ty decl_name%

/-! ## Object Type -/

structure TypeSlotsRef (leanTy : DataKind) where
  private mk ::
    private val : NonScalar
  deriving Nonempty

structure DTypeSlotsRef (α : Type u) [TypeName α] extends TypeSlotsRef (typeName α)

instance [TypeName α] : Nonempty (DTypeSlotsRef α ) :=
  ⟨⟨Classical.ofNonempty⟩⟩

instance [TypeName α] : CoeOut (DTypeSlotsRef α) (TypeSlotsRef (typeName α)) :=
  ⟨DTypeSlotsRef.toTypeSlotsRef⟩

/-- An (initialized) Python type object. -/
-- TODO: Enrich with proper fields
structure TypeObject (leanTy : DataKind) where
  /-- The type's name -/
  name : String
  /-- The type's documentation string or `none` if undefined. -/
  doc? : Option String := none
  /-- The type's slots. Used to optimize magic methods. -/
  slots : TypeSlotsRef leanTy
  deriving Nonempty

/-- A Python type object with a known Lean representation. -/
structure DTypeObject (α : Type u) [TypeName α] extends TypeObject (typeName α)

instance [TypeName α] : CoeOut (DTypeObject α) (TypeObject (typeName α)) :=
  ⟨DTypeObject.toTypeObject⟩

/-- A Python object. -/
structure Object where
  mk' ::
    /-- The type name of the object's Lean data. -/
    leanTy : DataKind
    /-- The object's Python type. -/
    ty : TypeObject leanTy
    /-- The object's Lean data. -/
    dynamicData : ObjectData leanTy
    /--
    The object's id.
    See `ObjectId` for details on how LeanPy encodes object identities.
    -/
    id : ObjectId
    deriving Nonempty

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

structure KObject (d : DataKind) extends Object where
  toObject_leanTy_eq : toObject.leanTy = d

abbrev DObject (α : Type u) [TypeName α] := KObject (typeName α)

namespace DObject

instance [TypeName α] : CoeOut (DObject α) Object :=
  ⟨KObject.toObject⟩

def data [Nonempty α] [TypeName α] (self : DObject α) : α :=
  self.dynamicData.get' self.toObject_leanTy_eq.symm

end DObject

namespace Object

def mk
  [TypeName α] (ty : DTypeObject α) (data : α) (id : ObjectId)
: Object := ⟨typeName α, ty, ObjectData.mk' data rfl, id⟩

protected def Object.toString (self : Object) : String :=
  s!"<{self.ty.name} object at 0x{self.id.hex}>"

instance : ToString Object := ⟨Object.toString⟩

end Object

/-! ## Slots -/

/-- Untyped object slots. -/
structure BaseTypeSlots (α : Type u) where
  /-- The type's `__hash__` slot.  -/
  hash (self : α) : PyM Hash
  /-- The type's `==` slot. Unlike `__eq__`, this returns `Bool`.  -/
  eqOp (self : α) (other : Object) : PyM Bool
  /-- The type's `!=` slot. Unlike `__ne__`, this returns `Bool`. -/
  neOp (self : α) (other : Object) : PyM Bool := Bool.not <$> eqOp self other
  /-- The type's `__bool__` slot.  -/
  bool (self : α) : PyM Bool
  /-- The type's `__repr__` slot.  -/
  repr (self : α) : PyM String
  /-- The type's `__str__` slot.  -/
  str (self : α) : PyM String := repr self
  deriving Nonempty

/-- Untyped object slots. -/
abbrev TypeSlots := BaseTypeSlots Object

@[inline] private unsafe def mkTypeSlotsRefImpl
  (slots : TypeSlots) :  BaseIO (TypeSlotsRef leanTy)
:= pure (unsafeCast slots)

@[implemented_by mkTypeSlotsRefImpl]
opaque mkTypeSlotsRef
  (slots : TypeSlots) : BaseIO (TypeSlotsRef leanTy)

/-- Typed object slots. -/
abbrev DTypeSlots (α : Type u) [TypeName α] := BaseTypeSlots (DObject α)

@[inline] private unsafe def mkDTypeSlotsRefImpl
  [TypeName α] (slots : DTypeSlots α) :  BaseIO (DTypeSlotsRef α)
:= pure (unsafeCast slots)

@[implemented_by mkDTypeSlotsRefImpl]
opaque mkDTypeSlotsRef
  [TypeName α] (slots : DTypeSlots α) : BaseIO (DTypeSlotsRef α)

/-- Typed object slots. -/
abbrev KTypeSlots (leanTy : DataKind) := BaseTypeSlots (KObject leanTy)

@[inline] private unsafe def TypeSlotsRef.getImpl
  (self : TypeSlotsRef leanTy) : BaseIO (KTypeSlots leanTy)
:= pure (unsafeCast self)

@[implemented_by getImpl]
opaque TypeSlotsRef.get
  (self : TypeSlotsRef leanTy) : BaseIO (KTypeSlots leanTy)

@[inline] def Object.slots (self : Object) : TypeSlotsRef self.leanTy :=
  self.ty.slots

@[inline] def Object.hashM (self : Object) : PyM Hash := do
  (← self.slots.get).hash ⟨self, rfl⟩

@[inline] def Object.eqOpM (self other : Object) : PyM Bool := do
  (← self.slots.get).eqOp ⟨self, rfl⟩ other

@[inline] def Object.neOpM (self other : Object) : PyM Bool := do
  (← self.slots.get).neOp ⟨self, rfl⟩ other

@[inline] def Object.reprM (self : Object) : PyM String := do
  (← self.slots.get).repr ⟨self, rfl⟩

@[inline] def Object.toStringM (self : Object) : PyM String := do
  (← self.slots.get).str ⟨self, rfl⟩

@[inline] def Object.toBoolM (self : Object) : PyM Bool := do
  (← self.slots.get).bool ⟨self, rfl⟩

/-! ## None -/

deriving instance TypeName for Unit

def noneHash : Hash :=
  hash ObjectId.none

def noneTypeSlots : DTypeSlots Unit where
  hash _ := return noneHash
  eqOp _ other := return other.id == .none
  neOp _ other := return other.id != .none
  bool _ := return false
  repr _ := return "None"

initialize noneTypeSlotsRef : DTypeSlotsRef Unit ←
  mkDTypeSlotsRef noneTypeSlots

def noneType : DTypeObject Unit where
  name := "NoneType"
  slots := noneTypeSlotsRef

protected def Object.none : Object :=
  .mk noneType () .none

instance : CoeDep (Option α) none Object := ⟨.none⟩

@[inline] def Object.isNone (self : Object) : Bool :=
  self.id == .none

@[simp] theorem Object.isNone_none : isNone none := rfl

/-! ## `str` Objects -/

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

@[inline] def Object.getString? (self : Object) : Option String :=
  if h : typeName StringRef = self.leanTy then -- TODO: Proper type-check
    some (self.dynamicData.get' h).data
  else
    none

def strTypeSlots : DTypeSlots StringRef where
  hash self := return hash self.data.data -- TODO: salt hash?
  eqOp self other := return other.getString?.any (self.data.data == ·)
  neOp self other := return other.getString?.all (self.data.data != ·)
  bool self := return self.data.data.length != 0
  str self := return self.data.data
  repr self := return strRepr self.data.data

initialize strTypeSlotsRef : DTypeSlotsRef StringRef ←
  mkDTypeSlotsRef strTypeSlots

def strType : DTypeObject StringRef where
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
    errors defaults to 'strict'.
  "
  slots := strTypeSlotsRef

@[inline] def Object.ofStringRef (r : StringRef) : Object :=
  .mk strType r r.id

@[inline] def mkStringObject (s : String) : BaseIO Object := do
  Object.ofStringRef <$> mkStringRef s

/-! ## `int` Objects -/

@[inline] def Object.getInt? (self : Object) : Option Int :=
  if h : typeName IntRef = self.leanTy then -- TODO: Proper type-check
    some (self.dynamicData.get' h).toInt
  else
    none

def intTypeSlots : DTypeSlots IntRef where
  hash self := return hash self.data.toInt
  eqOp self other := return other.getInt?.any (self.data.toInt == ·)
  neOp self other := return other.getInt?.all (self.data.toInt != ·)
  bool b := return b.data.toInt != 0
  repr b := return toString b.data.toInt

initialize intTypeSlotsRef : DTypeSlotsRef IntRef ←
  mkDTypeSlotsRef intTypeSlots

def intType : DTypeObject IntRef where
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
  slots := intTypeSlotsRef

@[inline] def Object.ofIntRef (n : IntRef) : Object :=
  .mk intType n n.id

instance : OfNat Object 0 := ⟨.ofIntRef 0⟩
instance : Coe IntRef Object := ⟨.ofIntRef⟩

theorem Object.zero_eq : (0 : Object) = .ofIntRef 0 := rfl

@[inline] def mkIntObject (n : Int) : BaseIO Object := do
  Object.ofIntRef <$> mkIntRef n

/-! ## `bool` Objects -/

def boolTypeSlots : DTypeSlots IntRef := {
  intTypeSlots with
  repr, str := repr
}
where
  repr b := return if b.data.toInt != 0 then "True" else "False"

initialize boolTypeSlotsRef : DTypeSlotsRef IntRef ←
  mkDTypeSlotsRef boolTypeSlots

def boolType : DTypeObject IntRef where
  name := "bool"
  doc? := some "\
    bool(x) -> bool\n\
    \n\
    Returns True when the argument x is true, False otherwise.\n\
    The builtins True and False are the only two instances of the class bool.\n\
    The class bool is a subclass of the class int, and cannot be subclassed.\
  "
  slots := boolTypeSlotsRef

protected def Object.false : Object :=
  .mk boolType 0 .false

instance : CoeDep Bool false Object := ⟨Object.false⟩

protected def Object.true : Object :=
  .mk boolType 1 .true

instance : CoeDep Bool true Object := ⟨Object.true⟩

def Object.ofBool (b : Bool) : Object :=
  if b then true else false

instance : Coe Bool Object := ⟨Object.ofBool⟩
