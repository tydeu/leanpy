/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
syntax Authors Mac Malone
-/
import Std.Data.HashMap
import LeanPy.Data.Object.Id
import LeanPy.Data.HashDict
import LeanPy.Data.AttrName
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

/-- An (initialized) Python type object. -/
-- TODO: Enrich with proper fields
structure TypeObject (leanTy : DataKind) where
  /-- The type's name -/
  name : String
  /-- The type's documentation string or `none` if undefined. -/
  doc? : Option String := none
  /-- The type's `__bool__` slot.  -/
  bool : BoolSlot leanTy
  /-- The type's `__repr__` slot.  -/
  repr : ReprSlot leanTy
  /-- The type's `__str__` slot.  -/
  str : ReprSlot leanTy := repr
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
    rawData : ObjectData leanTy
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

/-- Mutable dictionary of variables. -/
abbrev VarDict := IO.Ref AttrDict

structure PyContext where
  globals : VarDict
  locals : VarDict := globals

/-- The monad of Python code. -/
abbrev PyM := ReaderT PyContext <| EIO ErrorObject

structure DObject (α : Type u) [TypeName α] extends Object where
  toObject_leanTy_eq_typeName : toObject.leanTy = typeName α

instance [TypeName α] : CoeOut (DObject α) Object :=
  ⟨DObject.toObject⟩

def DObject.data [Nonempty α] [TypeName α] (self : DObject α) : α :=
  self.rawData.get' self.toObject_leanTy_eq_typeName.symm

namespace Object

def mk
  [TypeName α] (ty : DTypeObject α) (data : α) (id : ObjectId)
: Object := ⟨typeName α, ty, ObjectData.mk' data rfl, id⟩

protected def Object.toString (self : Object) : String :=
  s!"<{self.ty.name} object at 0x{self.id.hex}>"

instance : ToString Object := ⟨Object.toString⟩

end Object

/-! ## Slots -/

set_option linter.unusedVariables.funArgs false in
@[inline] def BoolSlot.mk' [TypeName α] (fn : DObject α → PyM Bool) (h : typeName α = n) : BoolSlot n :=
  unsafe unsafeCast fn

@[inline] def BoolSlot.mk [TypeName α] (fn : DObject α → PyM Bool) : BoolSlot (typeName α) :=
  mk' fn rfl

set_option linter.unusedVariables.funArgs false in
@[inline] def BoolSlot.call(slot : BoolSlot n) (self : Object) (h : n = self.leanTy) : PyM Bool :=
  (unsafe unsafeCast slot : Object → PyM Bool) self

@[inline] def ReprSlot.mk [TypeName α] (fn : DObject α → PyM String) : ReprSlot (typeName α) :=
  unsafe unsafeCast fn

set_option linter.unusedVariables.funArgs false in
@[inline] def ReprSlot.call (slot : ReprSlot n) (self : Object) (h : n = self.leanTy) : PyM String :=
  (unsafe unsafeCast slot : Object → PyM String) self

def Object.repr (self : Object) : PyM String :=
  self.ty.repr.call self rfl

def Object.toStr (self : Object) : PyM String :=
  self.ty.str.call self rfl

/-! ## None -/

deriving instance TypeName for Unit

def noneType : DTypeObject Unit where
  name := "NoneType"
  bool := .mk fun _ => pure true
  repr := .mk fun _ => pure "None"

def Object.none : Object :=
  .mk noneType () .none

instance : CoeDep (Option α) none Object := ⟨.none⟩

def Object.isNone (self : Object) : Bool :=
  self.ty.name == noneType.name

/-! ## Boolean Objects -/

deriving instance TypeName for Bool, Int

def boolType : DTypeObject Bool where
  name := "bool"
  doc? := some "\
    bool(x) -> bool\n\
    \n\
    Returns True when the argument x is true, False otherwise.\n\
    The builtins True and False are the only two instances of the class bool.\n\
    The class bool is a subclass of the class int, and cannot be subclassed.\
  "
  bool := .mk fun b => return b.data
  repr := .mk fun b => return if b.data then "True" else "False"

protected def Object.false : Object :=
  .mk boolType false .false

instance : CoeDep Bool false Object := ⟨Object.false⟩

protected def Object.true : Object :=
  .mk boolType true .true

instance : CoeDep Bool true Object := ⟨Object.true⟩

def Object.ofBool (b : Bool) : Object :=
  if b then true else false

instance : Coe Bool Object := ⟨Object.ofBool⟩

def Object.toBool (self : Object) : PyM Bool :=
  self.ty.bool.call self rfl
