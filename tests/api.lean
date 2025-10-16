import LeanPy

open LeanPy

/-- info: false -/
#guard_msgs in #eval return (← mkObjectObject).beq (← mkObjectObject)

/-- info: true -/
#guard_msgs in #eval (intTypeRef : Object).asObject.beq (intTypeRef : Object)

/-- info: false -/
#guard_msgs in #eval (intTypeRef : Object).asObject.beq (boolTypeRef : Object)

/-- info: false -/
#guard_msgs in #eval (intTypeRef : Object).asObject.beq (0 : Object)
