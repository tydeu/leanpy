import LeanPy

open LeanPy

/-- info: false -/
#guard_msgs in #eval return (← mkObject).beq (← mkObject)
