import LeanPy

open LeanPy

/-! ## Basics -/

/-- error: 'return' outside function -/
#guard_msgs in #eval_py return None

/-- error: 'yield' outside function -/
#guard_msgs in #eval_py (yield None)

/-- error: 'yield' outside function -/
#guard_msgs in #eval_py yield None

#guard_msgs in #eval_py pass

#guard_msgs in #eval_py None
#guard_msgs in #eval_py (None)

/-- info: False -/
#guard_msgs in #eval_py False

/-- info: True -/
#guard_msgs in #eval_py True

#eval_py
  pass
  None

/-- info: False -/
#guard_msgs in #eval_py None is False

/-- info: True -/
#guard_msgs in #eval_py False is not True

/-- info: False -/
#guard_msgs in #eval_py False is not False

/-- info: True -/
#guard_msgs in #eval_py None is None

/-! ## Conditionals -/

/-- info: True -/
#guard_msgs in #eval_py True if True else False

/-- info: False -/
#guard_msgs in #eval_py True if False else False

#guard_msgs in
#eval_py if False: False

/-- info: True -/
#guard_msgs in
#eval_py if True: True

/-- info: True -/
#guard_msgs in
#eval_py
  if False:
    False
  else:
    True

/-- info: True -/
#guard_msgs in
#eval_py
  if False:
    False
  elif True:
    True
  else:
    False

/-! ## Variables -/

/-- error: name 'x' is not defined -/
#guard_msgs in #eval_py x

/-- info: True -/
#guard_msgs in
#eval_py
  x = True
  x

/-- info: True -/
#guard_msgs in
#eval_py
  x = False
  if True:
    x = True
  x

/-- info: True -/
#guard_msgs in
#eval_py
  x = True
  if False:
    x = False
  x

/-- info: True -/
#guard_msgs in
#eval_py
  x = False
  if x := True:
    pass
  x
