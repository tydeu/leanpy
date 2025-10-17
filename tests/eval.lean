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

/-- info: 0 -/
#guard_msgs in #eval_py 0

/-- info: 255 -/
#guard_msgs in #eval_py 0xFF

/-- info: 4294967296 -/
-- smallest platform-independent big int
#guard_msgs in #eval_py 4294967296

/-- info: 'helloworld' -/
#guard_msgs in #eval_py "hello" "world"

/-! ## Types -/

/-- info: <class 'object'> -/
#guard_msgs in #eval_py object

/-- info: <class 'type'> -/
#guard_msgs in #eval_py type

/-- info: <class 'str'> -/
#guard_msgs in #eval_py str

/-- info: <class 'int'> -/
#guard_msgs in #eval_py int

/-- info: <class 'bool'> -/
#guard_msgs in #eval_py bool

/-! ## Comparisons -/

/-- info: False -/
#guard_msgs in #eval_py None is False

/-- info: True -/
#guard_msgs in #eval_py False is not True

/-- info: False -/
#guard_msgs in #eval_py False is not False

/-- info: True -/
#guard_msgs in #eval_py None is None

/-- info: False -/
#guard_msgs in #eval_py None == 0

/-- info: True -/
#guard_msgs in #eval_py None != 0

/-- info: False -/
#guard_msgs in #eval_py 0 == None

/-- info: True -/
#guard_msgs in #eval_py 0 == False

/-- info: False -/
#guard_msgs in #eval_py 42 != 42

/-- info: True -/
#guard_msgs in #eval_py "abc" == "abc"

/-- info: False -/
#guard_msgs in #eval_py "abc" != "abc"

/-- info: True -/
#guard_msgs in #eval_py "abc" != "def"

/-- info: True -/
#guard_msgs in #eval_py type == type

/-- info: False -/
#guard_msgs in #eval_py type != type

/-- info: True -/
#guard_msgs in #eval_py int != type

/-! ## Conditionals -/

/-- info: False -/
#guard_msgs in #eval_py True if None else False

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
