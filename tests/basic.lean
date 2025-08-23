import Py

syntax (name := pyCmd) withPosition("#py" Py.Grammar.block) : command
macro_rules
| `(pyCmd|#py $blk) => `(#eval IO.println $(Lean.quote <| toString blk))

#py
  x = f(1); 4 + f(3)
  if a is None:
    kill(pid)
    return True
  else:
    return False
