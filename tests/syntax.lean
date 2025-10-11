import LeanPy.Grammar

syntax withPosition("#print_py" LeanPy.Grammar.block) : command

macro_rules
| `(#print_py $blk) =>
  `(#eval IO.println $(Lean.quote <| toString blk))

#print_py
  x = f(1); 4 + f(3)
  if a is None:
    kill(pid)
    return True
  else:
    return False
