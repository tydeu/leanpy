import Lake
open Lake DSL

package «leanpy»

lean_lib «Leanpy»

@[default_target]
lean_exe «leanpy» where
  root := `Main
