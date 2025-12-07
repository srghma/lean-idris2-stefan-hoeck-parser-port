import Lake
open Lake DSL

package «idris2-parser» where
  -- add package configuration options here

lean_lib «Idris2Parser» where
  -- add library configuration options here

@[default_target]
lean_exe «idris2-parser» where
  root := `Main

require std from git "https://github.com/leanprover/std4" @ "main"
