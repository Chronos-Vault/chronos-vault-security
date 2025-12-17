import Lake
open Lake DSL

package «trinity-proofs» where
  -- add package configuration options here

lean_lib «Trinity» where
  -- add library configuration options here

@[default_target]
lean_exe «trinity-proofs» where
  root := `Main

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
