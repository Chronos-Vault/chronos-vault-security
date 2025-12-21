import Lake
open Lake DSL

package «trinity-proofs» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.14.0"

@[default_target]
lean_lib TrinityVerification where
  srcDir := "."

lean_lib Trinity where
  srcDir := "Trinity"

lean_lib Libraries where
  srcDir := "Libraries"

lean_lib Solana where
  srcDir := "Solana"

lean_lib TON where
  srcDir := "TON"
