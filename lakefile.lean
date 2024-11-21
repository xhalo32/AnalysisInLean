import Lake
open Lake DSL

package "DifferentialCalculus" where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`linter.unusedTactic, false⟩
  ]
  -- add any additional package configuration options here

require "leanprover-community" / "mathlib"

@[default_target]
lean_lib «DifferentialCalculus» where
  -- add any library configuration options here
