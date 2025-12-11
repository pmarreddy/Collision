import Lake
open Lake DSL

package «Collision» where
  moreLeanArgs := #[]
  moreServerArgs := #[]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "stable"

@[default_target]
lean_lib «Collision» where
  srcDir := "lean"
