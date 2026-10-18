import Lake
open Lake DSL

package «OSforGFF» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

-- Local branch only: point at the sibling ports (branch pin-v4.34.1) of the two upstream deps;
-- BochnerMinlos in turn requires `../kolmogorov_extension4` by path.
require BochnerMinlos from "../bochner"

require GaussianField from "../gaussian-field"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.34.1"

@[default_target]
lean_lib «OSforGFF» where
  -- add any library configuration options here
