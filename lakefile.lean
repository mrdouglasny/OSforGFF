import Lake
open Lake DSL

package «OSforGFF» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require BochnerMinlos from git
  "https://github.com/mrdouglasny/bochner.git" @ "58405ecd328cf8383a1c0b53d37605fe61a0b3f6"

require GaussianField from git
  "https://github.com/mrdouglasny/gaussian-field.git" @ "ddb7102eb0515e420944b731ac66f8b4c29a9341"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.33.0-rc1"

@[default_target]
lean_lib «OSforGFF» where
  -- add any library configuration options here

/-- The registry challenge: the auditable Mathlib-only statement (root `Challenge.lean`). -/
lean_lib «Challenge» where
  srcDir := "."

/-- The registry solution: proves the challenge from OSforGFF (root `Solution.lean`). -/
lean_lib «Solution» where
  srcDir := "."
