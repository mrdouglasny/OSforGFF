import Lake
open Lake DSL

package «OSforGFF» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require BochnerMinlos from git
  "https://github.com/mrdouglasny/bochner.git" @ "main"

require GaussianField from git
  "https://github.com/mrdouglasny/gaussian-field.git" @ "main"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «OSforGFF» where
  -- add any library configuration options here

lean_lib «DependencyExtractor» where
  -- Dependency extraction metaprogram
