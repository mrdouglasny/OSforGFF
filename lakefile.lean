import Lake
open Lake DSL

package «OSforGFF» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "82ff5788d387"

require BochnerMinlos from git
  "https://github.com/mrdouglasny/bochner.git" @ "4d73f08"

require GaussianField from git
  "https://github.com/mrdouglasny/gaussian-field.git" @ "4ce5d82"

@[default_target]
lean_lib «OSforGFF» where
  -- add any library configuration options here

lean_lib «DependencyExtractor» where
  -- Dependency extraction metaprogram
