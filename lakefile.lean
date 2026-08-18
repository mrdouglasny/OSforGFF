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
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.33.0-rc1"

@[default_target]
lean_lib «OSforGFF» where
  -- add any library configuration options here

/-! Demonstration of the "characterise, don't construct" pattern for the Palomar registry
    Challenge (see docs/palomar_proposal.md §6). Not default targets: build explicitly with
    `lake build ChallengeSlim SolutionSlim`. -/

/-- OS2 restated as a characterisation, Mathlib-only. Carries the challenge hole. -/
lean_lib «ChallengeSlim» where
  srcDir := "."

/-- Proves `ChallengeSlim`'s theorem from the OSforGFF library. -/
lean_lib «SolutionSlim» where
  srcDir := "."
