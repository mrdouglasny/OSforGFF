import OSforGFF.NuclearSpace.PhysHermiteSpaceTimeSchwartzToCoeffBound

/-!
# Schwartz nuclearity via spacetime Hermite coefficients

This module discharges the remaining `OSforGFF.SchwartzNuclearInclusion` hypothesis for
`TestFunction` using the spacetime Hermite coefficient seminorms `coeffSeminormSeq ξ hξ`.

We make a canonical choice `ξ = 1` (any `ξ ≠ 0` would work) and register:

* a proof `OSforGFF.SchwartzNuclearInclusion`;
* hence an instance `[OSforGFF.NuclearSpaceStd TestFunction]` (via `OSforGFF.NuclearSpace.Schwartz`).
-/

namespace OSforGFF

noncomputable section

open scoped BigOperators

theorem schwartzNuclearInclusion : SchwartzNuclearInclusion := by
  simpa using
    (PhysLean.SpaceTimeHermite.schwartzNuclearInclusion_of_coeffSeminormSeq (ξ := (1 : ℝ))
      (hξ := by simp))

noncomputable instance : NuclearSpaceStd TestFunction := by
  exact nuclearSpaceStd_TestFunction_of_schwartzNuclearInclusion schwartzNuclearInclusion

end

end OSforGFF

