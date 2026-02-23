import OSforGFF.ComplexTestFunction

/-!
# Complexification of real-valued test functions

This file provides the canonical real-linear map

`TestFunction →L[ℝ] TestFunctionℂ`

given by pointwise embedding `ℝ → ℂ` (via `Complex.ofReal`).

The underlying construction is `toComplexCLM` from `OSforGFF.ComplexTestFunction`;
we simply re-export it under a shorter name for the nuclear-space development.
-/

namespace OSforGFF

noncomputable section

/-- Pointwise embedding `f x ↦ (f x : ℂ)` as a continuous ℝ-linear map
`TestFunction →L[ℝ] TestFunctionℂ`. -/
abbrev ofRealSchwartz : TestFunction →L[ℝ] TestFunctionℂ :=
  _root_.toComplexCLM

@[simp] lemma ofRealSchwartz_apply (f : TestFunction) (x : SpaceTime) :
    ofRealSchwartz f x = (f x : ℂ) := by
  simp [ofRealSchwartz]

end

end OSforGFF

