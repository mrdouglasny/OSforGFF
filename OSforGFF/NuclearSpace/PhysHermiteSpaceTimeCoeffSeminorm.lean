/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import OSforGFF.NuclearSpace.PhysHermiteSpaceTimeCoeffRapidDecay

/-!
# Coefficient seminorm sequence on `TestFunction` (via spacetime Hermite coefficients)

We pull back the standard weighted `ℓ²` seminorms from the rapid-decay sequence model
`RapidDecaySeqBase.space base₄` along the normalized Hermite coefficient map.

This gives a canonical candidate seminorm sequence on `TestFunction` tailored to nuclearity
proofs (Hilbertian/diagonal on coefficients).
-/

open scoped BigOperators NNReal ENNReal

namespace PhysLean

noncomputable section

namespace SpaceTimeHermite

local notation "base₄" => OSforGFF.RapidDecaySeqMulti.base₄

/-! ## The pulled-back seminorm sequence -/

/-- The coefficient seminorm sequence on `TestFunction`, defined by pulling back the
weighted `ℓ²` seminorms on `RapidDecaySeqBase.space base₄` along
`normalizedCoeffRapidDecayₗ ξ hξ`. -/
noncomputable def coeffSeminormSeq (ξ : ℝ) (hξ : ξ ≠ 0) (k : ℕ) : Seminorm ℝ TestFunction :=
  (OSforGFF.RapidDecaySeqBase.Space.seminorm (base := base₄) k).comp (normalizedCoeffRapidDecayₗ ξ hξ)

@[simp]
lemma coeffSeminormSeq_apply (ξ : ℝ) (hξ : ξ ≠ 0) (k : ℕ) (f : TestFunction) :
    coeffSeminormSeq ξ hξ k f =
      OSforGFF.RapidDecaySeqBase.Space.seminorm (base := base₄) k (normalizedCoeffRapidDecay ξ hξ f) := by
  rfl

@[simp]
lemma coeffSeminormSeq_apply_eq_norm (ξ : ℝ) (hξ : ξ ≠ 0) (k : ℕ) (f : TestFunction) :
    coeffSeminormSeq ξ hξ k f =
      ‖OSforGFF.RapidDecaySeqBase.Space.toL2ₗ (base := base₄) k (normalizedCoeffRapidDecay ξ hξ f)‖ := by
  rfl

@[simp]
lemma coeffSeminormSeq_toL2_apply (ξ : ℝ) (hξ : ξ ≠ 0) (k : ℕ) (f : TestFunction) (n : ℕ) :
    (OSforGFF.RapidDecaySeqBase.Space.toL2ₗ (base := base₄) k (normalizedCoeffRapidDecay ξ hξ f) : ℕ → ℝ) n =
      (base₄ n) ^ k * normalizedCoeffCLM_SpaceTime ξ hξ n f := by
  simp [OSforGFF.RapidDecaySeqBase.Space.toL2ₗ_apply, normalizedCoeffRapidDecay_apply,
    OSforGFF.RapidDecaySeqBase.weight, mul_assoc]

/-! ## Monotonicity -/

theorem coeffSeminormSeq_mono (ξ : ℝ) (hξ : ξ ≠ 0) :
    Monotone (coeffSeminormSeq ξ hξ) := by
  intro a b hab f
  have hmono :
      Monotone (fun k : ℕ => OSforGFF.RapidDecaySeqBase.Space.seminorm (base := base₄) k) :=
    OSforGFF.RapidDecaySeqBase.Space.seminorm_mono (base := base₄) OSforGFF.RapidDecaySeqMulti.one_le_base₄
  simpa [coeffSeminormSeq] using hmono hab (normalizedCoeffRapidDecayₗ ξ hξ f)

end SpaceTimeHermite

end

end PhysLean
