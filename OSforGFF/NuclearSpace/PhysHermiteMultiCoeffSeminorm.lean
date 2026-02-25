/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import OSforGFF.NuclearSpace.PhysHermiteMulti
import OSforGFF.NuclearSpace.RapidDecaySeqIndex
import OSforGFF.NuclearSpace.RapidDecaySeqMultiIndex

/-!
# Coefficient seminorms for multi-index Hermite coefficients

This is the dimension-generic analogue of
`PhysHermiteSpaceTimeCoeffSeminorm.lean`, but using canonical multi-indices
`α : Fin d → ℕ` and the generic rapid-decay model
`RapidDecaySeqIndex.space (base_d d)`.
-/

open scoped BigOperators NNReal ENNReal

namespace PhysLean

noncomputable section

namespace MultiHermite

open MeasureTheory

local notation "base_d" => OSforGFF.RapidDecaySeqMultiIndex.base_d

/-- The raw coefficient sequence as a function on multi-indices. -/
def coeffSeq (d : ℕ) (ξ : ℝ) (hξ : ξ ≠ 0) (f : TestFunction d) : (Fin d → ℕ) → ℝ :=
  fun α => coeffCLM_E (d := d) ξ hξ α f

@[simp] lemma coeffSeq_apply (d : ℕ) (ξ : ℝ) (hξ : ξ ≠ 0)
    (f : TestFunction d) (α : Fin d → ℕ) :
    coeffSeq d ξ hξ f α = coeffCLM_E (d := d) ξ hξ α f := rfl

/-- The coefficient map as a linear map into the rapid-decay model.

Membership in `RapidDecaySeqIndex.space` is the substantive analytic statement and is exposed as a
hypothesis so this API remains theorem-safe and non-trivial. -/
noncomputable def coeffRapidDecayₗ (d : ℕ) (ξ : ℝ) (hξ : ξ ≠ 0)
    (hRD : ∀ f : TestFunction d,
      ∀ k : ℕ,
        Memℓp
          (OSforGFF.RapidDecaySeqIndex.weightFun (base := base_d d) k (coeffSeq d ξ hξ f))
          (2 : ℝ≥0∞)) :
    TestFunction d →ₗ[ℝ] OSforGFF.RapidDecaySeqIndex.space (base_d d) where
  toFun f := ⟨coeffSeq d ξ hξ f, hRD f⟩
  map_add' f g := by
    ext α
    simp [coeffSeq, map_add]
  map_smul' c f := by
    ext α
    simp [coeffSeq, map_smul]

@[simp] lemma coeffRapidDecayₗ_apply (d : ℕ) (ξ : ℝ) (hξ : ξ ≠ 0)
    (hRD : ∀ f : TestFunction d,
      ∀ k : ℕ,
        Memℓp
          (OSforGFF.RapidDecaySeqIndex.weightFun (base := base_d d) k (coeffSeq d ξ hξ f))
          (2 : ℝ≥0∞))
    (f : TestFunction d) (α : Fin d → ℕ) :
    ((coeffRapidDecayₗ d ξ hξ hRD f : OSforGFF.RapidDecaySeqIndex.space (base_d d)) : (Fin d → ℕ) → ℝ) α
      = coeffCLM_E (d := d) ξ hξ α f := rfl

/-- Coefficient seminorm sequence pulled back from rapid-decay seminorms. -/
noncomputable def coeffSeminormSeqOf (d : ℕ) (ξ : ℝ) (hξ : ξ ≠ 0)
    (hRD : ∀ f : TestFunction d,
      ∀ k : ℕ,
        Memℓp
          (OSforGFF.RapidDecaySeqIndex.weightFun (base := base_d d) k (coeffSeq d ξ hξ f))
          (2 : ℝ≥0∞))
    (k : ℕ) : Seminorm ℝ (TestFunction d) :=
  (OSforGFF.RapidDecaySeqIndex.Space.seminorm (base := base_d d) k).comp
    (coeffRapidDecayₗ d ξ hξ hRD)

@[simp] lemma coeffSeminormSeqOf_apply (d : ℕ) (ξ : ℝ) (hξ : ξ ≠ 0)
    (hRD : ∀ f : TestFunction d,
      ∀ k : ℕ,
        Memℓp
          (OSforGFF.RapidDecaySeqIndex.weightFun (base := base_d d) k (coeffSeq d ξ hξ f))
          (2 : ℝ≥0∞))
    (k : ℕ) (f : TestFunction d) :
    coeffSeminormSeqOf d ξ hξ hRD k f =
      OSforGFF.RapidDecaySeqIndex.Space.seminorm (base := base_d d) k
        (coeffRapidDecayₗ d ξ hξ hRD f) := rfl

@[simp] lemma coeffSeminormSeqOf_apply_eq_norm (d : ℕ) (ξ : ℝ) (hξ : ξ ≠ 0)
    (hRD : ∀ f : TestFunction d,
      ∀ k : ℕ,
        Memℓp
          (OSforGFF.RapidDecaySeqIndex.weightFun (base := base_d d) k (coeffSeq d ξ hξ f))
          (2 : ℝ≥0∞))
    (k : ℕ) (f : TestFunction d) :
    coeffSeminormSeqOf d ξ hξ hRD k f =
      ‖OSforGFF.RapidDecaySeqIndex.Space.toL2ₗ (base := base_d d) k
        (coeffRapidDecayₗ d ξ hξ hRD f)‖ := rfl

/-- Monotonicity of the pulled-back coefficient seminorm sequence. -/
theorem coeffSeminormSeqOf_mono (d : ℕ) (ξ : ℝ) (hξ : ξ ≠ 0)
    (hRD : ∀ f : TestFunction d,
      ∀ k : ℕ,
        Memℓp
          (OSforGFF.RapidDecaySeqIndex.weightFun (base := base_d d) k (coeffSeq d ξ hξ f))
          (2 : ℝ≥0∞)) :
    Monotone (coeffSeminormSeqOf d ξ hξ hRD) := by
  intro a b hab f
  have hmono :
      Monotone (fun k : ℕ =>
        OSforGFF.RapidDecaySeqIndex.Space.seminorm (base := base_d d) k) :=
    OSforGFF.RapidDecaySeqIndex.Space.seminorm_mono
      (base := base_d d) (OSforGFF.RapidDecaySeqMultiIndex.one_le_base_d d)
  simpa [coeffSeminormSeqOf] using hmono hab (coeffRapidDecayₗ d ξ hξ hRD f)

end MultiHermite

end

end PhysLean

