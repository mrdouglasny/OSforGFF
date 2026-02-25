/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import OSforGFF.NuclearSpace.PhysHermiteSpaceTimeCoeffNuclearity
import OSforGFF.NuclearSpace.Schwartz
import OSforGFF.NuclearSpace.PhysHermiteSpaceTimeHilbertBasis

/-!
# Bounding coefficient seminorms by Schwartz seminorms

This file starts the comparison between the coefficient seminorm sequence
`PhysLean.SpaceTimeHermite.coeffSeminormSeq ξ hξ` and the canonical Schwartz seminorm sequence
`OSforGFF.schwartzSeminormSeq`.

The key analytic ingredient for the easy direction is Bessel's inequality for the orthonormal
family of normalized spacetime Hermite eigenfunctions in `L²(SpaceTime)`.
-/

open scoped BigOperators NNReal ENNReal InnerProductSpace RealInnerProductSpace

namespace PhysLean

noncomputable section

namespace SpaceTimeHermite

open MeasureTheory

local notation "H" => ℓ²(ℕ, ℝ)

/-! ## Bessel estimate for normalized coefficients -/

lemma norm_normalizedCoeffL2_le_norm_toLp (ξ : ℝ) (hξ : ξ ≠ 0) (f : TestFunction) :
    ‖normalizedCoeffL2 ξ hξ f‖ ≤ ‖f.toLp 2 (volume : Measure SpaceTime)‖ := by
  exact le_of_eq (norm_normalizedCoeffL2_eq_norm_toLp (ξ := ξ) (hξ := hξ) (f := f))

/-! ## Relating coefficient seminorms to `L²` bounds -/

lemma coeffToL2ₗ_eq_normalizedCoeffL2_numAllPowCLM (ξ : ℝ) (hξ : ξ ≠ 0) (k : ℕ) (f : TestFunction) :
    coeffToL2ₗ (ξ := ξ) hξ k f = normalizedCoeffL2 ξ hξ (numAllPowCLM ξ k f) := by
  ext n
  simp only [coeffToL2ₗ_apply, normalizedCoeffL2_apply, normalizedCoeffCLM_SpaceTime_pi_apply,
    normalizedCoeffCLM_SpaceTime_numAllPowCLM]

lemma coeffSeminormSeq_eq_norm_normalizedCoeffL2_numAllPowCLM (ξ : ℝ) (hξ : ξ ≠ 0) (k : ℕ) (f : TestFunction) :
    coeffSeminormSeq ξ hξ k f = ‖normalizedCoeffL2 ξ hξ (numAllPowCLM ξ k f)‖ := by
  rw [coeffSeminormSeq_eq_norm_comp]
  simp [coeffToL2ₗ_eq_normalizedCoeffL2_numAllPowCLM (ξ := ξ) (hξ := hξ) (k := k) (f := f)]

lemma coeffSeminormSeq_eq_norm_toLp_numAllPowCLM (ξ : ℝ) (hξ : ξ ≠ 0) (k : ℕ) (f : TestFunction) :
    coeffSeminormSeq ξ hξ k f = ‖(numAllPowCLM ξ k f).toLp 2 (volume : Measure SpaceTime)‖ := by
  rw [coeffSeminormSeq_eq_norm_normalizedCoeffL2_numAllPowCLM (ξ := ξ) (hξ := hξ) (k := k) (f := f)]
  simpa using
    (norm_normalizedCoeffL2_eq_norm_toLp (ξ := ξ) (hξ := hξ) (f := numAllPowCLM ξ k f))

lemma coeffSeminormSeq_le_norm_toLp_numAllPowCLM (ξ : ℝ) (hξ : ξ ≠ 0) (k : ℕ) (f : TestFunction) :
    coeffSeminormSeq ξ hξ k f ≤ ‖(numAllPowCLM ξ k f).toLp 2 (volume : Measure SpaceTime)‖ := by
  rw [coeffSeminormSeq_eq_norm_normalizedCoeffL2_numAllPowCLM (ξ := ξ) (hξ := hξ) (k := k) (f := f)]
  exact norm_normalizedCoeffL2_le_norm_toLp (ξ := ξ) (hξ := hξ) (f := numAllPowCLM ξ k f)

/-! ## `coeffSeminormSeq` is bounded by the canonical Schwartz seminorm sequence -/

private theorem exists_norm_toLp_le_schwartzSeminormSeq :
    ∃ K : ℕ, ∃ C : ℝ≥0, ∀ g : TestFunction,
      ‖g.toLp 2 (volume : Measure SpaceTime)‖ ≤ (C : ℝ) * OSforGFF.schwartzSeminormSeq K g := by
  rcases (SchwartzMap.norm_toLp_le_seminorm (𝕜 := ℝ) (F := ℝ) (E := SpaceTime)
      (p := (2 : ℝ≥0∞)) (μ := (volume : Measure SpaceTime))) with ⟨K, C, hC0, hC⟩
  refine ⟨K, ⟨⟨C, hC0⟩, ?_⟩⟩
  intro g
  have hsubset : Finset.Iic (K, 0) ⊆ Finset.Iic (K, K) := by
    intro i hi
    exact
      Finset.mem_Iic.mpr <|
        le_trans (Finset.mem_Iic.mp hi) (Prod.mk_le_mk.2 ⟨le_rfl, Nat.zero_le _⟩)
  have hsup :
      (Finset.Iic (K, 0)).sup (OSforGFF.schwartzSeminormFamily_TestFunction) g ≤
        OSforGFF.schwartzSeminormSeq K g := by
    simpa [OSforGFF.schwartzSeminormSeq] using
      (Finset.sup_mono (f := OSforGFF.schwartzSeminormFamily_TestFunction) hsubset g)
  exact (hC g).trans (mul_le_mul_of_nonneg_left hsup hC0)

private theorem exists_bound_schwartzSeminormSeq_numAllPowCLM (ξ : ℝ) (K k : ℕ) :
    ∃ s : Finset ℕ, ∃ C : ℝ≥0, ∀ f : TestFunction,
      OSforGFF.schwartzSeminormSeq K (numAllPowCLM ξ k f) ≤ (C : ℝ) * (s.sup OSforGFF.schwartzSeminormSeq) f := by
  have hcont :
      Continuous
        ((OSforGFF.schwartzSeminormSeq K).comp
          ((numAllPowCLM ξ k : TestFunction →L[ℝ] TestFunction) : TestFunction →ₗ[ℝ] TestFunction)) := by
    exact (OSforGFF.schwartzSeminormSeq_withSeminorms.continuous_seminorm K).comp
      (numAllPowCLM ξ k).continuous
  rcases
      (Seminorm.bound_of_continuous (p := OSforGFF.schwartzSeminormSeq) (E := TestFunction)
        OSforGFF.schwartzSeminormSeq_withSeminorms
        ((OSforGFF.schwartzSeminormSeq K).comp
          ((numAllPowCLM ξ k : TestFunction →L[ℝ] TestFunction) : TestFunction →ₗ[ℝ] TestFunction)) hcont)
    with ⟨s, C, _hCne, hle⟩
  refine ⟨s, C, ?_⟩
  intro f
  simpa [Seminorm.comp_apply, Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul, mul_assoc] using (hle f)

theorem isBounded_schwartzSeminormSeq_coeffSeminormSeq (ξ : ℝ) (hξ : ξ ≠ 0) :
    Seminorm.IsBounded OSforGFF.schwartzSeminormSeq (coeffSeminormSeq ξ hξ)
      (LinearMap.id : TestFunction →ₗ[ℝ] TestFunction) := by
  rcases exists_norm_toLp_le_schwartzSeminormSeq with ⟨K, CtoLp, htoLp⟩
  intro k
  rcases exists_bound_schwartzSeminormSeq_numAllPowCLM (ξ := ξ) (K := K) (k := k) with ⟨s, C₁, hle⟩
  refine ⟨s, CtoLp * C₁, ?_⟩
  intro f
  have h₁ :=
    coeffSeminormSeq_le_norm_toLp_numAllPowCLM (ξ := ξ) (hξ := hξ) (k := k) (f := f)
  have htoLp' :
      ‖(numAllPowCLM ξ k f).toLp 2 (volume : Measure SpaceTime)‖ ≤
        (CtoLp : ℝ) * ((C₁ : ℝ) * (s.sup OSforGFF.schwartzSeminormSeq) f) := by
    have h :=
      (htoLp (g := numAllPowCLM ξ k f)).trans
        (mul_le_mul_of_nonneg_left (hle f) (by exact_mod_cast (zero_le CtoLp)))
    simpa [mul_assoc] using h
  have hcoeff := h₁.trans htoLp'
  simpa [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using hcoeff

/-! Once we also know the **reverse** boundedness `schwartzSeminormSeq ≲ coeffSeminormSeq`,
the remaining hypothesis `OSforGFF.SchwartzNuclearInclusion` follows from the proved local
nuclearity of the coefficient inclusions.

This reverse boundedness is proved in `OSforGFF.NuclearSpace.PhysHermiteSpaceTimeSchwartzToCoeffBound`,
so combining the two directions yields `OSforGFF.SchwartzNuclearInclusion` (and hence
`OSforGFF.NuclearSpaceStd TestFunction`) in the spacetime Hermite model; see
`OSforGFF.NuclearSpace.PhysHermiteSpaceTimeSchwartzNuclearInclusion`.
-/
theorem schwartzNuclearInclusion_of_equiv_coeffSeminormSeq
    (ξ : ℝ) (hξ : ξ ≠ 0)
    (hb_sch_le_coeff :
      Seminorm.IsBounded (coeffSeminormSeq ξ hξ) OSforGFF.schwartzSeminormSeq
        (LinearMap.id : TestFunction →ₗ[ℝ] TestFunction)) :
    OSforGFF.SchwartzNuclearInclusion := by
  refine
    OSforGFF.schwartzNuclearInclusion_of_equivFamily
      (q := coeffSeminormSeq ξ hξ)
      (hqmono := coeffSeminormSeq_mono (ξ := ξ) (hξ := hξ))
      (hb_q_le_sch := isBounded_schwartzSeminormSeq_coeffSeminormSeq (ξ := ξ) (hξ := hξ))
      (hb_sch_le_q := hb_sch_le_coeff)
      (hqNuclear := coeffSeminormSeq_localNuclear (ξ := ξ) (hξ := hξ))

end SpaceTimeHermite

end

end PhysLean
