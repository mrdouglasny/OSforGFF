/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.Distribution.TemperedDistribution

/-!
# Fourier multiplier on Schwartz functions and tempered distributions

This file is a small local extension: it defines the continuous Fourier-multiplier operator
`SchwartzMap.fourierMultiplierCLM` on Schwartz functions and proves the basic interaction with
Fourier transform and with the Laplacian.

It lives in the `OSforGFF` namespace to avoid shadowing upstream `Mathlib` modules.
-/

@[expose] public noncomputable section

variable {ι 𝕜 E F F₁ F₂ : Type*}

namespace SchwartzMap

open scoped SchwartzMap

variable [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ E] [NormedSpace ℂ F] [NormedSpace 𝕜 F] [SMulCommClass ℂ 𝕜 F]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

open FourierTransform

variable (F) in
/-- A Fourier multiplier on Schwartz functions. -/
def fourierMultiplierCLM (g : E → 𝕜) : 𝓢(E, F) →L[𝕜] 𝓢(E, F) :=
  fourierInvCLM 𝕜 𝓢(E, F) ∘L (smulLeftCLM F g) ∘L fourierCLM 𝕜 𝓢(E, F)

theorem fourierMultiplierCLM_apply (g : E → 𝕜) (f : 𝓢(E, F)) :
    fourierMultiplierCLM F g f = 𝓕⁻ (smulLeftCLM F g (𝓕 f)) := by
  rfl

variable (𝕜) in
theorem fourierMultiplierCLM_ofReal {g : E → ℝ} (hg : g.HasTemperateGrowth) (f : 𝓢(E, F)) :
    fourierMultiplierCLM F (fun x ↦ RCLike.ofReal (K := 𝕜) (g x)) f =
    fourierMultiplierCLM F g f := by
  simp_rw [fourierMultiplierCLM_apply]
  congr 1
  exact smulLeftCLM_ofReal 𝕜 hg (𝓕 f)

theorem fourierMultiplierCLM_smul_apply {g : E → 𝕜} (hg : g.HasTemperateGrowth) (c : 𝕜)
    (f : 𝓢(E, F)) :
    fourierMultiplierCLM F (c • g) f = c • fourierMultiplierCLM F g f := by
  simp [fourierMultiplierCLM_apply, smulLeftCLM_smul hg]

theorem fourierMultiplierCLM_smul {g : E → 𝕜} (hg : g.HasTemperateGrowth) (c : 𝕜) :
    fourierMultiplierCLM F (c • g) = c • fourierMultiplierCLM F g := by
  ext1 f
  exact fourierMultiplierCLM_smul_apply (F := F) hg c f

theorem fourierMultiplierCLM_add {g₁ g₂ : E → 𝕜} (hg₁ : g₁.HasTemperateGrowth)
    (hg₂ : g₂.HasTemperateGrowth) :
    fourierMultiplierCLM F (g₁ + g₂) = fourierMultiplierCLM F g₁ + fourierMultiplierCLM F g₂ := by
  ext1 f
  simp [fourierMultiplierCLM_apply, smulLeftCLM_add hg₁ hg₂]

theorem fourierMultiplierCLM_neg {g : E → 𝕜} (hg : g.HasTemperateGrowth) :
    fourierMultiplierCLM F (-g) = -fourierMultiplierCLM F g := by
  ext1 f
  simp [fourierMultiplierCLM_apply, smulLeftCLM_neg hg]

theorem fourierMultiplierCLM_sub {g₁ g₂ : E → 𝕜} (hg₁ : g₁.HasTemperateGrowth)
    (hg₂ : g₂.HasTemperateGrowth) :
    fourierMultiplierCLM F (g₁ - g₂) = fourierMultiplierCLM F g₁ - fourierMultiplierCLM F g₂ := by
  simpa [sub_eq_add_neg, fourierMultiplierCLM_neg (F := F) hg₂] using
    (fourierMultiplierCLM_add (F := F) hg₁ hg₂.neg)

variable (F) in
theorem fourierMultiplierCLM_sum {g : ι → E → 𝕜} {s : Finset ι}
    (hg : ∀ i ∈ s, (g i).HasTemperateGrowth) :
    fourierMultiplierCLM F (fun x ↦ ∑ i ∈ s, g i x) = ∑ i ∈ s, fourierMultiplierCLM F (g i) := by
  ext1 f
  simp [fourierMultiplierCLM_apply, smulLeftCLM_sum hg]

variable [CompleteSpace F]

@[simp]
theorem fourierMultiplierCLM_const (c : 𝕜) :
    fourierMultiplierCLM F (fun (_ : E) ↦ c) = c • ContinuousLinearMap.id _ _ := by
  ext f x
  simp [fourierMultiplierCLM_apply]

theorem fourierMultiplierCLM_fourierMultiplierCLM_apply {g₁ g₂ : E → 𝕜}
    (hg₁ : g₁.HasTemperateGrowth) (hg₂ : g₂.HasTemperateGrowth) (f : 𝓢(E, F)) :
    fourierMultiplierCLM F g₁ (fourierMultiplierCLM F g₂ f) =
    fourierMultiplierCLM F (g₁ * g₂) f := by
  simp [fourierMultiplierCLM_apply, smulLeftCLM_smulLeftCLM_apply hg₁ hg₂]

theorem fourierMultiplierCLM_compL_fourierMultiplierCLM {g₁ g₂ : E → 𝕜}
    (hg₁ : g₁.HasTemperateGrowth) (hg₂ : g₂.HasTemperateGrowth) :
    fourierMultiplierCLM F g₁ ∘L fourierMultiplierCLM F g₂ =
    fourierMultiplierCLM F (g₁ * g₂) := by
  ext1 f
  exact fourierMultiplierCLM_fourierMultiplierCLM_apply (F := F) hg₁ hg₂ f

open LineDeriv Laplacian Real

theorem lineDeriv_eq_fourierMultiplierCLM (m : E) (f : 𝓢(E, F)) :
    ∂_{m} f = (2 * π * Complex.I) • fourierMultiplierCLM F (inner ℝ · m) f := by
  rw [fourierMultiplierCLM_apply, ← FourierTransform.fourierInv_smul, ← fourier_lineDerivOp_eq,
    FourierTransform.fourierInv_fourier_eq]

@[simp]
theorem fourier_fourierMultiplierCLM (g : E → 𝕜) (f : 𝓢(E, F)) :
    𝓕 (fourierMultiplierCLM F g f) = smulLeftCLM F g (𝓕 f) := by
  simp [fourierMultiplierCLM_apply]

theorem laplacian_eq_fourierMultiplierCLM (f : 𝓢(E, F)) :
    Δ f = -(2 * π) ^ 2 • fourierMultiplierCLM F (‖·‖ ^ 2) f := by
  let ι := Fin (Module.finrank ℝ E)
  let b := stdOrthonormalBasis ℝ E
  have : ∀ i (hi : i ∈ Finset.univ), (inner ℝ · (b i) ^ 2).HasTemperateGrowth := by
    fun_prop
  simp_rw [laplacian_eq_sum b, ← b.sum_sq_inner_left, fourierMultiplierCLM_sum (F := F) this,
    ContinuousLinearMap.coe_sum', Finset.sum_apply, Finset.smul_sum]
  congr 1
  ext i x
  simp_rw [smul_apply, lineDeriv_eq_fourierMultiplierCLM]
  rw [← fourierMultiplierCLM_ofReal (F := F) ℂ (by fun_prop)]
  simp_rw [map_smul, smul_apply, smul_smul]
  congr 1
  · ring_nf
    simp
  rw [fourierMultiplierCLM_ofReal (F := F) ℂ (by fun_prop)]
  rw [fourierMultiplierCLM_fourierMultiplierCLM_apply (F := F) (by fun_prop) (by fun_prop)]
  congr 3
  ext y
  simp [pow_two]

end SchwartzMap

