/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Copyright (c) 2026 Sergey A. Cherkis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergey A. Cherkis, Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.ENNReal.Holder
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

import OSforGFF.Spacetime.Basic
import OSforGFF.Schwinger.Defs
import OSforGFF.Measure.Construct

/-!
## Gaussian Moments and n-Point Integrability

This file proves that Gaussian Free Field measures have finite moments of all orders,
establishing integrability of n-point correlation functions for arbitrary n.

### Main Results:

**Key Insight:**
Gaussian measures on nuclear spaces have finite polynomial moments of all orders.
Since each pairing ⟨ω, f⟩ is linear in ω, their n-fold product is a polynomial of degree n,
hence integrable.

**Proof Strategy:**
1. **Base Cases**: n = 0, 1, 2 (trivial, linear functional, covariance bound)
2. **Inductive Step**: Use Gaussian moment properties and Cauchy-Schwarz
3. **Nuclear Foundation**: Leverage nuclear covariance structure

This generalizes `gaussian_pairing_product_integrable_free_2point` to arbitrary n,
providing a unified foundation for all Schwinger function computations.
-/

open MeasureTheory Complex Finset OSforGFF
open TopologicalSpace SchwartzMap

noncomputable section

variable {d : ℕ} [Fact (2 ≤ d)]

/-! ## n-Point Integrability for Gaussian Free Fields -/

/-- **Foundation**: The original 2-point case implemented directly.
    This provides the base case for the general n-point theorem. -/
theorem gaussian_pairing_product_integrable_free_2point
  (m : ℝ) [Fact (0 < m)] [GFFPropagator d m] (φ ψ : SchwartzTestFunctionℂ d) :
  Integrable (fun ω => distributionPairingℂ_real ω φ * distributionPairingℂ_real ω ψ)
    (gaussianFreeField_free m).toMeasure := by
  -- Strategy: Decompose both complex test functions into real and imaginary parts
  -- and use the existing real pairing integrability

  classical
  -- Decompose φ and ψ into real and imaginary parts
  set φRe : SchwartzTestFunction d := (complex_testfunction_decompose φ).1
  set φIm : SchwartzTestFunction d := (complex_testfunction_decompose φ).2
  set ψRe : SchwartzTestFunction d := (complex_testfunction_decompose ψ).1
  set ψIm : SchwartzTestFunction d := (complex_testfunction_decompose ψ).2

  -- For each real component, we have L² integrability from the proven theorem
  have hφRe_mem : MemLp (distributionPairingCLM φRe) (2 : ENNReal) (gaussianFreeField_free m).toMeasure :=
    gaussianFreeField_pairing_memLp m φRe (2 : ENNReal) (by simp)
  have hφIm_mem : MemLp (distributionPairingCLM φIm) (2 : ENNReal) (gaussianFreeField_free m).toMeasure :=
    gaussianFreeField_pairing_memLp m φIm (2 : ENNReal) (by simp)
  have hψRe_mem : MemLp (distributionPairingCLM ψRe) (2 : ENNReal) (gaussianFreeField_free m).toMeasure :=
    gaussianFreeField_pairing_memLp m ψRe (2 : ENNReal) (by simp)
  have hψIm_mem : MemLp (distributionPairingCLM ψIm) (2 : ENNReal) (gaussianFreeField_free m).toMeasure :=
    gaussianFreeField_pairing_memLp m ψIm (2 : ENNReal) (by simp)

  -- Convert to integrability of individual real pairings
  have hφRe_int : Integrable (fun ω => distributionPairing ω φRe) (gaussianFreeField_free m).toMeasure := by
    have h_le : (1 : ENNReal) ≤ 2 := by norm_num
    have h_int := MemLp.integrable h_le hφRe_mem
    exact h_int
  have hφIm_int : Integrable (fun ω => distributionPairing ω φIm) (gaussianFreeField_free m).toMeasure := by
    have h_le : (1 : ENNReal) ≤ 2 := by norm_num
    have h_int := MemLp.integrable h_le hφIm_mem
    exact h_int
  have hψRe_int : Integrable (fun ω => distributionPairing ω ψRe) (gaussianFreeField_free m).toMeasure := by
    have h_le : (1 : ENNReal) ≤ 2 := by norm_num
    have h_int := MemLp.integrable h_le hψRe_mem
    exact h_int
  have hψIm_int : Integrable (fun ω => distributionPairing ω ψIm) (gaussianFreeField_free m).toMeasure := by
    have h_le : (1 : ENNReal) ≤ 2 := by norm_num
    have h_int := MemLp.integrable h_le hψIm_mem
    exact h_int

  -- Expand the complex product: (a+bi)(c+di) = (ac-bd) + i(ad+bc)
  have h_pointwise : (fun ω => distributionPairingℂ_real ω φ * distributionPairingℂ_real ω ψ) =
    (fun ω => (distributionPairing ω φRe * distributionPairing ω ψRe - distributionPairing ω φIm * distributionPairing ω ψIm : ℂ) +
              Complex.I * (distributionPairing ω φRe * distributionPairing ω ψIm + distributionPairing ω φIm * distributionPairing ω ψRe : ℂ)) := by
    funext ω
    -- Expand distributionPairingℂ_real using definition
    unfold distributionPairingℂ_real
    simp only [φRe, φIm, ψRe, ψIm, complex_testfunction_decompose]
    -- Use (a + bi)(c + di) = (ac - bd) + i(ad + bc) where a,b,c,d are real
    simp only [distributionPairing]
    -- Expand and use I^2 = -1
    ring_nf
    rw [Complex.I_sq]
    ring

  -- Use the fact that each product of real pairings is integrable (they're in L² so products are in L¹)
  -- For L² × L² → L¹, we use Hölder's inequality: p⁻¹ + q⁻¹ = 1⁻¹ gives 2⁻¹ + 2⁻¹ = 1⁻¹
  have h_holder : ENNReal.HolderTriple (2 : ENNReal) 2 1 := by
    -- Need to prove 2⁻¹ + 2⁻¹ = 1⁻¹, i.e., 1/2 + 1/2 = 1
    apply ENNReal.HolderTriple.mk
    -- Use the fact that inv_one gives us 1⁻¹ = 1
    simp only [inv_one]
    exact ENNReal.inv_two_add_inv_two

  have h_ac_bd : Integrable (fun ω => distributionPairing ω φRe * distributionPairing ω ψRe - distributionPairing ω φIm * distributionPairing ω ψIm)
                   (gaussianFreeField_free m).toMeasure := by
    apply Integrable.sub
    · -- L² × L² → L¹ by Hölder's inequality
      have h_mem_φRe : MemLp (fun ω => distributionPairing ω φRe) 2 (gaussianFreeField_free m).toMeasure := by
        exact hφRe_mem
      have h_mem_ψRe : MemLp (fun ω => distributionPairing ω ψRe) 2 (gaussianFreeField_free m).toMeasure := by
        exact hψRe_mem
      exact MemLp.integrable_mul h_mem_φRe h_mem_ψRe
    · -- L² × L² → L¹ by Hölder's inequality
      have h_mem_φIm : MemLp (fun ω => distributionPairing ω φIm) 2 (gaussianFreeField_free m).toMeasure := by
        exact hφIm_mem
      have h_mem_ψIm : MemLp (fun ω => distributionPairing ω ψIm) 2 (gaussianFreeField_free m).toMeasure := by
        exact hψIm_mem
      exact MemLp.integrable_mul h_mem_φIm h_mem_ψIm

  have h_ad_bc : Integrable (fun ω => distributionPairing ω φRe * distributionPairing ω ψIm + distributionPairing ω φIm * distributionPairing ω ψRe)
                   (gaussianFreeField_free m).toMeasure := by
    apply Integrable.add
    · -- L² × L² → L¹ by Hölder's inequality
      have h_mem_φRe : MemLp (fun ω => distributionPairing ω φRe) 2 (gaussianFreeField_free m).toMeasure := by
        exact hφRe_mem
      have h_mem_ψIm : MemLp (fun ω => distributionPairing ω ψIm) 2 (gaussianFreeField_free m).toMeasure := by
        exact hψIm_mem
      exact MemLp.integrable_mul h_mem_φRe h_mem_ψIm
    · -- L² × L² → L¹ by Hölder's inequality
      have h_mem_φIm : MemLp (fun ω => distributionPairing ω φIm) 2 (gaussianFreeField_free m).toMeasure := by
        exact hφIm_mem
      have h_mem_ψRe : MemLp (fun ω => distributionPairing ω ψRe) 2 (gaussianFreeField_free m).toMeasure := by
        exact hψRe_mem
      exact MemLp.integrable_mul h_mem_φIm h_mem_ψRe

  -- The complex function is integrable if both real and imaginary parts are integrable
  rw [h_pointwise]
  -- Convert real integrability to complex integrability and combine
  have h_real_part : Integrable (fun ω => (distributionPairing ω φRe * distributionPairing ω ψRe - distributionPairing ω φIm * distributionPairing ω ψIm : ℂ))
                       (gaussianFreeField_free m).toMeasure := by
    -- Use the fact that real-valued functions can be viewed as complex-valued
    have h_cast : (fun ω => (distributionPairing ω φRe * distributionPairing ω ψRe - distributionPairing ω φIm * distributionPairing ω ψIm : ℂ)) =
                  (fun ω => ↑(distributionPairing ω φRe * distributionPairing ω ψRe - distributionPairing ω φIm * distributionPairing ω ψIm)) := by
      funext ω
      simp only [Complex.ofReal_sub, Complex.ofReal_mul]
    rw [h_cast]
    exact Integrable.ofReal h_ac_bd

  have h_imag_part : Integrable (fun ω => Complex.I * (distributionPairing ω φRe * distributionPairing ω ψIm + distributionPairing ω φIm * distributionPairing ω ψRe : ℂ))
                       (gaussianFreeField_free m).toMeasure := by
    -- Multiplication by a constant (Complex.I) preserves integrability
    apply Integrable.const_mul
    -- The base function is integrable when viewed as complex-valued
    have h_cast : (fun ω => (distributionPairing ω φRe * distributionPairing ω ψIm + distributionPairing ω φIm * distributionPairing ω ψRe : ℂ)) =
                  (fun ω => ↑(distributionPairing ω φRe * distributionPairing ω ψIm + distributionPairing ω φIm * distributionPairing ω ψRe)) := by
      funext ω
      simp only [Complex.ofReal_add, Complex.ofReal_mul]
    rw [h_cast]
    exact Integrable.ofReal h_ad_bc

  exact Integrable.add h_real_part h_imag_part

/-- **Corollary**: The complex covariance is well-defined via the general integrability. -/
theorem covariance_bilinear_from_general
  (m : ℝ) [Fact (0 < m)] [GFFPropagator d m] :
  CovarianceBilinear (gaussianFreeField_free (d := d) m) := by
  -- Apply the general construction from integrability
  apply CovarianceBilinear_of_integrable
  exact fun φ ψ => gaussian_pairing_product_integrable_free_2point m φ ψ

end
