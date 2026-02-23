import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import OSforGFF.NuclearSpace.HermiteSchwartz
import OSforGFF.NuclearSpace.PhysHermite

/-!
# PhysLean Hermite functions as Schwartz maps

This file bridges `PhysLean.physHermite` and the `SchwartzMap` API.

The main constructions are:

* the scaled Gaussian `x ↦ exp(-x^2/(2 ξ^2))` as a Schwartz function (for `ξ ≠ 0`);
* the unnormalized harmonic-oscillator eigenfunctions
  `x ↦ physHermite n (x/ξ) * exp(-x^2/(2 ξ^2))` as Schwartz functions.

This is designed to match PhysLean's `ξ`-scaling conventions, while reusing Mathlib's
Schwartz-space infrastructure.
-/

open scoped BigOperators

namespace PhysLean

noncomputable section

open SchwartzMap

open MeasureTheory

/-! ## Temperate growth for polynomial functions -/

lemma hasTemperateGrowth_aeval_intPoly (p : Polynomial ℤ) :
    Function.HasTemperateGrowth (fun x : ℝ ↦ (Polynomial.aeval x p : ℝ)) := by
  classical
  refine Polynomial.induction_on' p (motive := fun p ↦
      Function.HasTemperateGrowth (fun x : ℝ ↦ (Polynomial.aeval x p : ℝ)))
    (fun p q hp hq ↦ ?_) (fun n a ↦ ?_)
  · simpa [Polynomial.aeval_add] using hp.add hq
  · simpa [Polynomial.aeval_monomial] using
      (by fun_prop :
        Function.HasTemperateGrowth (fun x : ℝ ↦ (algebraMap ℤ ℝ a) * x ^ n))

lemma hasTemperateGrowth_physHermite (n : ℕ) :
    Function.HasTemperateGrowth (fun x : ℝ ↦ physHermite n x) := by
  simpa [physHermite_eq_aeval] using (hasTemperateGrowth_aeval_intPoly (p := physHermite n))

/-! ## The `ξ`-scaled Gaussian as a Schwartz function -/

/-- The scaling `x ↦ x / ξ` as a continuous linear equiv, for `ξ ≠ 0`. -/
noncomputable def divCLM (ξ : ℝ) (hξ : ξ ≠ 0) : ℝ ≃L[ℝ] ℝ :=
  ContinuousLinearEquiv.smulLeft (Units.mk0 ξ⁻¹ (inv_ne_zero hξ))

@[simp] lemma divCLM_apply (ξ : ℝ) (hξ : ξ ≠ 0) (x : ℝ) :
    divCLM ξ hξ x = x / ξ := by
  simp [divCLM, div_eq_mul_inv, mul_comm]

/-- `gaussianHO ξ` as a Schwartz map, constructed by scaling `OSforGFF.HermiteSchwartz.gaussianSchwartz`. -/
noncomputable def gaussianHOSchwartz (ξ : ℝ) (hξ : ξ ≠ 0) : 𝓢(ℝ, ℝ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv (𝕜 := ℝ) (divCLM ξ hξ)
    OSforGFF.HermiteSchwartz.gaussianSchwartz

@[simp] lemma gaussianHOSchwartz_apply (ξ : ℝ) (hξ : ξ ≠ 0) (x : ℝ) :
    gaussianHOSchwartz ξ hξ x = gaussianHO ξ x := by
  -- `gaussianHO ξ x = exp (-(x^2)/(2 ξ^2)) = gaussian (x/ξ)`
  simp [gaussianHOSchwartz, gaussianHO, divCLM_apply, OSforGFF.HermiteSchwartz.gaussian, div_eq_mul_inv,
    mul_assoc, mul_left_comm, mul_comm, pow_two]

/-! ## Eigenfunctions as Schwartz maps -/

/-- The unnormalized eigenfunction as a Schwartz map, `x ↦ physHermite n (x/ξ) * exp(-x^2/(2 ξ^2))`. -/
noncomputable def eigenfunctionRealSchwartz (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) : 𝓢(ℝ, ℝ) :=
  SchwartzMap.smulLeftCLM (𝕜 := ℝ) (F := ℝ)
      (fun x : ℝ ↦ physHermite n (x / ξ))
      (gaussianHOSchwartz ξ hξ)

@[simp] lemma eigenfunctionRealSchwartz_apply (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) (x : ℝ) :
    eigenfunctionRealSchwartz ξ hξ n x = eigenfunctionReal ξ n x := by
  have hpoly : (fun x : ℝ ↦ physHermite n (x / ξ)).HasTemperateGrowth := by
    have : (fun x : ℝ ↦ x / ξ).HasTemperateGrowth := by
      simpa [div_eq_mul_inv] using (ContinuousLinearMap.hasTemperateGrowth
        (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) ξ⁻¹))
    simpa [Function.comp, physHermite_eq_aeval] using
      (hasTemperateGrowth_physHermite n).comp this
  simp [eigenfunctionRealSchwartz, SchwartzMap.smulLeftCLM_apply_apply (F := ℝ) hpoly,
    eigenfunctionReal, gaussianHOSchwartz_apply, smul_eq_mul]

/-! ## Coefficient functionals via integration -/

/-- The coefficient functional `f ↦ ∫ x, eigenfunctionReal ξ n x * f x`. -/
noncomputable def coeffCLM (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) : 𝓢(ℝ, ℝ) →L[ℝ] ℝ :=
  (SchwartzMap.integralCLM (𝕜 := ℝ) (μ := (volume : Measure ℝ))).comp
    (SchwartzMap.smulLeftCLM (F := ℝ) (fun x : ℝ ↦ eigenfunctionRealSchwartz ξ hξ n x))

@[simp] lemma coeffCLM_apply (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) (f : 𝓢(ℝ, ℝ)) :
    coeffCLM ξ hξ n f = ∫ x : ℝ, eigenfunctionReal ξ n x * f x := by
  have hg :
      (fun x : ℝ ↦ eigenfunctionRealSchwartz ξ hξ n x).HasTemperateGrowth := by
    exact SchwartzMap.hasTemperateGrowth (f := eigenfunctionRealSchwartz ξ hξ n)
  have hcoeff :
      coeffCLM ξ hξ n f = ∫ x : ℝ, eigenfunctionRealSchwartz ξ hξ n x * f x := by
    simp [coeffCLM, SchwartzMap.integralCLM_apply,
      SchwartzMap.smulLeftCLM_apply_apply (F := ℝ) hg, smul_eq_mul,
      -eigenfunctionRealSchwartz_apply]
  simp [hcoeff, eigenfunctionRealSchwartz_apply, mul_assoc]

lemma coeffCLM_apply_eigenfunctionRealSchwartz (ξ : ℝ) (hξ : ξ ≠ 0) (n m : ℕ) :
    coeffCLM ξ hξ n (eigenfunctionRealSchwartz ξ hξ m) =
      ∫ x : ℝ, eigenfunctionReal ξ n x * eigenfunctionReal ξ m x := by
  simp [coeffCLM_apply, eigenfunctionRealSchwartz_apply, mul_assoc]

lemma coeffCLM_apply_eigenfunctionRealSchwartz_ne (ξ : ℝ) (hξ : ξ ≠ 0) {n m : ℕ} (hnm : n ≠ m) :
    coeffCLM ξ hξ n (eigenfunctionRealSchwartz ξ hξ m) = 0 := by
  simpa [coeffCLM_apply_eigenfunctionRealSchwartz (ξ := ξ) (hξ := hξ) (n := n) (m := m)] using
    (eigenfunctionReal_orthogonal (ξ := ξ) (n := n) (m := m) hnm)

lemma coeffCLM_apply_eigenfunctionRealSchwartz_eq (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) :
    coeffCLM ξ hξ n (eigenfunctionRealSchwartz ξ hξ n) =
      |ξ| * (↑n.factorial * 2 ^ n * √Real.pi) := by
  simpa [coeffCLM_apply_eigenfunctionRealSchwartz (ξ := ξ) (hξ := hξ) (n := n) (m := n),
    smul_eq_mul] using (eigenfunctionReal_norm (ξ := ξ) (n := n))

end

end PhysLean
