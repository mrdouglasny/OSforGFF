/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/

import Mathlib.Tactic  -- gives `ext` and `simp` power
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Constructions

import Mathlib.Topology.Algebra.Module.LinearMapPiProd

import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction

import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.LineDeriv.Basic

import Mathlib.Data.Nat.Choose.Sum

import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Density

import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-!
## Functional Analysis for AQFT

This file provides functional analysis tools for Algebraic Quantum Field Theory,
focusing on integrability, Schwartz function properties, and L² embeddings.

### Key Definitions & Theorems:

**Schwartz Space Properties:**
- `SchwartzMap.hasTemperateGrowth_general`: Schwartz functions have temperate growth
- `SchwartzMap.integrable_mul_bounded`: Schwartz × bounded → integrable
- `SchwartzMap.integrable_conj`: Conjugate of Schwartz function is integrable
- `SchwartzMap.translate`: Translation of Schwartz functions
- `schwartz_integrable_decay`: Decay bounds for Schwartz function integrals

**Complex Embeddings:**
- `Complex.ofRealCLM_isometry`: Real→Complex embedding is isometric
- `Complex.ofRealCLM_continuous_compLp`: Continuous lifting to Lp spaces
- `embedding_real_to_complex`: Canonical ℝ→ℂ embedding for Lp functions

**Schwartz→L² Embedding:**
- `schwartzToL2`: Embedding Schwartz functions into L² space
- `schwartzToL2'`: Alternative embedding for EuclideanSpace types

**L∞·L² Multiplication:**
- `linfty_mul_L2_CLM`: Continuous bilinear map L∞ × L² → L²
- `linfty_mul_L2_CLM_norm_bound`: Norm bound ‖f · g‖₂ ≤ ‖f‖∞ · ‖g‖₂

**Integrability Results:**
- `integrableOn_ball_of_radial`: Radial functions integrable on balls
- `integrableOn_ball_of_rpow_decay`: Power-law decay integrable on balls
- `integrableOn_compact_diff_ball`: Integrability on compact ∖ ball
- `locallyIntegrable_of_rpow_decay_real`: Local integrability from power decay (d ≥ 3)
- `polynomial_decay_integrable_3d`: 1/‖x‖ integrable on 3D balls
- `schwartz_bilinear_integrable_of_translationInvariant_L1`: Bilinear Schwartz integrability

**Vanishing & Bounds:**
- `schwartz_vanishing_linear_bound_general`: Linear vanishing bounds for Schwartz functions

**Bump Function Convolutions:**
- `bumpSelfConv`: Self-convolution of bump functions
- `bumpSelfConv_nonneg`, `bumpSelfConv_integral`: Properties of self-convolution
- `bumpSelfConv_support_subset`, `bumpSelfConv_support_tendsto`: Support control
- `double_mollifier_convergence`: Convergence of double mollifier approximations

**Utility Lemmas:**
- `norm_exp_I_mul_real`, `norm_exp_neg_I_mul_real`: ‖exp(±i·r)‖ = 1
- `sub_const_hasTemperateGrowth`: Translation has temperate growth
-/

open MeasureTheory NNReal ENNReal Complex
open TopologicalSpace Measure
open scoped FourierTransform

noncomputable section

/-! ## Proven theorems in this file

The following L∞ × L² multiplication theorems are fully proven (2025-12-13):
- `linfty_mul_L2_CLM` (line ~607): L∞ × L² → L² bounded linear operator
- `linfty_mul_L2_CLM_spec` (line ~639): pointwise specification (g·f)(x) = g(x)·f(x) a.e.
- `linfty_mul_L2_CLM_norm_bound` (line ~650): operator norm bound ‖T_g f‖ ≤ C·‖f‖
-/

open MeasureTheory.Measure


variable {d : ℕ} [NeZero d]

-- Add inner product space structure
variable [Fintype (Fin d)]

/-! ## Schwartz function properties -/

/- Multiplication of Schwarz functions
 -/

open scoped SchwartzMap

variable {𝕜 : Type} [RCLike 𝕜]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

-- General version that works for any normed space over ℝ
lemma SchwartzMap.hasTemperateGrowth_general
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (g : 𝓢(E, V)) :
    Function.HasTemperateGrowth (⇑g) :=
  hasTemperateGrowth g

/- Measure lifting from real to complex Lp spaces -/

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

-- Add measurable space instances for Lp spaces
instance [MeasurableSpace α] (μ : Measure α) : MeasurableSpace (Lp ℝ 2 μ) := borel _
instance [MeasurableSpace α] (μ : Measure α) : BorelSpace (Lp ℝ 2 μ) := ⟨rfl⟩
instance [MeasurableSpace α] (μ : Measure α) : MeasurableSpace (Lp ℂ 2 μ) := borel _
instance [MeasurableSpace α] (μ : Measure α) : BorelSpace (Lp ℂ 2 μ) := ⟨rfl⟩

-- Check if Complex.ofRealCLM is an isometry
lemma Complex.ofRealCLM_isometry : Isometry (Complex.ofRealCLM : ℝ →L[ℝ] ℂ) := by
  -- Complex.ofRealCLM is defined as ofRealLI.toContinuousLinearMap,
  -- where ofRealLI is a linear isometry
  have h : (Complex.ofRealCLM : ℝ →L[ℝ] ℂ) = Complex.ofRealLI.toContinuousLinearMap := rfl
  rw [h]
  -- The coercion to function is the same for both
  convert Complex.ofRealLI.isometry

-- Use this to prove our specific case
lemma Complex.ofRealCLM_continuous_compLp {α : Type*} [MeasurableSpace α] {μ : Measure α} :
  Continuous (fun φ : Lp ℝ 2 μ => Complex.ofRealCLM.compLp φ : Lp ℝ 2 μ → Lp ℂ 2 μ) := by
  -- The function φ ↦ L.compLp φ is the application of the continuous linear map
  -- ContinuousLinearMap.compLpL p μ L, which is continuous
  exact (ContinuousLinearMap.compLpL 2 μ Complex.ofRealCLM).continuous

/--
Compose an Lp function with a continuous linear map.
This should be the canonical way to lift real Lp functions to complex Lp functions.
-/
noncomputable def composed_function {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : Lp ℝ 2 μ) (A : ℝ →L[ℝ] ℂ): Lp ℂ 2 μ :=
  A.compLp f

-- Check that we get the expected norm bound
example {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : Lp ℝ 2 μ) (A : ℝ →L[ℝ] ℂ) : ‖A.compLp f‖ ≤ ‖A‖ * ‖f‖ :=
  ContinuousLinearMap.norm_compLp_le A f

/--
Embedding from real Lp functions to complex Lp functions using the canonical embedding ℝ → ℂ.
-/
noncomputable def embedding_real_to_complex {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (φ : Lp ℝ 2 μ) : Lp ℂ 2 μ :=
  composed_function φ (Complex.ofRealCLM)

section LiftMeasure
  variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

  /--
  Lifts a probability measure from the space of real Lp functions to the space of
  complex Lp functions, with support on the real subspace.
  -/
  noncomputable def liftMeasure_real_to_complex
      (dμ_real : ProbabilityMeasure (Lp ℝ 2 μ)) :
      ProbabilityMeasure (Lp ℂ 2 μ) :=
    let dμ_complex_measure : Measure (Lp ℂ 2 μ) :=
      Measure.map embedding_real_to_complex dμ_real
    have h_ae : AEMeasurable embedding_real_to_complex dμ_real := by
      apply Continuous.aemeasurable
      unfold embedding_real_to_complex composed_function
      have : Continuous (fun φ : Lp ℝ 2 μ => Complex.ofRealCLM.compLp φ : Lp ℝ 2 μ → Lp ℂ 2 μ) :=
        Complex.ofRealCLM_continuous_compLp
      exact this
    have h_is_prob := isProbabilityMeasure_map h_ae
    ⟨dμ_complex_measure, h_is_prob⟩

end LiftMeasure



/-! ## Fourier Transform as Linear Isometry on L² Spaces

The key challenge in defining the Fourier transform on L² spaces is that the Fourier integral
∫ f(x) e^(-2πi⟨x,ξ⟩) dx may not converge for arbitrary f ∈ L²(ℝᵈ).

**Construction Strategy (following the Schwartz space approach):**
1. **Dense Core**: Use Schwartz functions 𝒮(ℝᵈ) as the dense subset where Fourier integrals converge
2. **Schwartz Fourier**: Apply the Fourier transform on Schwartz space (unitary)
3. **Embedding to L²**: Embed Schwartz functions into L² space
4. **Plancherel on Core**: Show ‖ℱf‖₂ = ‖f‖₂ for f ∈ 𝒮(ℝᵈ)
5. **Extension**: Use the universal property of L² to extend to all of L²

This construction gives a unitary operator ℱ : L²(ℝᵈ) ≃ₗᵢ[ℂ] L²(ℝᵈ).
-/

variable {d : ℕ} [NeZero d] [Fintype (Fin d)]

-- Type abbreviations for clarity
abbrev EuclideanRd (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev SchwartzRd (d : ℕ) := SchwartzMap (EuclideanRd d) ℂ
abbrev L2Complex (d : ℕ) := Lp ℂ 2 (volume : Measure (EuclideanRd d))

/-! ### Core construction components (using Mathlib APIs) -/


/-- Embedding Schwartz functions into L² space using Mathlib's toLpCLM.
    This is a continuous linear map from Schwartz space to L²(ℝᵈ, ℂ).
    ✅ IMPLEMENTED: Uses SchwartzMap.toLpCLM from Mathlib -/
noncomputable def schwartzToL2 (d : ℕ) : SchwartzRd d →L[ℂ] L2Complex d :=
  SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure (EuclideanRd d))

/-- Alternative embedding that produces the exact L² type expected by the unprimed theorems.
    This maps Schwartz functions to Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))).
    The difference from schwartzToL2 is only in the type representation, not the mathematical content. -/
noncomputable def schwartzToL2' (d : ℕ) [NeZero d] [Fintype (Fin d)] :
  SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ →L[ℂ] Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
  SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))

/-! ## L∞ Multiplication on L² Spaces

This section proves that multiplication by L∞ functions defines bounded operators on L².

Mathematical background:
- If g ∈ L∞(μ) with ‖g‖∞ ≤ C, then f ↦ g·f is a bounded linear operator L² → L²
- The operator norm satisfies ‖Mg‖ ≤ C
- The action is pointwise a.e.: (Mg f)(x) = g(x) · f(x) a.e.

Proof method (2025-12-13):
- Uses Mathlib's `eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm` for the L∞ × Lp → Lp bound
- For ℂ, multiplication equals scalar multiplication (g * f = g • f)
- Hölder's inequality via `MemLp.mul` with HolderTriple ∞ 2 2

These theorems are used to construct specific multiplication operators
(e.g., momentumWeightSqrt_mul_CLM) without repeating technical details.
-/

/-- Helper lemma for the norm bound of the multiplication operator. -/
lemma linfty_mul_L2_bound_aux {μ : Measure α}
    (g : α → ℂ) (_hg_meas : Measurable g) (C : ℝ) (_hC : 0 < C)
    (hg_bound : ∀ᵐ x ∂μ, ‖g x‖ ≤ C)
    (f : Lp ℂ 2 μ) :
    eLpNorm (g * ⇑f) 2 μ ≤ ENNReal.ofReal C * eLpNorm f 2 μ := by
  -- For ℂ, multiplication is the same as scalar multiplication
  have h_eq : g * ⇑f = g • ⇑f := rfl
  rw [h_eq]
  -- Use the L∞ × Lp → Lp bound for smul
  have h_smul_le := eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm (p := 2)
    (Lp.memLp f).aestronglyMeasurable g
  have h_g_norm : eLpNorm g ∞ μ ≤ ENNReal.ofReal C := by
    rw [eLpNorm_exponent_top]
    exact eLpNormEssSup_le_of_ae_bound hg_bound
  calc eLpNorm (g • ⇑f) 2 μ
      ≤ eLpNorm g ∞ μ * eLpNorm f 2 μ := h_smul_le
    _ ≤ ENNReal.ofReal C * eLpNorm f 2 μ := by gcongr

/-- Given a measurable function `g` that is essentially bounded by `C`,
    multiplication by `g` defines a bounded linear operator on `L²`. -/
noncomputable def linfty_mul_L2_CLM {μ : Measure α}
    (g : α → ℂ) (hg_meas : Measurable g) (C : ℝ) (hC : 0 < C)
    (hg_bound : ∀ᵐ x ∂μ, ‖g x‖ ≤ C) :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ := by
  have hg_mem : MemLp g ∞ μ := memLp_top_of_bound hg_meas.aestronglyMeasurable C hg_bound
  refine LinearMap.mkContinuous
    { toFun := fun f => (MemLp.mul (p:=∞) (q:=2) (r:=2) (Lp.memLp f) hg_mem).toLp (g * ⇑f)
      map_add' := fun f1 f2 => by
        ext1
        filter_upwards [MemLp.coeFn_toLp (MemLp.mul (p:=∞) (q:=2) (r:=2) (Lp.memLp (f1 + f2)) hg_mem),
                        MemLp.coeFn_toLp (MemLp.mul (p:=∞) (q:=2) (r:=2) (Lp.memLp f1) hg_mem),
                        MemLp.coeFn_toLp (MemLp.mul (p:=∞) (q:=2) (r:=2) (Lp.memLp f2) hg_mem),
                        Lp.coeFn_add f1 f2,
                        Lp.coeFn_add ((MemLp.mul (p:=∞) (q:=2) (r:=2) (Lp.memLp f1) hg_mem).toLp (g * ⇑f1)) ((MemLp.mul (p:=∞) (q:=2) (r:=2) (Lp.memLp f2) hg_mem).toLp (g * ⇑f2))] with x h1 h2 h3 h4 h5
        simp only [h1, h2, h3, h4, h5, Pi.add_apply, Pi.mul_apply, mul_add]
      map_smul' := fun c f => by
        ext1
        filter_upwards [MemLp.coeFn_toLp (MemLp.mul (p:=∞) (q:=2) (r:=2) (Lp.memLp (c • f)) hg_mem),
                        MemLp.coeFn_toLp (MemLp.mul (p:=∞) (q:=2) (r:=2) (Lp.memLp f) hg_mem),
                        Lp.coeFn_smul c f,
                        Lp.coeFn_smul c ((MemLp.mul (p:=∞) (q:=2) (r:=2) (Lp.memLp f) hg_mem).toLp (g * ⇑f))] with x h1 h2 h3 h4
        simp only [h1, h2, h3, h4, Pi.smul_apply, Pi.mul_apply, RingHom.id_apply, smul_eq_mul]
        ring }
    C
    (fun f => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, Lp.norm_toLp]
      apply ENNReal.toReal_le_of_le_ofReal (by positivity)
      refine (linfty_mul_L2_bound_aux g hg_meas C hC hg_bound f).trans ?_
      rw [ENNReal.ofReal_mul (le_of_lt hC)]
      gcongr
      exact le_of_eq (ENNReal.ofReal_toReal (Lp.memLp f).eLpNorm_ne_top).symm
    )

/-- The multiplication operator acts pointwise almost everywhere on `L²`. -/
lemma linfty_mul_L2_CLM_spec {μ : Measure α}
    (g : α → ℂ) (hg_meas : Measurable g) (C : ℝ) (hC : 0 < C)
    (hg_bound : ∀ᵐ x ∂μ, ‖g x‖ ≤ C)
    (f : Lp ℂ 2 μ) :
    (linfty_mul_L2_CLM g hg_meas C hC hg_bound f) =ᵐ[μ] fun x => g x * f x := by
  simp [linfty_mul_L2_CLM]
  exact MemLp.coeFn_toLp _

/-- The operator norm of the multiplication operator is bounded by C.
    This gives ‖Mg f‖₂ ≤ C · ‖f‖₂ for all f ∈ L². -/
theorem linfty_mul_L2_CLM_norm_bound {μ : Measure α}
    (g : α → ℂ) (hg_meas : Measurable g) (C : ℝ) (hC : 0 < C)
    (hg_bound : ∀ᵐ x ∂μ, ‖g x‖ ≤ C)
    (f : Lp ℂ 2 μ) :
    ‖linfty_mul_L2_CLM g hg_meas C hC hg_bound f‖ ≤ C * ‖f‖ := by
  have eq : linfty_mul_L2_CLM g hg_meas C hC hg_bound f = (MemLp.mul (p:=∞) (q:=2) (r:=2) (Lp.memLp f) (memLp_top_of_bound hg_meas.aestronglyMeasurable C hg_bound)).toLp (g * ⇑f) := rfl
  rw [eq, Lp.norm_toLp]
  apply ENNReal.toReal_le_of_le_ofReal (by positivity)
  refine (linfty_mul_L2_bound_aux g hg_meas C hC hg_bound f).trans ?_
  rw [ENNReal.ofReal_mul (le_of_lt hC)]
  gcongr
  exact le_of_eq (ENNReal.ofReal_toReal (Lp.memLp f).eLpNorm_ne_top).symm

/-! ## Local Integrability of Power-Law Decay Functions

Functions with polynomial decay are locally integrable in finite dimensions.
-/

open Set Metric in
/-- Local version of `integrable_fun_norm_addHaar`: integrability of radial functions on balls.
    If the radial part is integrable on (0, r), then the function is integrable on ball 0 r.

    Key technique: Use indicator functions to reduce to the global `integrable_fun_norm_addHaar`.
    - Define g := indicator (Iio r) f, so g(y) = f(y) for y < r, else 0
    - Then indicator (ball 0 r) (f ∘ ‖·‖) = g ∘ ‖·‖
    - Apply global lemma to g -/
lemma integrableOn_ball_of_radial {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    {f : ℝ → F} {r : ℝ} (_hr : 0 < r)
    (hint : IntegrableOn (fun y => y ^ (Module.finrank ℝ E - 1) • f y) (Ioo 0 r) volume) :
    IntegrableOn (fun x : E => f ‖x‖) (ball (0 : E) r) μ := by
  -- Key: indicator (ball 0 r) (f ∘ ‖·‖) = (indicator (Iio r) f) ∘ ‖·‖
  have h_eq : indicator (ball (0 : E) r) (fun x : E => f ‖x‖) =
      fun x : E => indicator (Iio r) f ‖x‖ := by
    ext x
    simp only [indicator, mem_ball_zero_iff, mem_Iio]
  -- IntegrableOn ↔ Integrable of indicator
  rw [← integrable_indicator_iff measurableSet_ball, h_eq]
  -- Now apply the global lemma integrable_fun_norm_addHaar
  rw [integrable_fun_norm_addHaar μ (f := indicator (Iio r) f)]
  -- The RHS is IntegrableOn (y^(d-1) • (indicator (Iio r) f) y) (Ioi 0)
  -- Since indicator (Iio r) f = 0 on [r, ∞), this equals IntegrableOn (y^(d-1) • f y) (Ioo 0 r)
  have h_supp : ∀ y ∈ Ioi (0 : ℝ), y ^ (Module.finrank ℝ E - 1) • indicator (Iio r) f y =
      indicator (Ioo 0 r) (fun y => y ^ (Module.finrank ℝ E - 1) • f y) y := by
    intro y hy
    simp only [indicator, mem_Ioo, mem_Iio, mem_Ioi] at hy ⊢
    by_cases hyr : y < r
    · simp only [hyr, hy, and_self, ↓reduceIte]
    · simp only [hyr, hy, and_false, ↓reduceIte, smul_zero]
  rw [integrableOn_congr_fun h_supp measurableSet_Ioi]
  -- IntegrableOn (indicator (Ioo 0 r) g) (Ioi 0) ← IntegrableOn g (Ioo 0 r) since Ioo 0 r ⊆ Ioi 0
  have : Integrable (indicator (Ioo 0 r) (fun y => y ^ (Module.finrank ℝ E - 1) • f y)) volume :=
    hint.integrable_indicator measurableSet_Ioo
  exact this.integrableOn

open Set Metric in
/-- Integrability on balls for power-law decay functions.
    If |f(x)| ≤ C‖x‖^{-α} with α < d, then f is integrable on any ball centered at 0. -/
lemma integrableOn_ball_of_rpow_decay {d : ℕ} (hd : d ≥ 1)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} {C α r : ℝ}
    (_hC : 0 < C) (hα : α < d) (hr : 0 < r)
    (h_decay : ∀ x, |f x| ≤ C * ‖x‖ ^ (-α))
    (h_meas : AEStronglyMeasurable f volume) :
    IntegrableOn f (ball (0 : EuclideanSpace ℝ (Fin d)) r) volume := by
  haveI : Nontrivial (EuclideanSpace ℝ (Fin d)) := by
    haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    infer_instance
  -- We apply integrableOn_ball_of_radial with the bound function g(y) = C * y^(-α)
  -- The radial integral becomes ∫_0^r y^(d-1) * C * y^(-α) dy = C * ∫_0^r y^(d-1-α) dy
  -- which converges when d-1-α > -1, i.e., α < d

  -- First show the bound function is radially integrable
  have hint : IntegrableOn (fun y => y ^ (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) - 1) • (C * y ^ (-α)))
      (Ioo 0 r) volume := by
    have hfinrank : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := by simp
    simp only [hfinrank, smul_eq_mul]
    -- Simplify y^(d-1) * (C * y^(-α)) = C * y^(d-1-α)
    have h_simp : ∀ y ∈ Ioo (0 : ℝ) r, (y : ℝ) ^ (d - 1) * (C * y ^ (-α)) = C * y ^ ((d : ℝ) - 1 - α) := by
      intro y hy
      have hy_pos : 0 < y := hy.1
      rw [mul_comm (y ^ _), mul_assoc]
      congr 1
      rw [← Real.rpow_natCast y (d - 1), ← Real.rpow_add hy_pos]
      congr 1
      simp only [Nat.cast_sub hd]
      ring
    rw [integrableOn_congr_fun h_simp measurableSet_Ioo]
    -- Now show IntegrableOn (C * y^(d-1-α)) (Ioo 0 r)
    -- First show the rpow part is integrable
    have h_rpow : IntegrableOn (fun y => y ^ ((d : ℝ) - 1 - α)) (Ioo 0 r) volume := by
      rw [intervalIntegral.integrableOn_Ioo_rpow_iff hr]
      linarith
    exact h_rpow.const_mul C

  -- Now use integrableOn_ball_of_radial and monotonicity
  have h_bound := integrableOn_ball_of_radial volume hr hint
  -- h_bound : IntegrableOn (fun x => C * ‖x‖^(-α)) (ball 0 r) volume

  -- Show f is dominated by the bound
  apply Integrable.mono' h_bound h_meas.restrict
  filter_upwards with x
  simp only [Real.norm_eq_abs]
  exact h_decay x

/-- Integrability away from the origin for bounded functions on compact sets. -/
lemma integrableOn_compact_diff_ball {d : ℕ}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} {C α δ : ℝ} {K : Set (EuclideanSpace ℝ (Fin d))}
    (hK : IsCompact K) (hC : 0 < C) (hδ : 0 < δ)
    (h_decay : ∀ x, |f x| ≤ C * ‖x‖ ^ (-α))
    (h_meas : AEStronglyMeasurable f volume) :
    IntegrableOn f (K \ Metric.ball 0 δ) volume := by
  -- On K \ ball 0 δ, ‖x‖ ≥ δ > 0 so the bound C * ‖x‖^(-α) is bounded
  have h_finite : volume (K \ Metric.ball 0 δ) < ⊤ :=
    (hK.diff Metric.isOpen_ball).measure_lt_top
  by_cases hne : (K \ Metric.ball 0 δ).Nonempty
  · -- The set is nonempty
    obtain ⟨R, hR_pos, hR⟩ := hK.isBounded.exists_pos_norm_le
    -- On K \ ball 0 δ, we have δ ≤ ‖x‖ ≤ R, so ‖x‖^(-α) is bounded
    -- Use M = C * max (δ^(-α)) (R^(-α)) as bound (handles both signs of α)
    let M := C * max (δ ^ (-α)) (R ^ (-α))
    have hM_pos : 0 < M := by positivity
    have h_bound : ∀ x ∈ K \ Metric.ball 0 δ, |f x| ≤ M := by
      intro x hx
      have hx_in_K : x ∈ K := hx.1
      have hx_norm_lower : δ ≤ ‖x‖ := by
        simp only [Set.mem_diff, Metric.mem_ball, dist_zero_right, not_lt] at hx
        exact hx.2
      have hx_norm_upper : ‖x‖ ≤ R := hR x hx_in_K
      have hx_norm_pos : 0 < ‖x‖ := hδ.trans_le hx_norm_lower
      calc |f x| ≤ C * ‖x‖ ^ (-α) := h_decay x
        _ ≤ M := by
          show C * ‖x‖ ^ (-α) ≤ C * max (δ ^ (-α)) (R ^ (-α))
          apply mul_le_mul_of_nonneg_left _ (le_of_lt hC)
          by_cases hα_nonneg : 0 ≤ α
          · -- α ≥ 0: -α ≤ 0, so rpow is antitone, ‖x‖^(-α) ≤ δ^(-α)
            have h1 : ‖x‖ ^ (-α) ≤ δ ^ (-α) := by
              apply (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (neg_nonpos.mpr hα_nonneg))
              · exact hδ
              · exact hx_norm_pos
              · exact hx_norm_lower
            exact le_max_of_le_left h1
          · -- α < 0: -α > 0, so rpow is monotone, ‖x‖^(-α) ≤ R^(-α)
            push_neg at hα_nonneg
            have h1 : ‖x‖ ^ (-α) ≤ R ^ (-α) := by
              apply Real.rpow_le_rpow (le_of_lt hx_norm_pos) hx_norm_upper
              linarith
            exact le_max_of_le_right h1
    have hM_bound : ∀ x ∈ K \ Metric.ball 0 δ, ‖f x‖ ≤ M := fun x hx => by
      rw [Real.norm_eq_abs]
      exact h_bound x hx
    have h_const : IntegrableOn (fun _ => M) (K \ Metric.ball 0 δ) volume :=
      MeasureTheory.integrableOn_const (μ := volume) (s := K \ Metric.ball 0 δ)
        (by exact ne_top_of_lt h_finite)
    have h_ae : ∀ᵐ x ∂(volume.restrict (K \ Metric.ball 0 δ)), ‖f x‖ ≤ M := by
      rw [ae_restrict_iff' (hK.diff Metric.isOpen_ball).measurableSet]
      exact ae_of_all _ hM_bound
    exact h_const.mono' h_meas.restrict h_ae
  · -- The set is empty
    rw [Set.not_nonempty_iff_eq_empty.mp hne]
    exact integrableOn_empty

/-- Functions with polynomial decay are locally integrable.
    For d-dimensional space, if α < d and |f(x)| ≤ C‖x‖^{-α}, then f is locally integrable. -/
theorem locallyIntegrable_of_rpow_decay_real {d : ℕ} (hd : d ≥ 3)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} {C : ℝ} {α : ℝ}
    (hC : C > 0) (hα : α < d)
    (h_decay : ∀ x, |f x| ≤ C * ‖x‖ ^ (-α))
    (h_meas : AEStronglyMeasurable f volume) :
    LocallyIntegrable f volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  -- Cover K with ball 0 1 and K \ ball 0 (1/2)
  have h_cover : K ⊆ (K ∩ Metric.ball 0 1) ∪ (K \ Metric.ball 0 (1/2)) := by
    intro x hx
    by_cases hxb : x ∈ Metric.ball 0 1
    · exact Or.inl ⟨hx, hxb⟩
    · simp only [Metric.mem_ball, dist_zero_right, not_lt] at hxb
      right
      constructor
      · exact hx
      · simp only [Metric.mem_ball, dist_zero_right, not_lt]
        linarith
  apply IntegrableOn.mono_set _ h_cover
  apply IntegrableOn.union
  · -- IntegrableOn f (K ∩ ball 0 1)
    apply IntegrableOn.mono_set _ Set.inter_subset_right
    exact integrableOn_ball_of_rpow_decay (by omega : d ≥ 1) hC hα (by norm_num : (0:ℝ) < 1)
      h_decay h_meas
  · -- IntegrableOn f (K \ ball 0 (1/2))
    exact integrableOn_compact_diff_ball hK hC (by norm_num : (0:ℝ) < 1/2) h_decay h_meas

/-- **Polynomial decay is integrable in 3D**: The function 1/(1+‖x‖)^4 is integrable
    over SpatialCoords = EuclideanSpace ℝ (Fin 3).

    This is a standard result: decay rate 4 > dimension 3 ensures integrability.

    **Mathematical content**: In ℝ³ with spherical coordinates,
    ∫ 1/(1+r)^4 · r² dr dΩ = 4π ∫₀^∞ r²/(1+r)^4 dr < ∞
    since the integrand decays as r⁻² for large r.

    **Used by**: `spatialNormIntegral_linear_bound` and `F_norm_bound_via_linear_vanishing`
    to show that spatial integrals of Schwartz functions with linear time vanishing
    are bounded by C·t. -/
lemma polynomial_decay_integrable_3d :
    Integrable (fun x : EuclideanSpace ℝ (Fin 3) => 1 / (1 + ‖x‖)^4) volume := by
  -- Use integrable_one_add_norm: (1 + ‖x‖)^(-r) is integrable when r > dim
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := finrank_euclideanSpace
  have hdim_lt : (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) : ℝ) < (4 : ℝ) := by
    rw [hdim]; norm_num
  have h_int := integrable_one_add_norm (E := EuclideanSpace ℝ (Fin 3)) (μ := volume) (r := 4) hdim_lt
  -- Convert (1 + ‖x‖)^(-4) to 1 / (1 + ‖x‖)^4
  convert h_int using 1
  ext x
  have h_pos : 0 < 1 + ‖x‖ := by linarith [norm_nonneg x]
  simp only [Real.rpow_neg (le_of_lt h_pos), one_div]
  congr 1
  exact (Real.rpow_natCast (1 + ‖x‖) 4).symm

/-! ## Bilinear Integrability for L¹ Translation-Invariant Kernels

For translation-invariant kernels K₀ that are integrable (L¹), the bilinear form
f(x) K₀(x-y) g(y) with Schwartz test functions f, g is integrable on E × E.

This applies to exponentially decaying kernels like the massive free covariance.
-/

/-- For translation-invariant kernels K₀ that are **integrable** (L¹), the bilinear form
    with Schwartz test functions is integrable. This is the easiest case and applies to
    exponentially decaying kernels like the massive free covariance.

    Proof idea:
    - Schwartz functions are bounded: ‖f‖_∞ < ∞ (via toBoundedContinuousFunction)
    - Schwartz functions are integrable: ‖g‖_{L¹} < ∞
    - K₀ is integrable: ‖K₀‖_{L¹} < ∞
    - Then: ∫∫ |f(x) K₀(x-y) g(y)| dx dy ≤ ‖f‖_∞ · ‖K₀‖_{L¹} · ‖g‖_{L¹} < ∞ -/
theorem schwartz_bilinear_integrable_of_translationInvariant_L1
    {d : ℕ}
    (K₀ : EuclideanSpace ℝ (Fin d) → ℂ)
    (hK₀_int : Integrable K₀ volume)
    (f g : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ) :
    Integrable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      f p.1 * K₀ (p.1 - p.2) * g p.2) volume := by
  -- Get boundedness of f: Schwartz functions are bounded continuous
  have hf_bdd : ∃ Cf, ∀ x, ‖f x‖ ≤ Cf := by
    use ‖f.toBoundedContinuousFunction‖
    intro x
    exact BoundedContinuousFunction.norm_coe_le_norm f.toBoundedContinuousFunction x
  obtain ⟨Cf, hCf⟩ := hf_bdd

  -- Get integrability of g (Schwartz functions are integrable)
  have hg_int : Integrable g volume := g.integrable

  -- The dominating function: Cf * |K₀(x-y)| * |g(y)|
  let bound : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ :=
    fun p => Cf * ‖K₀ (p.1 - p.2)‖ * ‖g p.2‖

  -- Use Integrable.mono' with the bound
  apply Integrable.mono'
  · -- Show the bound is integrable
    -- Key: ∫∫ |K₀(x-y)| |g(y)| dx dy = ‖K₀‖_{L¹} · ‖g‖_{L¹} (by Fubini + translation invariance)
    -- Get integrability of norms
    have hK_norm_int : Integrable (fun z => ‖K₀ z‖) volume := Integrable.norm hK₀_int
    have hg_norm_int : Integrable (fun y => ‖g y‖) volume := Integrable.norm hg_int
    -- Product of integrable real functions is integrable on product space
    have hprod : Integrable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
        ‖K₀ p.1‖ * ‖g p.2‖) (volume.prod volume) := Integrable.mul_prod hK_norm_int hg_norm_int
    -- Change of variables: (z, y) ↦ (z + y, y) = (x, y), so z = x - y
    -- Use the MeasurableEquiv for (x, y) ↦ (x - y, y)
    let e : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ≃ᵐ
        EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) :=
      { toFun := fun p => (p.1 - p.2, p.2)
        invFun := fun p => (p.1 + p.2, p.2)
        left_inv := fun p => by simp [sub_add_cancel]
        right_inv := fun p => by simp [add_sub_cancel_right]
        measurable_toFun := Measurable.prodMk (measurable_fst.sub measurable_snd) measurable_snd
        measurable_invFun := Measurable.prodMk (measurable_fst.add measurable_snd) measurable_snd }
    -- The map preserves measure (translation invariance of Lebesgue measure)
    have he_preserves : MeasurePreserving e (volume.prod volume) (volume.prod volume) := by
      -- Use measurePreserving_sub_prod: (x, y) ↦ (x - y, y) preserves measure
      have := measurePreserving_sub_prod (G := EuclideanSpace ℝ (Fin d)) volume volume
      convert this using 1
    have hchange : Integrable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
        ‖K₀ (p.1 - p.2)‖ * ‖g p.2‖) (volume.prod volume) := by
      -- We have hprod : Integrable (fun p => ‖K₀ p.1‖ * ‖g p.2‖)
      -- We want: Integrable (fun p => ‖K₀ (p.1 - p.2)‖ * ‖g p.2‖)
      -- These are related by: (fun p => ‖K₀ p.1‖ * ‖g p.2‖) ∘ e = (fun p => ‖K₀ (p.1 - p.2)‖ * ‖g p.2‖)
      -- where e(p) = (p.1 - p.2, p.2)
      -- Use integrable_comp_emb: (Integrable g μb ↔ Integrable (g ∘ f) μa) for MeasurePreserving f
      have heq : (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
          ‖K₀ (p.1 - p.2)‖ * ‖g p.2‖) = (fun p => ‖K₀ p.1‖ * ‖g p.2‖) ∘ e := by
        ext p
        rfl
      rw [heq, he_preserves.integrable_comp_emb e.measurableEmbedding]
      exact hprod
    -- Multiply by constant Cf
    exact hchange.const_mul Cf

  · -- AEStronglyMeasurable of the integrand
    apply AEStronglyMeasurable.mul
    apply AEStronglyMeasurable.mul
    · exact f.continuous.aestronglyMeasurable.comp_measurable measurable_fst
    · -- K₀ is AEStronglyMeasurable on volume, need it on product
      -- Use that the shear map (x,y) ↦ (x-y, y) is measure-preserving
      have hK_ae : AEStronglyMeasurable K₀ volume := hK₀_int.1
      -- K₀ ∘ fst is AEStronglyMeasurable on volume.prod volume
      have hK_fst : AEStronglyMeasurable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
          K₀ p.1) (volume.prod volume) := hK_ae.comp_fst
      -- The shear map e(x,y) = (x-y, y) is measure-preserving
      have he_sub_preserves : MeasurePreserving
          (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => (p.1 - p.2, p.2))
          (volume.prod volume) (volume.prod volume) := by
        have := measurePreserving_sub_prod (G := EuclideanSpace ℝ (Fin d)) volume volume
        convert this using 1
      -- Composition: K₀ ∘ fst ∘ e = fun p => K₀ (p.1 - p.2)
      have heq : (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => K₀ (p.1 - p.2)) =
          (fun p => K₀ p.1) ∘ (fun p => (p.1 - p.2, p.2)) := by
        ext p; simp only [Function.comp_apply]
      rw [heq]
      exact hK_fst.comp_measurePreserving he_sub_preserves
    · exact g.continuous.aestronglyMeasurable.comp_measurable measurable_snd

  · -- Pointwise bound: ‖f(x) K₀(x-y) g(y)‖ ≤ Cf * ‖K₀(x-y)‖ * ‖g(y)‖
    filter_upwards with p
    rw [norm_mul, norm_mul]
    calc ‖f p.1‖ * ‖K₀ (p.1 - p.2)‖ * ‖g p.2‖
        ≤ Cf * ‖K₀ (p.1 - p.2)‖ * ‖g p.2‖ := by
          have h := hCf p.1
          have h1 : 0 ≤ ‖K₀ (p.1 - p.2)‖ := norm_nonneg _
          have h2 : 0 ≤ ‖g p.2‖ := norm_nonneg _
          have h12 : 0 ≤ ‖K₀ (p.1 - p.2)‖ * ‖g p.2‖ := mul_nonneg h1 h2
          calc ‖f p.1‖ * ‖K₀ (p.1 - p.2)‖ * ‖g p.2‖
              = ‖f p.1‖ * (‖K₀ (p.1 - p.2)‖ * ‖g p.2‖) := by ring
            _ ≤ Cf * (‖K₀ (p.1 - p.2)‖ * ‖g p.2‖) := mul_le_mul_of_nonneg_right h h12
            _ = Cf * ‖K₀ (p.1 - p.2)‖ * ‖g p.2‖ := by ring
      _ = Cf * (‖K₀ (p.1 - p.2)‖ * ‖g p.2‖) := by ring

/-! ## Schwartz Functions Times Bounded Functions

These lemmas establish integrability of Schwartz functions multiplied by bounded
measurable functions, which is essential for Fourier transform computations.
-/

section SchwartzBounded

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] {μ : Measure E} [μ.HasTemperateGrowth]

/-- A Schwartz function times a bounded measurable function is integrable.
    This is the key technical lemma for Fourier-type integrals. -/
lemma SchwartzMap.integrable_mul_bounded (f : SchwartzMap E ℂ) (g : E → ℂ)
    (hg_meas : Measurable g) (hg_bdd : ∀ x, ‖g x‖ ≤ 1) :
    Integrable (fun x => f x * g x) μ := by
  have hf_int : Integrable f μ := f.integrable
  -- Use bdd_mul: Integrable f → AEStronglyMeasurable g → (∀ᵐ x, ‖g x‖ ≤ C) → Integrable (g * f)
  -- Then convert by commutativity
  have hg_ae : AEStronglyMeasurable g μ := hg_meas.aestronglyMeasurable
  have hg_ae_bdd : ∀ᵐ x ∂μ, ‖g x‖ ≤ 1 := Filter.Eventually.of_forall hg_bdd
  exact Integrable.mul_bdd hf_int hg_ae hg_ae_bdd

/-- The conjugate of a Schwartz function is integrable. -/
lemma SchwartzMap.integrable_conj (f : SchwartzMap E ℂ) :
    Integrable (fun y => starRingEnd ℂ (f y)) μ := by
  have hf_int : Integrable f μ := f.integrable
  have hf_star_meas : AEStronglyMeasurable (fun y => starRingEnd ℂ (f y)) μ :=
    hf_int.aestronglyMeasurable.star
  have h_norm_eq : ∀ᵐ y ∂μ, ‖f y‖ = ‖starRingEnd ℂ (f y)‖ := by
    filter_upwards with y
    exact (RCLike.norm_conj (f y)).symm
  exact hf_int.congr' hf_star_meas h_norm_eq

end SchwartzBounded

/-! ## Phase Exponential Lemmas

Lemmas about complex exponentials of pure imaginary arguments, used in Fourier analysis.
-/

/-- Complex exponential of pure imaginary argument has norm 1. -/
lemma norm_exp_I_mul_real (r : ℝ) : ‖Complex.exp (Complex.I * r)‖ = 1 :=
  norm_exp_I_mul_ofReal r

/-- Complex exponential of negative pure imaginary argument has norm 1. -/
lemma norm_exp_neg_I_mul_real (r : ℝ) : ‖Complex.exp (-Complex.I * r)‖ = 1 := by
  rw [Complex.norm_exp]
  simp only [neg_mul, Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re,
    zero_mul, Complex.I_im, Complex.ofReal_im, mul_zero, sub_zero, neg_zero, Real.exp_zero]

/-! ## Linear Vanishing Bound for Schwartz Functions

If a Schwartz function on ℝ × E vanishes for t ≤ 0, then it grows at most linearly in t.
This is a key lemma for UV regularization in QFT integrals.
-/

namespace SchwartzLinearBound

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The Linear Vanishing Bound (general version).
    If f : 𝓢(ℝ × E, ℂ) vanishes for t ≤ 0, it grows at most linearly in t for t > 0.

    This follows from the Mean Value Theorem: f(t,x) - f(0,x) = ∫₀ᵗ ∂ₜf dt,
    and since ∂ₜf is bounded (Schwartz), we get |f(t,x)| ≤ C·t.
-/
theorem schwartz_vanishing_linear_bound_general
    (f : SchwartzMap (ℝ × E) ℂ)
    (h_vanish : ∀ t x, t ≤ 0 → f (t, x) = 0) :
    ∃ C, ∀ t ≥ 0, ∀ x, ‖f (t, x)‖ ≤ C * t := by

  -- 1. Get a bound on the Fréchet derivative using Schwartz seminorms
  have h_diff : Differentiable ℝ f := f.differentiable

  -- Use the first order seminorm to bound the derivative
  let C_deriv := (SchwartzMap.seminorm ℝ 0 1).toFun f + 1

  have h_deriv_bound : ∀ y : ℝ × E, ‖iteratedFDeriv ℝ 1 f y‖ ≤ C_deriv := by
    intro y
    have h := SchwartzMap.le_seminorm ℝ 0 1 f y
    simp only [pow_zero, one_mul] at h
    calc ‖iteratedFDeriv ℝ 1 (⇑f) y‖ ≤ (SchwartzMap.seminorm ℝ 0 1) f := h
      _ ≤ (SchwartzMap.seminorm ℝ 0 1) f + 1 := by linarith
      _ = C_deriv := rfl

  -- The convex set (whole space)
  have h_convex : Convex ℝ (Set.univ : Set (ℝ × E)) := convex_univ

  -- Schwartz functions have FDeriv everywhere
  have h_hasFDeriv : ∀ y ∈ (Set.univ : Set (ℝ × E)),
      HasFDerivWithinAt f (fderiv ℝ f y) Set.univ y := by
    intro y _
    exact f.differentiableAt.hasFDerivAt.hasFDerivWithinAt

  -- Connection: ‖fderiv ℝ f y‖ = ‖iteratedFDeriv ℝ 1 f y‖
  have h_fderiv_bound : ∀ y ∈ (Set.univ : Set (ℝ × E)), ‖fderiv ℝ f y‖ ≤ C_deriv := by
    intro y _
    have h_norm_eq : ‖iteratedFDeriv ℝ 1 f y‖ = ‖fderiv ℝ f y‖ := by
      rw [← iteratedFDerivWithin_univ, ← fderivWithin_univ]
      exact norm_iteratedFDerivWithin_one f uniqueDiffWithinAt_univ
    linarith [h_deriv_bound y]

  use C_deriv
  intro t ht x

  -- 2. The reference point: (0, x) where f vanishes
  let A : ℝ × E := (0, x)
  let B : ℝ × E := (t, x)

  -- f vanishes at A = (0, x)
  have h_zero : f A = 0 := h_vanish 0 x (le_refl 0)

  -- Handle the t = 0 case separately
  by_cases ht0 : t = 0
  · simp [ht0, h_zero, A]

  -- For t > 0, apply MVT
  have ht_pos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)

  -- Apply the Mean Value Theorem
  have h_mvt := h_convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    h_hasFDeriv h_fderiv_bound (Set.mem_univ A) (Set.mem_univ B)

  -- Simplify: f A = 0, so ‖f B‖ ≤ C_deriv * ‖B - A‖
  rw [h_zero, sub_zero] at h_mvt

  -- Compute ‖B - A‖ = ‖(t, x) - (0, x)‖ = ‖(t, 0)‖ = |t| = t
  have h_dist : ‖B - A‖ = t := by
    simp only [B, A, Prod.mk_sub_mk, sub_zero]
    rw [Prod.norm_def]
    simp only [_root_.sub_self, norm_zero, max_eq_left (norm_nonneg t)]
    rw [Real.norm_eq_abs, abs_of_nonneg ht]

  rw [h_dist] at h_mvt
  exact h_mvt

end SchwartzLinearBound

/-! ### Schwartz Translation Invariance

Translation by a constant vector preserves Schwartz class. This is a fundamental
fact in harmonic analysis: if f ∈ 𝒮(ℝⁿ), then f(· - a) ∈ 𝒮(ℝⁿ) for any a ∈ ℝⁿ.

**Mathematical proof:**
1. Smoothness: f(x - a) is C∞ if f is (composition with smooth translation)
2. Decay: ‖x‖^k |D^n f(x-a)| ≤ C' follows from ‖y‖^m |D^n f(y)| ≤ C for y = x - a
   using the triangle inequality ‖x‖ ≤ ‖x-a‖ + ‖a‖ and taking m large enough

**Reference:** Stein-Weiss, "Fourier Analysis", Chapter 1; any Schwartz space text
-/

/-- Translation `x ↦ x - a` has temperate growth. -/
lemma sub_const_hasTemperateGrowth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (a : E) :
    Function.HasTemperateGrowth (fun x : E => x - a) := by fun_prop

/-- Translation `x ↦ x - a` is antilipschitz (actually an isometry). -/
lemma sub_const_antilipschitz {E : Type*} [NormedAddCommGroup E] (a : E) :
    AntilipschitzWith 1 (fun x : E => x - a) := by
  intro x y
  simp [edist_dist, dist_eq_norm]

/-- **Schwartz functions are invariant under translation.**
    For f ∈ 𝒮(E, F) and a ∈ E, the translated function f(· - a) is also in 𝒮(E, F).

    This is proved using Mathlib's `compCLMOfAntilipschitz`: translation is composition
    with `x ↦ x - a`, which has temperate growth and is antilipschitz (an isometry). -/
noncomputable def SchwartzMap.translate {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : SchwartzMap E F) (a : E) : SchwartzMap E F :=
  SchwartzMap.compCLMOfAntilipschitz ℝ (sub_const_hasTemperateGrowth a) (sub_const_antilipschitz a) f

@[simp]
theorem SchwartzMap.translate_apply {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : SchwartzMap E F) (a x : E) :
    f.translate a x = f (x - a) := rfl

/-! ### Schwartz Integrable Decay

Schwartz functions decay faster than any polynomial inverse.
This justifies integrability conditions.
-/

section SchwartzDecay
open Real

/-- **Schwartz L¹ bound**: Schwartz functions are integrable with explicit decay.
    For f ∈ 𝓢(ℝⁿ), we have ∫ |f(x)| dx < ∞.

    More precisely, for any N, there exists C such that
    |f(x)| ≤ C / (1 + |x|)^N. If N > dim(V), this implies integrability.

    **Reference**: Stein-Weiss, Chapter 1, Proposition 1.1 -/
theorem schwartz_integrable_decay {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasureSpace V] [BorelSpace V]
    (f : SchwartzMap V ℂ) (N : ℕ) (_hN : Module.finrank ℝ V < N) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : V, ‖f x‖ ≤ C / (1 + ‖x‖)^N := by
  -- Get bounds for each k ≤ N
  have h_decay : ∀ k, ∃ C_k > 0, ∀ x, ‖x‖^k * ‖iteratedFDeriv ℝ 0 f x‖ ≤ C_k := fun k => SchwartzMap.decay f k 0
  choose C hC_pos hC using h_decay

  let total_C := Finset.sum (Finset.range (N + 1)) (fun k => (N.choose k : ℝ) * C k)

  use total_C
  constructor
  · apply Finset.sum_pos
    · intro k hk
      apply _root_.mul_pos
      · exact Nat.cast_pos.mpr (Nat.choose_pos (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))
      · exact hC_pos k
    · use 0; simp
  · intro x
    rw [div_eq_mul_inv, le_mul_inv_iff₀ (pow_pos (by linarith [norm_nonneg x]) _)]

    -- Expand (1 + ‖x‖)^N
    have h_binom : (1 + ‖x‖)^N = Finset.sum (Finset.range (N + 1)) (fun k => (N.choose k : ℝ) * ‖x‖^k) := by
      rw [add_comm, add_pow]
      simp only [one_pow, mul_one]
      congr; ext k
      rw [mul_comm]
    rw [h_binom]

    -- Move norm inside
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk

    -- Use the bound for each term
    -- We need to know ‖iteratedFDeriv ℝ 0 f x‖ = ‖f x‖
    have h_norm : ‖iteratedFDeriv ℝ 0 f x‖ = ‖f x‖ := by
       rw [norm_iteratedFDeriv_zero]

    -- Rearrange to match hC
    have h_rearrange : ‖f x‖ * ((N.choose k : ℝ) * ‖x‖^k) = (N.choose k : ℝ) * (‖x‖^k * ‖iteratedFDeriv ℝ 0 f x‖) := by
       rw [h_norm]
       ring
    rw [h_rearrange]

    apply mul_le_mul_of_nonneg_left (hC k x) (Nat.cast_nonneg _)

end SchwartzDecay

/-! ## Double Mollifier Convergence

This section proves the double mollifier convergence theorem: for a continuous
kernel C (away from the origin), the double convolution with mollifiers converges
to the kernel value at separated points:

  ∫∫ φ_ε(x-a) C(x-y) φ_ε(y) dx dy → C(a) as ε → 0

The key insight is that the self-convolution φ ⋆ φ is itself an approximate identity,
so by associativity we reduce to a single convolution limit.
-/

section DoubleMollifierConvergence

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NoAtoms (volume : Measure E)]

open MeasureTheory Filter Convolution Set Function Topology
open scoped Pointwise BigOperators

variable {E}

/-- The self-convolution of a normalized bump function. -/
noncomputable def bumpSelfConv (φ : ContDiffBump (0 : E)) : E → ℝ :=
  (φ.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (φ.normed volume)

set_option linter.unusedSectionVars false in
/-- Self-convolution is nonnegative. -/
lemma bumpSelfConv_nonneg (φ : ContDiffBump (0 : E)) (x : E) : 0 ≤ bumpSelfConv φ x := by
  unfold bumpSelfConv convolution
  apply integral_nonneg
  intro y
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  exact mul_nonneg (φ.nonneg_normed _) (φ.nonneg_normed _)

set_option linter.unusedSectionVars false in
/-- Self-convolution has mass 1: ∫(φ ⋆ φ) = (∫φ)(∫φ) = 1·1 = 1. -/
lemma bumpSelfConv_integral (φ : ContDiffBump (0 : E)) :
    ∫ x, bumpSelfConv φ x = 1 := by
  unfold bumpSelfConv
  rw [integral_convolution (L := ContinuousLinearMap.lsmul ℝ ℝ)]
  · simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    have h1 := φ.integral_normed (μ := volume)
    simp only [h1]
    norm_num
  · exact φ.integrable_normed
  · exact φ.integrable_normed

set_option linter.unusedSectionVars false in
/-- Support of self-convolution is contained in ball of radius 2*rOut. -/
lemma bumpSelfConv_support_subset (φ : ContDiffBump (0 : E)) :
    support (bumpSelfConv φ) ⊆ Metric.ball 0 (2 * φ.rOut) := by
  unfold bumpSelfConv
  intro x hx
  have hsub : support (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] φ.normed volume) ⊆
      support (φ.normed volume) + support (φ.normed volume) :=
    support_convolution_subset (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume)
  have hx' := hsub hx
  rw [Set.mem_add] at hx'
  obtain ⟨y, hy, z, hz, hyz⟩ := hx'
  have hy_ball : y ∈ Metric.ball (0 : E) φ.rOut := by
    have := φ.support_normed_eq (μ := volume)
    rw [this] at hy
    exact hy
  have hz_ball : z ∈ Metric.ball (0 : E) φ.rOut := by
    have := φ.support_normed_eq (μ := volume)
    rw [this] at hz
    exact hz
  rw [Metric.mem_ball] at hy_ball hz_ball ⊢
  rw [dist_zero_right] at hy_ball hz_ball ⊢
  rw [← hyz]
  calc ‖y + z‖ ≤ ‖y‖ + ‖z‖ := norm_add_le y z
    _ < φ.rOut + φ.rOut := add_lt_add hy_ball hz_ball
    _ = 2 * φ.rOut := by ring

/-- Self-convolution support shrinks to {0} as rOut → 0. -/
lemma bumpSelfConv_support_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    (φ : ι → ContDiffBump (0 : E)) (hφ : Tendsto (fun i => (φ i).rOut) l (nhds 0)) :
    Tendsto (fun i => support (bumpSelfConv (φ i))) l (𝓝 (0 : E)).smallSets := by
  rw [tendsto_smallSets_iff]
  intro s hs
  rw [Metric.mem_nhds_iff] at hs
  obtain ⟨ε, hε, hs⟩ := hs
  have h := hφ.eventually (Iio_mem_nhds (half_pos hε))
  filter_upwards [h] with i hi
  intro x hx
  apply hs
  have hsub := bumpSelfConv_support_subset (φ i)
  have hx_ball := hsub hx
  rw [Metric.mem_ball, dist_zero_right] at hx_ball ⊢
  calc ‖x‖ < 2 * (φ i).rOut := hx_ball
    _ < 2 * (ε / 2) := by
        apply mul_lt_mul_of_pos_left hi
        norm_num
    _ = ε := by ring

/-- **Main theorem: Double mollifier convergence via associativity.**

    For C continuous on {x ≠ 0}, the double mollifier integral converges:
    ∫∫ φ_ε(x-a) C(x-y) φ_ε(y) dx dy → C(a) as ε → 0

    **Proof strategy:**
    1. Recognize that ψ := φ ⋆ φ (self-convolution) is an approximate identity:
       - Nonnegative (integral of product of nonneg functions)
       - Mass 1: ∫ψ = (∫φ)² = 1
       - Shrinking support: supp(ψ) ⊆ B(0, 2·rOut)
    2. By associativity: ∫∫ φ(x-a) C(x-y) φ(y) dx dy = (ψ ⋆ C)(a)
    3. Apply single-convolution theorem: (ψ ⋆ C)(a) → C(a)
-/
theorem double_mollifier_convergence
    (C : E → ℝ)
    (hC : ContinuousOn C {x | x ≠ 0})
    (a : E) (ha : a ≠ 0)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (φ : ι → ContDiffBump (0 : E))
    (hφ : Tendsto (fun i => (φ i).rOut) l (nhds 0)) :
    Tendsto
      (fun i => ∫ x, ∫ y, (φ i).normed volume (x - a) * C (x - y) * (φ i).normed volume y)
      l (nhds (C a)) := by
  -- The self-convolution satisfies approximate identity conditions:
  -- 1. Nonnegative
  have hnonneg : ∀ᶠ i in l, ∀ x, 0 ≤ bumpSelfConv (φ i) x :=
    Eventually.of_forall (fun i => bumpSelfConv_nonneg (φ i))

  -- 2. Integral = 1
  have hintegral : ∀ᶠ i in l, ∫ x, bumpSelfConv (φ i) x = 1 :=
    Eventually.of_forall (fun i => bumpSelfConv_integral (φ i))

  -- 3. Support shrinks to 0
  have hsupport : Tendsto (fun i => support (bumpSelfConv (φ i))) l (𝓝 (0 : E)).smallSets :=
    bumpSelfConv_support_tendsto φ hφ

  -- C is continuous at a (since a ≠ 0)
  have hCa : ContinuousAt C a := hC.continuousAt (isOpen_ne.mem_nhds ha)

  -- Step 1: C is AE strongly measurable (continuous on open set)
  have hmC : AEStronglyMeasurable C volume := by
    have h_ae : ∀ᵐ (x : E) ∂volume, x ∈ {x : E | x ≠ 0} := by
      rw [ae_iff]
      simp only [mem_setOf_eq, not_not]
      have : ({x : E | x = 0} : Set E) = {0} := by ext; simp
      rw [this]
      exact measure_singleton 0
    have h_restrict : (volume : Measure E).restrict {x | x ≠ 0} = volume :=
      Measure.restrict_eq_self_of_ae_mem h_ae
    have h_meas : MeasurableSet {x : E | x ≠ 0} := isOpen_ne.measurableSet
    have h := hC.aestronglyMeasurable (μ := volume) h_meas
    rw [h_restrict] at h
    exact h

  -- Step 2: C converges to C(a) at a (since C is continuous at a)
  have hCconv : Tendsto (uncurry fun _ : ι => C) (l ×ˢ 𝓝 a) (𝓝 (C a)) := by
    have h : uncurry (fun _ : ι => C) = C ∘ Prod.snd := by
      ext ⟨i, x⟩
      simp [uncurry]
    rw [h]
    exact hCa.tendsto.comp (Filter.tendsto_snd (f := l) (g := 𝓝 a))

  -- Step 3: Apply convolution_tendsto_right with ψ = bumpSelfConv
  have h_selfconv_limit : Tendsto
      (fun i => (bumpSelfConv (φ i) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] C) a)
      l (𝓝 (C a)) := by
    apply convolution_tendsto_right hnonneg hintegral hsupport
    · filter_upwards with i; exact hmC
    · exact hCconv
    · exact tendsto_const_nhds

  -- Step 4: Show double integral equals (bumpSelfConv ⋆ C)(a)
  have h_eq : ∀ᶠ i in l,
      (∫ x, ∫ y, (φ i).normed volume (x - a) * C (x - y) * (φ i).normed volume y) =
      (bumpSelfConv (φ i) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] C) a := by
    have hr_pos : 0 < ‖a‖ / 3 := div_pos (norm_pos_iff.mpr ha) (by norm_num)
    filter_upwards [hφ (Metric.ball_mem_nhds 0 hr_pos)] with i hi
    let ψ := (φ i).normed volume

    -- 1. Identify inner integral as convolution
    have h_inner : ∀ x, ∫ y, C (x - y) * ψ y = (ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] C) x := by
      intro x
      rw [convolution_def]
      simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
      congr 1; ext y; ring

    -- 2. Rewrite LHS using inner convolution
    conv_lhs =>
      enter [2, x]
      conv =>
        enter [2, y]
        rw [mul_assoc]
      rw [MeasureTheory.integral_const_mul]
      rw [h_inner x]

    -- 3. Show equal to (ψ ⋆ (ψ ⋆ C))(a)
    have h_outer : (∫ x, ψ (x - a) * (ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] C) x) =
                   (ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] C)) a := by
      let g := ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] C
      rw [convolution_def]
      simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
      rw [← MeasureTheory.integral_add_right_eq_self (fun x => ψ (x - a) * g x) a]
      simp only [add_sub_cancel_right]
      rw [← MeasureTheory.integral_neg_eq_self]
      dsimp
      congr 1; ext x
      dsimp [ψ]
      rw [(φ i).normed_neg, add_comm (-x) a, sub_eq_add_neg]

    rw [h_outer]

    -- 4. Apply associativity manually to avoid global integrability issues
    let g := ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] C
    have h_assoc : (ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) a =
                   (bumpSelfConv (φ i) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] C) a := by
       simp only [bumpSelfConv, convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
       conv_rhs =>
         enter [2]
         ext t
         rw [← MeasureTheory.integral_mul_const]
       rw [MeasureTheory.integral_integral_swap]
       · -- Transformations to match LHS
         congr 1; ext v
         dsimp [g]
         rw [convolution_def]
         simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
         have h_eq : ∫ x, ψ v * ψ (x - v) * C (a - x) = ψ v * ∫ y, ψ y * C (a - v - y) := by
           rw [← MeasureTheory.integral_const_mul]
           have h_shift := @MeasureTheory.integral_sub_right_eq_self E ℝ _ _ _
             (volume : Measure E) _ _ _
             (fun y => ψ v * (ψ y * C (a - v - y))) v
           rw [← h_shift]
           congr 1
           ext x
           have : a - v - (x - v) = a - x := by abel
           simp only [this]
           ring
         rw [h_eq]
       · -- Prove integrability of F(t, v) = ψ v * ψ(t-v) * C(a-t)
         let F := fun (p : E × E) => ψ p.2 * ψ (p.1 - p.2) * C (a - p.1)
         let K_t := Metric.closedBall (0 : E) (2 * (φ i).rOut)
         let K_v := Metric.closedBall (0 : E) ((φ i).rOut)
         let K := K_t ×ˢ K_v
         have hK_compact : IsCompact K := IsCompact.prod (isCompact_closedBall 0 _) (isCompact_closedBall 0 _)

         -- Support is in K
         have h_supp_F : support F ⊆ K := by
           intro ⟨t, v⟩ h
           rw [Function.mem_support] at h
           dsimp [F] at h
           have hv : ψ v ≠ 0 := by
             intro zero
             rw [zero] at h; simp at h
           have htv : ψ (t - v) ≠ 0 := by
             intro zero
             rw [zero] at h; simp at h
           rw [← Function.mem_support] at hv htv
           have h_supp_psi : support ψ = Metric.ball 0 (φ i).rOut := by
             dsimp [ψ]
             simp only [(φ i).support_normed_eq]
           rw [h_supp_psi, Metric.mem_ball, dist_zero_right] at hv htv
           dsimp [K, K_t, K_v]
           rw [mem_prod, Metric.mem_closedBall, Metric.mem_closedBall, dist_zero_right, dist_zero_right]
           constructor
           · calc ‖t‖ = ‖(t-v) + v‖ := by abel_nf
                  _ ≤ ‖t-v‖ + ‖v‖ := norm_add_le _ _
                  _ ≤ (φ i).rOut + (φ i).rOut := add_le_add (le_of_lt htv) (le_of_lt hv)
                  _ = 2 * (φ i).rOut := by ring
           · exact le_of_lt hv

         -- Continuity on K
         have h_cont_F : ContinuousOn F K := by
            apply ContinuousOn.mul
            · apply ContinuousOn.mul
              · have h_cont_ψ : Continuous ψ := (φ i).continuous_normed
                exact Continuous.continuousOn (h_cont_ψ.comp continuous_snd)
              · have h_cont_ψ : Continuous ψ := (φ i).continuous_normed
                exact Continuous.continuousOn (h_cont_ψ.comp (continuous_fst.sub continuous_snd))
            · apply ContinuousOn.comp hC
              · exact Continuous.continuousOn (continuous_const.sub continuous_fst)
              · intro ⟨t, v⟩ htv
                dsimp [K, K_t, K_v] at htv
                simp only [mem_prod, Metric.mem_closedBall, dist_zero_right, mem_setOf_eq, sub_ne_zero] at htv ⊢
                by_contra h_ta
                rw [← h_ta] at htv
                have hr : (φ i).rOut < ‖a‖ / 3 := by
                   rw [mem_preimage, Metric.mem_ball, dist_zero_right] at hi
                   rw [Real.norm_of_nonneg (le_of_lt (φ i).rOut_pos)] at hi
                   exact hi
                have : ‖a‖ < ‖a‖ := by
                   rcases htv with ⟨ht, _⟩
                   calc ‖a‖ ≤ 2 * (φ i).rOut := ht
                        _ < 2 * (‖a‖ / 3) := mul_lt_mul_of_pos_left hr (by norm_num)
                        _ < ‖a‖ := by linarith [norm_nonneg a]
                linarith

         change Integrable F (volume.prod volume)
         rw [← MeasureTheory.integrableOn_iff_integrable_of_support_subset h_supp_F]
         exact h_cont_F.integrableOn_compact hK_compact

    rw [h_assoc]

  -- Use Tendsto.congr' with the eventually equal functions
  have h_eq' : ∀ᶠ i in l,
      (bumpSelfConv (φ i) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] C) a =
      (∫ x, ∫ y, (φ i).normed volume (x - a) * C (x - y) * (φ i).normed volume y) := by
    filter_upwards [h_eq] with i hi
    exact hi.symm
  exact Tendsto.congr' h_eq' h_selfconv_limit

end DoubleMollifierConvergence
