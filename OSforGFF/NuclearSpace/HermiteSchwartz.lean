/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
/-!
# Hermite / Gaussian Schwartz functions (1D)

This file begins the analytic “bridge layer” needed to transport nuclearity from rapid-decay
sequence models to Schwartz test functions.

For now we isolate a small, fully-proved and reusable fact:

* the 1D Gaussian `x ↦ exp (-(x^2/2))` is a Schwartz function, and
* its iterated derivatives are (up to signs) Hermite polynomials times the same Gaussian.

These statements are already present in Mathlib at the level of ordinary derivatives
(`Polynomial.deriv_gaussian_eq_hermite_mul_gaussian`); the main work here is to repackage them
into the `SchwartzMap` API.
-/

open scoped BigOperators

namespace OSforGFF

noncomputable section

namespace HermiteSchwartz

open Filter Topology SchwartzMap

/-! ## A general “boundedness from cocompact decay” lemma -/

lemma bounded_of_continuous_tendsto_zero
    {g : ℝ → ℝ} (hg_cont : Continuous g) (hg_zero : Tendsto g (cocompact ℝ) (nhds 0)) :
    ∃ C : ℝ, ∀ x, ‖g x‖ ≤ C := by
  rw [Metric.tendsto_nhds] at hg_zero
  have h1 := hg_zero 1 (by norm_num : (0 : ℝ) < 1)
  rw [Filter.eventually_iff_exists_mem] at h1
  rcases h1 with ⟨S, hS_mem, hS⟩
  rcases (Filter.mem_cocompact.mp hS_mem) with ⟨K, hKcpt, hKsub⟩
  have h_out : ∀ x ∉ K, ‖g x‖ < 1 := by
    intro x hxK
    have hxS : x ∈ S := hKsub hxK
    have : dist (g x) 0 < 1 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hS x hxS
    simpa [dist_eq_norm] using this
  have himg_cpt : IsCompact (Set.image (‖g ·‖) K) :=
    hKcpt.image (continuous_norm.comp hg_cont)
  rcases himg_cpt.isBounded.subset_closedBall 0 with ⟨M, hM⟩
  refine ⟨max M 1, ?_⟩
  intro x
  by_cases hxK : x ∈ K
  · have hx : ‖g x‖ ∈ Set.image (‖g ·‖) K := ⟨x, hxK, rfl⟩
    have hx_ball : ‖g x‖ ∈ Metric.closedBall (0 : ℝ) M := hM hx
    have hle : ‖g x‖ ≤ M := by
      simpa [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, abs_norm] using hx_ball
    exact le_trans hle (le_max_left _ _)
  · exact le_trans (le_of_lt (h_out x hxK)) (le_max_right _ _)

/-! ## A convenient decay lemma for monomials times Gaussians -/

lemma tendsto_pow_mul_norm_pow_mul_exp_neg_mul_sq_cocompact
    (a : ℝ) (ha : 0 < a) (r s : ℕ) :
    Tendsto (fun x : ℝ => x ^ r * ‖x‖ ^ s * Real.exp (-a * x ^ 2)) (cocompact ℝ) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hnorm :
      (fun x : ℝ => ‖x ^ r * ‖x‖ ^ s * Real.exp (-a * x ^ 2)‖) =
        fun x : ℝ => |x| ^ (r + s) * Real.exp (-a * x ^ 2) := by
    funext x
    simp [mul_assoc, norm_mul, norm_pow, pow_add, Real.norm_eq_abs]
  have h₀ :
      Tendsto (fun x : ℝ => |x| ^ ((r + s : ℕ) : ℝ) * Real.exp (-a * x ^ 2))
        (cocompact ℝ) (𝓝 0) :=
    tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact (a := a) ha ((r + s : ℕ) : ℝ)
  have h₁ :
      Tendsto (fun x : ℝ => |x| ^ (r + s) * Real.exp (-a * x ^ 2)) (cocompact ℝ) (𝓝 0) := by
    refine h₀.congr fun x => by
      have hx : |x| ^ ((r + s : ℕ) : ℝ) = |x| ^ (r + s) := by
        simpa using (Real.rpow_natCast |x| (r + s))
      have hx' : |x| ^ (↑r + ↑s : ℝ) = |x| ^ (r + s) := by
        simpa [Nat.cast_add] using hx
      simp [hx']
  exact (hnorm ▸ h₁)

/-! ## The Gaussian as a Schwartz function -/

/-- The (unnormalized) Gaussian \(x \mapsto \exp(-(x^2/2))\). -/
def gaussian (x : ℝ) : ℝ := Real.exp (-(x ^ 2 / 2))

@[simp]
lemma gaussian_def (x : ℝ) : gaussian x = Real.exp (-(x ^ 2 / 2)) := rfl

lemma gaussian_contDiff : ContDiff ℝ (⊤ : ℕ∞) gaussian := by
  simpa [gaussian] using (by fun_prop :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => Real.exp (-(x ^ 2 / 2))))

lemma iteratedDeriv_gaussian_eq_hermite_mul_gaussian (n : ℕ) (x : ℝ) :
    iteratedDeriv n gaussian x =
      (-1 : ℝ) ^ n * Polynomial.aeval x (Polynomial.hermite n) * gaussian x := by
  simpa [gaussian, iteratedDeriv_eq_iterate] using
    (Polynomial.deriv_gaussian_eq_hermite_mul_gaussian n x)

lemma tendsto_pow_mul_iteratedDeriv_gaussian_cocompact (k n : ℕ) :
    Tendsto (fun x : ℝ => ‖x‖ ^ k * iteratedDeriv n gaussian x) (cocompact ℝ) (𝓝 0) := by
  have hrepr :
      (fun x : ℝ => ‖x‖ ^ k * iteratedDeriv n gaussian x) =
        fun x : ℝ =>
          ‖x‖ ^ k * ((-1 : ℝ) ^ n * Polynomial.aeval x (Polynomial.hermite n) * gaussian x) := by
    funext x
    simp [iteratedDeriv_gaussian_eq_hermite_mul_gaussian (n := n), mul_left_comm, mul_comm]
  have haeval :
      ∀ x : ℝ,
        Polynomial.aeval x (Polynomial.hermite n) =
          ∑ i ∈ Finset.range (n + 1), (Polynomial.hermite n).coeff i • x ^ i := by
    intro x
    simpa [Polynomial.natDegree_hermite] using
      (Polynomial.aeval_eq_sum_range (R := ℤ) (S := ℝ) (p := Polynomial.hermite n) x)
  have hsum :
      (fun x : ℝ =>
          ‖x‖ ^ k * ((-1 : ℝ) ^ n * Polynomial.aeval x (Polynomial.hermite n) * gaussian x)) =
        fun x : ℝ =>
          ∑ i ∈ Finset.range (n + 1),
            ‖x‖ ^ k * ((-1 : ℝ) ^ n * ((Polynomial.hermite n).coeff i) • x ^ i * gaussian x) := by
    funext x
    simp [haeval x, gaussian, mul_assoc, mul_left_comm, mul_comm, Finset.mul_sum]
  have hterm :
      ∀ i ∈ Finset.range (n + 1),
        Tendsto
          (fun x : ℝ => ‖x‖ ^ k * ((-1 : ℝ) ^ n * ((Polynomial.hermite n).coeff i) • x ^ i * gaussian x))
          (cocompact ℝ) (𝓝 0) := by
    intro i hi
    have hmono :
        Tendsto (fun x : ℝ => x ^ i * ‖x‖ ^ k * Real.exp (-(1 / 2 : ℝ) * x ^ 2))
          (cocompact ℝ) (𝓝 0) := by
      simpa [mul_assoc] using
        (tendsto_pow_mul_norm_pow_mul_exp_neg_mul_sq_cocompact (a := (1 / 2 : ℝ)) (by positivity)
          (r := i) (s := k))
    have hgauss :
        (fun x : ℝ => ‖x‖ ^ k * ((-1 : ℝ) ^ n * ((Polynomial.hermite n).coeff i) • x ^ i * gaussian x)) =
          fun x : ℝ =>
            ((-1 : ℝ) ^ n) * ((Polynomial.hermite n).coeff i : ℤ) *
              (x ^ i * ‖x‖ ^ k * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) := by
      funext x
      have hexp : Real.exp (-(x ^ 2 / 2)) = Real.exp (-(1 / 2 : ℝ) * x ^ 2) := by
        congr 1
        simp [div_eq_mul_inv, mul_comm]
      simp [gaussian, hexp, mul_assoc, mul_left_comm, mul_comm]
    have ht :
        Tendsto
          (fun x : ℝ =>
            ((-1 : ℝ) ^ n * ((Polynomial.hermite n).coeff i : ℝ)) *
              (x ^ i * ‖x‖ ^ k * Real.exp (-(1 / 2 : ℝ) * x ^ 2)))
          (cocompact ℝ) (𝓝 0) := by
      simpa using (tendsto_const_nhds.mul hmono)
    refine (ht.congr fun x => ?_)
    have hx := congrArg (fun f : ℝ → ℝ => f x) hgauss.symm
    simpa [mul_assoc, mul_left_comm, mul_comm] using hx
  have hsum_tendsto :
      Tendsto
        (fun x : ℝ =>
          ∑ i ∈ Finset.range (n + 1),
            ‖x‖ ^ k * ((-1 : ℝ) ^ n * ((Polynomial.hermite n).coeff i) • x ^ i * gaussian x))
        (cocompact ℝ) (𝓝 0) := by
    let F : ℕ → ℝ → ℝ :=
      fun i x => ‖x‖ ^ k * ((-1 : ℝ) ^ n * ((Polynomial.hermite n).coeff i) • x ^ i * gaussian x)
    have hF : ∀ i ∈ Finset.range (n + 1), Tendsto (F i) (cocompact ℝ) (𝓝 0) := by
      intro i hi
      simpa [F] using hterm i hi
    simpa [F] using (tendsto_finset_sum (Finset.range (n + 1)) (fun i hi => hF i hi))
  refine Tendsto.congr
    (f₁ := (fun x : ℝ =>
      ∑ i ∈ Finset.range (n + 1),
        ‖x‖ ^ k * ((-1 : ℝ) ^ n * ((Polynomial.hermite n).coeff i) • x ^ i * gaussian x)))
    (f₂ := (fun x : ℝ => ‖x‖ ^ k * iteratedDeriv n gaussian x))
    (l₁ := cocompact ℝ) (l₂ := 𝓝 0) ?_ hsum_tendsto
  intro x
  have hx :
      (‖x‖ ^ k * iteratedDeriv n gaussian x) =
        ∑ i ∈ Finset.range (n + 1),
          ‖x‖ ^ k * ((-1 : ℝ) ^ n * ((Polynomial.hermite n).coeff i) • x ^ i * gaussian x) := by
    have hx1 : (‖x‖ ^ k * iteratedDeriv n gaussian x) =
        ‖x‖ ^ k * ((-1 : ℝ) ^ n * Polynomial.aeval x (Polynomial.hermite n) * gaussian x) :=
      congrArg (fun f : ℝ → ℝ => f x) hrepr
    have hx2 :
        (‖x‖ ^ k * ((-1 : ℝ) ^ n * Polynomial.aeval x (Polynomial.hermite n) * gaussian x)) =
          ∑ i ∈ Finset.range (n + 1),
            ‖x‖ ^ k * ((-1 : ℝ) ^ n * ((Polynomial.hermite n).coeff i) • x ^ i * gaussian x) :=
      congrArg (fun f : ℝ → ℝ => f x) hsum
    exact hx1.trans hx2
  simpa [Real.norm_eq_abs, gaussian, mul_assoc, mul_left_comm, mul_comm] using hx.symm

/-- The Gaussian defines a Schwartz function `𝓢(ℝ, ℝ)`. -/
def gaussianSchwartz : 𝓢(ℝ, ℝ) where
  toFun := gaussian
  smooth' := gaussian_contDiff
  decay' := by
    intro k n
    -- The function `h(x) = ‖x‖^k * iteratedDeriv n gaussian x`, which tends to 0 at infinity.
    let h : ℝ → ℝ := fun x => ‖x‖ ^ k * iteratedDeriv n gaussian x
    have hh_cont : Continuous h := by
      have hgauss_cont : Continuous gaussian := gaussian_contDiff.continuous
      have hpow_cont : Continuous (fun x : ℝ => ‖x‖ ^ k) :=
        (continuous_norm.pow k)
      have haeval_cont :
          Continuous (fun x : ℝ => Polynomial.aeval x (Polynomial.hermite n)) := by
        simpa using (Polynomial.continuous_aeval (p := Polynomial.hermite n) (R := ℤ) (A := ℝ))
      have hrepr_cont :
          Continuous fun x : ℝ =>
            ‖x‖ ^ k * ((-1 : ℝ) ^ n * Polynomial.aeval x (Polynomial.hermite n) * gaussian x) := by
        have hconst : Continuous fun _ : ℝ => ((-1 : ℝ) ^ n) := continuous_const
        have hprod : Continuous fun x : ℝ =>
            ((-1 : ℝ) ^ n) * Polynomial.aeval x (Polynomial.hermite n) * gaussian x := by
          simpa [mul_assoc] using (hconst.mul (haeval_cont.mul hgauss_cont))
        exact hpow_cont.mul hprod
      refine hrepr_cont.congr ?_
      intro x
      simp [h, iteratedDeriv_gaussian_eq_hermite_mul_gaussian (n := n), mul_left_comm, mul_comm]
    have hh_zero : Tendsto h (cocompact ℝ) (nhds 0) :=
      tendsto_pow_mul_iteratedDeriv_gaussian_cocompact (k := k) (n := n)
    rcases bounded_of_continuous_tendsto_zero hh_cont hh_zero with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro x
    have :
        ‖x‖ ^ k * ‖iteratedFDeriv ℝ n gaussian x‖ = ‖h x‖ := by
      simp [h, Real.norm_eq_abs, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    have hx' : ‖h x‖ ≤ C := hC x
    rw [this]
    exact hx'

@[simp]
lemma gaussianSchwartz_apply (x : ℝ) : gaussianSchwartz x = gaussian x := rfl

@[simp]
lemma gaussianSchwartz_coe :
    ((gaussianSchwartz : 𝓢(ℝ, ℝ)) : ℝ → ℝ) = gaussian := rfl


example : gaussianSchwartz 0 = gaussian 0 := rfl

/-! ## Hermite–Gaussian Schwartz functions -/

/-- The `n`-th Schwartz derivative of `gaussianSchwartz`. -/
noncomputable def gaussianSchwartzDeriv (n : ℕ) : 𝓢(ℝ, ℝ) :=
  ((SchwartzMap.derivCLM ℝ ℝ)^[n]) gaussianSchwartz

@[simp]
lemma gaussianSchwartzDeriv_zero : gaussianSchwartzDeriv 0 = gaussianSchwartz := by
  simp [gaussianSchwartzDeriv]

@[simp]
lemma gaussianSchwartzDeriv_succ (n : ℕ) :
    gaussianSchwartzDeriv (n + 1) =
      SchwartzMap.derivCLM ℝ ℝ (gaussianSchwartzDeriv n) := by
  simp [gaussianSchwartzDeriv, Function.iterate_succ_apply']

lemma gaussianSchwartzDeriv_apply (n : ℕ) (x : ℝ) :
    gaussianSchwartzDeriv n x = iteratedDeriv n gaussian x := by
  have hfun :
      ((gaussianSchwartzDeriv n : 𝓢(ℝ, ℝ)) : ℝ → ℝ) = iteratedDeriv n gaussian := by
    induction n with
    | zero =>
        simp [gaussianSchwartzDeriv, iteratedDeriv_zero]
    | succ n ih =>
        funext x
        calc
          gaussianSchwartzDeriv (n + 1) x = deriv (gaussianSchwartzDeriv n) x := by
            simp [gaussianSchwartzDeriv_succ]
          _ = deriv (iteratedDeriv n gaussian) x := by
            simp [ih]
          _ = iteratedDeriv (n + 1) gaussian x := by
            simp [iteratedDeriv_succ]
  exact congrArg (fun f : ℝ → ℝ => f x) hfun

/-- The (probabilists') Hermite polynomial times the Gaussian, as a plain function. -/
def hermiteGaussian (n : ℕ) (x : ℝ) : ℝ :=
  Polynomial.aeval x (Polynomial.hermite n) * gaussian x

@[simp]
lemma hermiteGaussian_def (n : ℕ) (x : ℝ) :
    hermiteGaussian n x = Polynomial.aeval x (Polynomial.hermite n) * gaussian x := rfl

/-- The Hermite–Gaussian function as a Schwartz map, constructed from derivatives of the Gaussian. -/
noncomputable def hermiteGaussianSchwartz (n : ℕ) : 𝓢(ℝ, ℝ) :=
  ((-1 : ℝ) ^ n) • gaussianSchwartzDeriv n

@[simp]
lemma hermiteGaussianSchwartz_apply (n : ℕ) (x : ℝ) :
    hermiteGaussianSchwartz n x = hermiteGaussian n x := by
  have hsign : ((-1 : ℝ) ^ n) * ((-1 : ℝ) ^ n) = 1 := by
    calc
      ((-1 : ℝ) ^ n) * ((-1 : ℝ) ^ n) = (-1 : ℝ) ^ (n + n) := (pow_add (-1 : ℝ) n n).symm
      _ = 1 := (Even.neg_one_pow (α := ℝ) (n := n + n) ⟨n, rfl⟩)
  calc
    hermiteGaussianSchwartz n x
        = ((-1 : ℝ) ^ n) * gaussianSchwartzDeriv n x := by
            simp [hermiteGaussianSchwartz]
    _ = ((-1 : ℝ) ^ n) * iteratedDeriv n gaussian x := by
            simp [gaussianSchwartzDeriv_apply]
    _ = ((-1 : ℝ) ^ n) *
          (((-1 : ℝ) ^ n) * (Polynomial.aeval x (Polynomial.hermite n) * gaussian x)) := by
            simp [iteratedDeriv_gaussian_eq_hermite_mul_gaussian, mul_assoc]
    _ = (((-1 : ℝ) ^ n) * ((-1 : ℝ) ^ n)) * (Polynomial.aeval x (Polynomial.hermite n) * gaussian x) := by
            ring_nf
    _ = hermiteGaussian n x := by
            simp [hermiteGaussian, hsign]

/-! ### Ladder relation: derivatives shift the Hermite index -/

lemma derivCLM_hermiteGaussianSchwartz (n : ℕ) :
    SchwartzMap.derivCLM ℝ ℝ (hermiteGaussianSchwartz n) = -hermiteGaussianSchwartz (n + 1) := by
  ext x
  simp [hermiteGaussianSchwartz, gaussianSchwartzDeriv_succ, pow_succ]

/-!
## Hermite functions for the 1D harmonic oscillator

For nuclearity, it is convenient to work with a Hilbertian seminorm family coming from the
harmonic oscillator. The corresponding (unnormalized) Hermite functions are
\[
u_n(x) = \mathrm{He}_n(x)\, e^{-x^2/4},
\]
where `He_n` are the probabilists' Hermite polynomials (Mathlib's `Polynomial.hermite n`).

These satisfy the eigenvalue equation
\[
(-\partial_x^2 + x^2/4)\,u_n = (n + 1/2)\,u_n,
\]
and hence are orthogonal in `L²(ℝ)` by symmetry of the operator (integration by parts).
-/

/-! ### The quarter-Gaussian as a Schwartz function -/

/-- The quarter-Gaussian \(x \mapsto \exp(-x^2/4)\). -/
def gaussianQuarter (x : ℝ) : ℝ := Real.exp (-(x ^ 2 / 4))

@[simp]
lemma gaussianQuarter_def (x : ℝ) : gaussianQuarter x = Real.exp (-(x ^ 2 / 4)) := rfl

/-- `gaussianQuarter` as a Schwartz function, by scaling `gaussianSchwartz`. -/
noncomputable def gaussianQuarterSchwartz : 𝓢(ℝ, ℝ) := by
  -- `exp(-x^2/4) = gaussian (x / √2)`, and precomposition by a linear equiv preserves Schwartz.
  let c : ℝ := (Real.sqrt 2)⁻¹
  have hc : c ≠ 0 := by
    have : (Real.sqrt 2 : ℝ) ≠ 0 := by
      simp
    exact inv_ne_zero this
  let g : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.smulLeft (Units.mk0 c hc)
  exact SchwartzMap.compCLMOfContinuousLinearEquiv (𝕜 := ℝ) g gaussianSchwartz

@[simp]
lemma gaussianQuarterSchwartz_apply (x : ℝ) :
    gaussianQuarterSchwartz x = gaussianQuarter x := by
  have hsq : ((Real.sqrt 2)⁻¹ : ℝ) ^ 2 = (2 : ℝ)⁻¹ := by
    calc
      ((Real.sqrt 2)⁻¹ : ℝ) ^ 2 = ((Real.sqrt 2 : ℝ) ^ 2)⁻¹ := by
        simp [inv_pow]
      _ = (2 : ℝ)⁻¹ := by
        simp [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2)]
  have hconst :
      (((Real.sqrt 2)⁻¹ * x) ^ 2) * (2 : ℝ)⁻¹ = (x ^ 2) * (4 : ℝ)⁻¹ := by
    calc
      (((Real.sqrt 2)⁻¹ * x) ^ 2) * (2 : ℝ)⁻¹
          = (((Real.sqrt 2)⁻¹ : ℝ) ^ 2 * x ^ 2) * (2 : ℝ)⁻¹ := by
              simp [mul_pow,  mul_left_comm, mul_comm]
      _ = ((2 : ℝ)⁻¹ * x ^ 2) * (2 : ℝ)⁻¹ := by
              simp [hsq]
      _ = (x ^ 2) * (4 : ℝ)⁻¹ := by
              ring
  simp [gaussianQuarterSchwartz, gaussianQuarter, gaussian, div_eq_mul_inv]
  exact hconst

/-! ### Temperate growth of polynomial functions -/

lemma hasTemperateGrowth_aeval_intPoly (p : Polynomial ℤ) :
    Function.HasTemperateGrowth (fun x : ℝ ↦ (Polynomial.aeval x p : ℝ)) := by
  refine Polynomial.induction_on' p (motive := fun p ↦
      Function.HasTemperateGrowth (fun x : ℝ ↦ (Polynomial.aeval x p : ℝ)))
    (fun p q hp hq ↦ ?_) (fun n a ↦ ?_)
  · simpa [Polynomial.aeval_add] using hp.add hq
  · simpa [Polynomial.aeval_monomial] using
      (by fun_prop :
        Function.HasTemperateGrowth (fun x : ℝ ↦ (algebraMap ℤ ℝ a) * x ^ n))

/-! ### Hermite functions as Schwartz maps -/

/-- The (unnormalized) 1D Hermite function \(u_n(x)=\mathrm{He}_n(x)\,e^{-x^2/4}\). -/
def hermiteFun (n : ℕ) (x : ℝ) : ℝ :=
  (Polynomial.aeval x (Polynomial.hermite n) : ℝ) * gaussianQuarter x

@[simp]
lemma hermiteFun_def (n : ℕ) (x : ℝ) :
  hermiteFun n x = (Polynomial.aeval x (Polynomial.hermite n) : ℝ) * gaussianQuarter x := rfl

noncomputable def hermiteFunSchwartz (n : ℕ) : 𝓢(ℝ, ℝ) :=
  SchwartzMap.smulLeftCLM (𝕜 := ℝ) (F := ℝ)
      (fun x : ℝ ↦ (Polynomial.aeval x (Polynomial.hermite n) : ℝ))
      (gaussianQuarterSchwartz)

@[simp]
lemma hermiteFunSchwartz_apply (n : ℕ) (x : ℝ) :
    hermiteFunSchwartz n x = hermiteFun n x := by
  have hg :
      (fun x : ℝ ↦ (Polynomial.aeval x (Polynomial.hermite n) : ℝ)).HasTemperateGrowth := by
    simpa using hasTemperateGrowth_aeval_intPoly (p := Polynomial.hermite n)
  simp [hermiteFunSchwartz, SchwartzMap.smulLeftCLM_apply_apply (F := ℝ) hg,
    hermiteFun, gaussianQuarterSchwartz_apply, gaussianQuarter, smul_eq_mul]

end HermiteSchwartz

end

end OSforGFF
