/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import OSforGFF.NuclearSpace.PhysHermiteSpaceTimeCoeffOpBounds
import OSforGFF.NuclearSpace.PhysHermiteSpaceTimeCoeffToSchwartzBound

import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Function.L2Space

import OSforGFF.Analysis.Distribution.FourierMultiplier
import OSforGFF.NuclearSpace.SchwartzComplexify

/-!
# Bounding Schwartz seminorms by coefficient seminorms (spacetime Hermite model)

This file proves the **hard direction** in the topological equivalence between:

* the standard Schwartz seminorm sequence `OSforGFF.schwartzSeminormSeq`, and
* the Hermite-coefficient (rapid-decay) seminorm sequence `coeffSeminormSeq ξ hξ`.

Concretely, we prove `OSforGFF.schwartzSeminormSeq ≲ coeffSeminormSeq ξ hξ`, i.e.

`Seminorm.IsBounded (coeffSeminormSeq ξ hξ) OSforGFF.schwartzSeminormSeq (LinearMap.id)`.

The proof combines:

* a Sobolev-embedding type estimate (sup-norm bounded by finitely many `L²`-norms of Laplacian
  iterates), implemented via Fourier inversion + Cauchy–Schwarz; and
* the coefficient seminorm bounds for coordinate multiplication and coordinate derivatives from
  `PhysHermiteSpaceTimeCoeffOpBounds`.
-/

open scoped BigOperators FourierTransform RealInnerProductSpace NNReal ENNReal LineDeriv
open scoped Laplacian

namespace PhysLean

noncomputable section

open MeasureTheory

namespace SpaceTimeHermite

/-! ## Elementary inequalities for spacetime coordinates -/

open scoped BigOperators

private lemma sum_ofLp_smul_unitVec (x : SpaceTime) :
    (∑ i : Fin STDimension, (x.ofLp i) • unitVec i) = x := by
  ext j
  calc
    (∑ i : Fin STDimension, (x.ofLp i) • unitVec i) j
        = ∑ i : Fin STDimension, (x.ofLp i) * (if j = i then (1 : ℝ) else 0) := by
            simp [smul_eq_mul, unitVec_ofLp]
    _ = ∑ i : Fin STDimension, (if j = i then x.ofLp i else 0) := by
          simp [mul_ite]
    _ = x.ofLp j := by simp
    _ = x j := by simp

private lemma norm_le_sum_abs_ofLp (x : SpaceTime) :
    ‖x‖ ≤ ∑ i : Fin STDimension, |x.ofLp i| := by
  have hsq :
      (∑ i : Fin STDimension, ‖x i‖ ^ 2) ≤ (∑ i : Fin STDimension, ‖x i‖) ^ 2 := by
    simpa [pow_two] using
      (Finset.sum_sq_le_sq_sum_of_nonneg (s := (Finset.univ : Finset (Fin STDimension)))
        (f := fun i : Fin STDimension => ‖x i‖) (by intro i hi; exact norm_nonneg _))
  have hx :
      √(∑ i : Fin STDimension, ‖x i‖ ^ 2) ≤ ∑ i : Fin STDimension, ‖x i‖ := by
    have hnonneg : 0 ≤ ∑ i : Fin STDimension, ‖x i‖ :=
      Finset.sum_nonneg fun _ _ => norm_nonneg _
    have h' : √(∑ i : Fin STDimension, ‖x i‖ ^ 2) ≤ |∑ i : Fin STDimension, ‖x i‖| := by
      simpa only [Real.sqrt_sq_eq_abs] using (Real.sqrt_le_sqrt hsq)
    simpa only [abs_of_nonneg hnonneg] using h'
  have hn : ‖x‖ = √(∑ i : Fin STDimension, ‖x i‖ ^ 2) := by
    simpa using (EuclideanSpace.norm_eq (x := x))
  calc
    ‖x‖ = √(∑ i : Fin STDimension, ‖x i‖ ^ 2) := hn
    _ ≤ ∑ i : Fin STDimension, ‖x i‖ := hx
    _ = ∑ i : Fin STDimension, |x.ofLp i| := by simp [Real.norm_eq_abs]

private lemma norm_pow_succ_le_card_pow_mul_sum_abs_pow (x : SpaceTime) (k : ℕ) :
    ‖x‖ ^ (k + 1) ≤ (Fintype.card (Fin STDimension) : ℝ) ^ k *
      ∑ i : Fin STDimension, |x.ofLp i| ^ (k + 1) := by
  have hle₁ : ‖x‖ ≤ ∑ i : Fin STDimension, |x.ofLp i| := norm_le_sum_abs_ofLp x
  have hle₂ : ‖x‖ ^ (k + 1) ≤ (∑ i : Fin STDimension, |x.ofLp i|) ^ (k + 1) := by
    exact pow_le_pow_left₀ (by positivity) hle₁ (k + 1)
  have hnonneg : ∀ i : Fin STDimension, i ∈ (Finset.univ : Finset (Fin STDimension)) → 0 ≤ |x.ofLp i| := by
    intro i hi; exact abs_nonneg _
  have hpow :
      (∑ i : Fin STDimension, |x.ofLp i|) ^ (k + 1) ≤
        (Fintype.card (Fin STDimension) : ℝ) ^ k *
          ∑ i : Fin STDimension, |x.ofLp i| ^ (k + 1) := by
    simpa using
      (pow_sum_le_card_mul_sum_pow (s := (Finset.univ : Finset (Fin STDimension)))
        (f := fun i : Fin STDimension => |x.ofLp i|) (hf := hnonneg) k)
  exact le_trans hle₂ hpow

private lemma abs_ofLp_le_norm (x : SpaceTime) (i : Fin STDimension) :
    |x.ofLp i| ≤ ‖x‖ := by
  have hterm :
      (x.ofLp i) ^ 2 ≤ ∑ j : Fin STDimension, ‖x j‖ ^ 2 := by
    have hnonneg :
        ∀ j : Fin STDimension, j ∈ (Finset.univ : Finset (Fin STDimension)) → 0 ≤ ‖x j‖ ^ 2 := by
      intro j hj; positivity
    have : ‖x i‖ ^ 2 ≤ ∑ j : Fin STDimension, ‖x j‖ ^ 2 := by
      simpa using Finset.single_le_sum hnonneg (by simp : i ∈ (Finset.univ : Finset (Fin STDimension)))
    simpa [Real.norm_eq_abs, sq_abs] using this
  have hn : ‖x‖ = √(∑ j : Fin STDimension, ‖x j‖ ^ 2) := by
    simpa using (EuclideanSpace.norm_eq (x := x))
  have := Real.sqrt_le_sqrt hterm
  simpa [hn, Real.sqrt_sq_eq_abs] using this

/-! ## Small helper lemmas for finite sums -/

private lemma sum_le_card_mul_of_pointwise_le {α : Type*} [Fintype α]
    {f : α → ℝ} {C : ℝ} (hf : ∀ a : α, f a ≤ C) :
    (∑ a : α, f a) ≤ (Fintype.card α : ℝ) * C := by
  have : (∑ a : α, f a) ≤ ∑ _a : α, C := by
    refine Finset.sum_le_sum ?_
    intro a ha
    simpa using hf a
  simpa [Finset.sum_const, nsmul_eq_mul] using this

private lemma sum_abs_ofLp_le_card_mul_norm (x : SpaceTime) :
    (∑ i : Fin STDimension, |x.ofLp i|) ≤ (Fintype.card (Fin STDimension) : ℝ) * ‖x‖ := by
  have hcoord : ∀ i : Fin STDimension, |x.ofLp i| ≤ ‖x‖ := fun i => abs_ofLp_le_norm x i
  calc
    (∑ i : Fin STDimension, |x.ofLp i|) ≤ (Fintype.card (Fin STDimension) : ℝ) * ‖x‖ := by
      simpa using sum_le_card_mul_of_pointwise_le (f := fun i : Fin STDimension => |x.ofLp i|)
        (C := ‖x‖) hcoord

private lemma ContinuousMultilinearMap.apply_eq_sum_ofLp_smul_unitVec
    {n : ℕ} (T : ContinuousMultilinearMap ℝ (fun _ : Fin n => SpaceTime) ℝ) (m : Fin n → SpaceTime) :
    T m =
      ∑ r : (Fin n → Fin STDimension), T (fun j => (m j).ofLp (r j) • unitVec (r j)) := by
  have hm : (fun j : Fin n => ∑ i : Fin STDimension, (m j).ofLp i • unitVec i) = m := by
    funext j
    simpa using (sum_ofLp_smul_unitVec (x := m j))
  simpa [hm] using
    (ContinuousMultilinearMap.map_sum (f := T)
      (g := fun j (i : Fin STDimension) => (m j).ofLp i • unitVec i))

private lemma ContinuousMultilinearMap.norm_apply_le_sum_norm_ofLp_smul_unitVec
    {n : ℕ} (T : ContinuousMultilinearMap ℝ (fun _ : Fin n => SpaceTime) ℝ) (m : Fin n → SpaceTime) :
    ‖T m‖ ≤ ∑ r : (Fin n → Fin STDimension), ‖T (fun j => (m j).ofLp (r j) • unitVec (r j))‖ := by
  simpa [ContinuousMultilinearMap.apply_eq_sum_ofLp_smul_unitVec (T := T) (m := m)] using
    (norm_sum_le (s := (Finset.univ : Finset (Fin n → Fin STDimension)))
      (f := fun r => T (fun j => (m j).ofLp (r j) • unitVec (r j))))

private lemma ContinuousMultilinearMap.norm_prod_ofLp_le_prod_sum_abs_ofLp
    {n : ℕ} (m : Fin n → SpaceTime) (r : Fin n → Fin STDimension) :
    ‖(∏ j : Fin n, (m j).ofLp (r j))‖ ≤ ∏ j : Fin n, ∑ i : Fin STDimension, |(m j).ofLp i| := by
  have hfac :
      ∀ j : Fin n, ‖(m j).ofLp (r j)‖ ≤ ∑ i : Fin STDimension, |(m j).ofLp i| := by
    intro j
    have hnonneg :
        ∀ i : Fin STDimension, i ∈ (Finset.univ : Finset (Fin STDimension)) → 0 ≤ |(m j).ofLp i| := by
      intro i hi
      exact abs_nonneg _
    have : |(m j).ofLp (r j)| ≤ ∑ i : Fin STDimension, |(m j).ofLp i| := by
      simpa using
        (Finset.single_le_sum (s := (Finset.univ : Finset (Fin STDimension)))
          (f := fun i : Fin STDimension => |(m j).ofLp i|) hnonneg
          (by simp : r j ∈ (Finset.univ : Finset (Fin STDimension))))
    simpa [Real.norm_eq_abs] using this
  have :=
    Finset.prod_le_prod (s := (Finset.univ : Finset (Fin n)))
      (fun j hj => by positivity)
      (fun j hj => hfac j)
  simpa using this

private lemma ContinuousMultilinearMap.norm_apply_ofLp_smul_unitVec_le_prod_sum_abs_ofLp_mul_norm_apply_unitVec
    {n : ℕ} (T : ContinuousMultilinearMap ℝ (fun _ : Fin n => SpaceTime) ℝ)
    (m : Fin n → SpaceTime) (r : Fin n → Fin STDimension) :
    ‖T (fun j => (m j).ofLp (r j) • unitVec (r j))‖ ≤
      ((∏ j : Fin n, ∑ i : Fin STDimension, |(m j).ofLp i|) : ℝ) * ‖T (fun j => unitVec (r j))‖ := by
  have hsmul :
      T (fun j => (m j).ofLp (r j) • unitVec (r j)) =
        (∏ j : Fin n, (m j).ofLp (r j)) • T (fun j => unitVec (r j)) := by
    simpa using
      (ContinuousMultilinearMap.map_smul_univ (f := T)
        (c := fun j : Fin n => (m j).ofLp (r j)) (m := fun j => unitVec (r j)))
  calc
    ‖T (fun j => (m j).ofLp (r j) • unitVec (r j))‖
        = ‖(∏ j : Fin n, (m j).ofLp (r j)) • T (fun j => unitVec (r j))‖ := by simp [hsmul]
    _ ≤ ‖(∏ j : Fin n, (m j).ofLp (r j))‖ * ‖T (fun j => unitVec (r j))‖ := by simp
    _ ≤ ((∏ j : Fin n, ∑ i : Fin STDimension, |(m j).ofLp i|) : ℝ) * ‖T (fun j => unitVec (r j))‖ := by
          gcongr
          exact ContinuousMultilinearMap.norm_prod_ofLp_le_prod_sum_abs_ofLp (m := m) (r := r)

private lemma ContinuousMultilinearMap.sum_norm_apply_ofLp_smul_unitVec_le_prod_sum_abs_ofLp_mul_sum_norm_apply_unitVec
    {n : ℕ} (T : ContinuousMultilinearMap ℝ (fun _ : Fin n => SpaceTime) ℝ) (m : Fin n → SpaceTime) :
    (∑ r : (Fin n → Fin STDimension), ‖T (fun j => (m j).ofLp (r j) • unitVec (r j))‖) ≤
      ((∏ j : Fin n, ∑ i : Fin STDimension, |(m j).ofLp i|) : ℝ) *
        (∑ r : (Fin n → Fin STDimension), ‖T (fun j => unitVec (r j))‖) := by
  have h :
      (Finset.univ : Finset (Fin n → Fin STDimension)).sum
          (fun r => ‖T (fun j => (m j).ofLp (r j) • unitVec (r j))‖)
        ≤
        (Finset.univ : Finset (Fin n → Fin STDimension)).sum
          (fun r =>
            ((∏ j : Fin n, ∑ i : Fin STDimension, |(m j).ofLp i|) : ℝ) * ‖T (fun j => unitVec (r j))‖) := by
    refine Finset.sum_le_sum ?_
    intro r hr
    simpa [mul_assoc] using
      (ContinuousMultilinearMap.norm_apply_ofLp_smul_unitVec_le_prod_sum_abs_ofLp_mul_norm_apply_unitVec
        (T := T) (m := m) (r := r))
  simpa [Finset.mul_sum, mul_assoc] using h

private lemma ContinuousMultilinearMap.prod_sum_abs_ofLp_le_card_pow_mul_prod_norm
    {n : ℕ} (m : Fin n → SpaceTime) :
    ((∏ j : Fin n, ∑ i : Fin STDimension, |(m j).ofLp i|) : ℝ) ≤
      ((Fintype.card (Fin STDimension) : ℝ) ^ n) * (∏ j : Fin n, ‖m j‖) := by
  have hfactor :
      ∀ j : Fin n,
        (∑ i : Fin STDimension, |(m j).ofLp i|) ≤ (Fintype.card (Fin STDimension) : ℝ) * ‖m j‖ := by
    intro j
    simpa using (sum_abs_ofLp_le_card_mul_norm (x := m j))
  have h :=
    Finset.prod_le_prod (s := (Finset.univ : Finset (Fin n)))
      (fun j _ => by positivity)
      (fun j _ => hfactor j)
  simpa [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ] using h

private lemma ContinuousMultilinearMap.sum_norm_apply_ofLp_smul_unitVec_le_card_pow_mul_sum_unitVec_mul_prod_norm
    {n : ℕ} (T : ContinuousMultilinearMap ℝ (fun _ : Fin n => SpaceTime) ℝ) (m : Fin n → SpaceTime) :
    (∑ r : (Fin n → Fin STDimension), ‖T (fun j => (m j).ofLp (r j) • unitVec (r j))‖) ≤
      (((Fintype.card (Fin STDimension) : ℝ) ^ n) *
          (∑ r : (Fin n → Fin STDimension), ‖T (fun j => unitVec (r j))‖)) *
        (∏ j : Fin n, ‖m j‖) := by
  have hsum :=
    ContinuousMultilinearMap.sum_norm_apply_ofLp_smul_unitVec_le_prod_sum_abs_ofLp_mul_sum_norm_apply_unitVec
      (T := T) (m := m)
  have hprod := ContinuousMultilinearMap.prod_sum_abs_ofLp_le_card_pow_mul_prod_norm (m := m)
  have hnonneg : 0 ≤ ∑ r : (Fin n → Fin STDimension), ‖T (fun j => unitVec (r j))‖ := by positivity
  have hmul := mul_le_mul_of_nonneg_right hprod hnonneg
  simpa [mul_assoc, mul_left_comm, mul_comm] using (le_trans hsum hmul)

private lemma ContinuousMultilinearMap.norm_apply_le_card_pow_mul_sum_unitVec_mul_prod_norm
    {n : ℕ} (T : ContinuousMultilinearMap ℝ (fun _ : Fin n => SpaceTime) ℝ) (m : Fin n → SpaceTime) :
    ‖T m‖ ≤
      (((Fintype.card (Fin STDimension) : ℝ) ^ n) *
          (∑ r : (Fin n → Fin STDimension), ‖T (fun j => unitVec (r j))‖)) *
        (∏ j : Fin n, ‖m j‖) := by
  refine (ContinuousMultilinearMap.norm_apply_le_sum_norm_ofLp_smul_unitVec (T := T) (m := m)).trans ?_
  exact
    ContinuousMultilinearMap.sum_norm_apply_ofLp_smul_unitVec_le_card_pow_mul_sum_unitVec_mul_prod_norm
      (T := T) (m := m)

private lemma opNorm_le_sum_unitVec
    {n : ℕ} (T : ContinuousMultilinearMap ℝ (fun _ : Fin n => SpaceTime) ℝ) :
    ‖T‖ ≤ ((Fintype.card (Fin STDimension) : ℝ) ^ n) *
      (∑ r : (Fin n → Fin STDimension), ‖T (fun j => unitVec (r j))‖) := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) ?_
  intro m
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    (ContinuousMultilinearMap.norm_apply_le_card_pow_mul_sum_unitVec_mul_prod_norm (T := T) (m := m))

/-! ## Iterates of coordinate multiplication -/

private lemma mulCoordCLM_iter_apply (i : Fin STDimension) (k : ℕ) (f : TestFunction) (x : SpaceTime) :
    ((mulCoordCLM i)^[k] f) x = (x.ofLp i) ^ k * f x := by
  induction k generalizing f with
  | zero =>
    simp
  | succ k ih =>
    -- unfold one iterate and use `mulCoordCLM_apply`, then apply the inductive hypothesis
    simp [Function.iterate_succ_apply', ih, mulCoordCLM_apply, pow_succ,
      mul_assoc, mul_comm]

private lemma mulCoordCLM_iter_norm_apply (i : Fin STDimension) (k : ℕ) (f : TestFunction) (x : SpaceTime) :
    ‖((mulCoordCLM i)^[k] f) x‖ = |x.ofLp i| ^ k * ‖f x‖ := by
  rw [mulCoordCLM_iter_apply (i := i) (k := k) (f := f) (x := x)]
  simp [norm_mul, norm_pow, Real.norm_eq_abs]

/-! ## Bounding Schwartz seminorms by finite sums of `seminorm 0 0` -/

private lemma iteratedFDeriv_norm_le_card_pow_mul_sum_unitVec (n : ℕ) (f : TestFunction) (x : SpaceTime) :
    ‖iteratedFDeriv ℝ n f x‖ ≤ ((Fintype.card (Fin STDimension) : ℝ) ^ n) *
      (∑ r : (Fin n → Fin STDimension), ‖iteratedFDeriv ℝ n f x (fun j => unitVec (r j))‖) := by
  simpa using (opNorm_le_sum_unitVec (n := n) (T := iteratedFDeriv ℝ n f x))

private lemma iteratedFDeriv_unitVec_eq_iteratedLineDerivOp (n : ℕ) (f : TestFunction) (x : SpaceTime)
    (r : Fin n → Fin STDimension) :
    iteratedFDeriv ℝ n f x (fun j : Fin n ↦ unitVec (r j)) =
      (∂^{fun j : Fin n ↦ unitVec (r j)} f) x := by
  simpa using
    (SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv
      (m := fun j : Fin n ↦ unitVec (r j)) (f := f) (x := x)).symm

private lemma iteratedFDeriv_unitVec_norm_le_schwartz_seminorm0 (n : ℕ) (f : TestFunction) (x : SpaceTime)
    (r : Fin n → Fin STDimension) :
    ‖iteratedFDeriv ℝ n f x (fun j : Fin n ↦ unitVec (r j))‖ ≤
      SchwartzMap.seminorm ℝ 0 0 (∂^{fun j : Fin n ↦ unitVec (r j)} f) := by
  have hEq :
      iteratedFDeriv ℝ n f x (fun j : Fin n ↦ unitVec (r j)) =
        (∂^{fun j : Fin n ↦ unitVec (r j)} f) x := by
    simpa using
      (SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv
        (m := fun j : Fin n ↦ unitVec (r j)) (f := f) (x := x)).symm
  simpa [hEq] using
    (SchwartzMap.norm_le_seminorm (𝕜 := ℝ) (f := (∂^{fun j : Fin n ↦ unitVec (r j)} f)) x)

private lemma iteratedFDeriv_norm_le_card_pow_mul_sum_seminorm0 (n : ℕ) (f : TestFunction) (x : SpaceTime) :
    ‖iteratedFDeriv ℝ n f x‖ ≤ ((Fintype.card (Fin STDimension) : ℝ) ^ n) *
      (∑ r : (Fin n → Fin STDimension),
        SchwartzMap.seminorm ℝ 0 0 (∂^{fun j : Fin n ↦ unitVec (r j)} f)) := by
  have hop := iteratedFDeriv_norm_le_card_pow_mul_sum_unitVec (n := n) (f := f) (x := x)
  have hdir :
      (∑ r : (Fin n → Fin STDimension), ‖iteratedFDeriv ℝ n f x (fun j => unitVec (r j))‖) ≤
        ∑ r : (Fin n → Fin STDimension),
          SchwartzMap.seminorm ℝ 0 0 (∂^{fun j : Fin n ↦ unitVec (r j)} f) := by
    refine Finset.sum_le_sum ?_
    intro r hr
    exact iteratedFDeriv_unitVec_norm_le_schwartz_seminorm0 (n := n) (f := f) (x := x) (r := r)
  exact le_trans hop (mul_le_mul_of_nonneg_left hdir (by positivity))

private lemma schwartz_seminorm0_le_card_pow_mul_sum_seminorm0
    (n : ℕ) (f : TestFunction) :
    SchwartzMap.seminorm ℝ 0 n f ≤
      ((Fintype.card (Fin STDimension) : ℝ) ^ n) *
        (∑ r : (Fin n → Fin STDimension),
          SchwartzMap.seminorm ℝ 0 0 (∂^{fun j : Fin n ↦ unitVec (r j)} f)) := by
  refine SchwartzMap.seminorm_le_bound (𝕜 := ℝ) (k := 0) (n := n) f (by positivity) ?_
  intro x
  simp
  simpa using (iteratedFDeriv_norm_le_card_pow_mul_sum_seminorm0 (n := n) (f := f) (x := x))

private lemma abs_pow_mul_iteratedFDeriv_unitVec_norm_le_seminorm0_mulCoordCLM_iter (k n : ℕ) (f : TestFunction)
    (x : SpaceTime) (i : Fin STDimension) (r : Fin n → Fin STDimension) :
    (|x.ofLp i| ^ (k + 1)) * ‖iteratedFDeriv ℝ n f x (fun j : Fin n ↦ unitVec (r j))‖ ≤
      SchwartzMap.seminorm ℝ 0 0 (((mulCoordCLM i)^[k + 1]) (∂^{fun j : Fin n ↦ unitVec (r j)} f)) := by
  have hEq := iteratedFDeriv_unitVec_eq_iteratedLineDerivOp (n := n) (f := f) (x := x) (r := r)
  have hnorm :
      (|x.ofLp i| ^ (k + 1)) * ‖iteratedFDeriv ℝ n f x (fun j : Fin n ↦ unitVec (r j))‖ =
        ‖(((mulCoordCLM i)^[k + 1]) (∂^{fun j : Fin n ↦ unitVec (r j)} f)) x‖ := by
    simpa [hEq] using
      (mulCoordCLM_iter_norm_apply (i := i) (k := k + 1)
        (f := (∂^{fun j : Fin n ↦ unitVec (r j)} f)) (x := x)).symm
  rw [hnorm]
  simpa using
    (SchwartzMap.norm_le_seminorm (𝕜 := ℝ)
      (f := (((mulCoordCLM i)^[k + 1]) (∂^{fun j : Fin n ↦ unitVec (r j)} f))) x)

private lemma sum_abs_pow_mul_sum_iteratedFDeriv_unitVec_norm_eq_sum_sum (k n : ℕ) (f : TestFunction) (x : SpaceTime) :
    (∑ i : Fin STDimension, |x.ofLp i| ^ (k + 1)) *
        (∑ r : (Fin n → Fin STDimension), ‖iteratedFDeriv ℝ n f x (fun j => unitVec (r j))‖)
      =
      ∑ i : Fin STDimension, ∑ r : (Fin n → Fin STDimension),
        (|x.ofLp i| ^ (k + 1)) * ‖iteratedFDeriv ℝ n f x (fun j => unitVec (r j))‖ := by
  simpa using
    (Fintype.sum_mul_sum (f := fun i : Fin STDimension => |x.ofLp i| ^ (k + 1))
      (g := fun r : (Fin n → Fin STDimension) =>
        ‖iteratedFDeriv ℝ n f x (fun j => unitVec (r j))‖))

private lemma sum_sum_abs_pow_mul_iteratedFDeriv_unitVec_norm_le_sum_sum_seminorm0 (k n : ℕ) (f : TestFunction) (x : SpaceTime) :
    (∑ i : Fin STDimension, ∑ r : (Fin n → Fin STDimension),
          (|x.ofLp i| ^ (k + 1)) * ‖iteratedFDeriv ℝ n f x (fun j => unitVec (r j))‖)
      ≤
      ∑ i : Fin STDimension, ∑ r : (Fin n → Fin STDimension),
        SchwartzMap.seminorm ℝ 0 0 (((mulCoordCLM i)^[k + 1]) (∂^{fun j : Fin n ↦ unitVec (r j)} f)) := by
  refine Finset.sum_le_sum ?_
  intro i hi
  refine Finset.sum_le_sum ?_
  intro r hr
  simpa using
    (abs_pow_mul_iteratedFDeriv_unitVec_norm_le_seminorm0_mulCoordCLM_iter
      (k := k) (n := n) (f := f) (x := x) (i := i) (r := r))

private lemma sum_abs_pow_mul_sum_iteratedFDeriv_unitVec_norm_le_sum_sum_seminorm0 (k n : ℕ) (f : TestFunction)
    (x : SpaceTime) :
    (∑ i : Fin STDimension, |x.ofLp i| ^ (k + 1)) *
        (∑ r : (Fin n → Fin STDimension), ‖iteratedFDeriv ℝ n f x (fun j => unitVec (r j))‖)
      ≤
      ∑ i : Fin STDimension, ∑ r : (Fin n → Fin STDimension),
        SchwartzMap.seminorm ℝ 0 0 (((mulCoordCLM i)^[k + 1]) (∂^{fun j : Fin n ↦ unitVec (r j)} f)) := by
  rw [sum_abs_pow_mul_sum_iteratedFDeriv_unitVec_norm_eq_sum_sum (k := k) (n := n) (f := f) (x := x)]
  exact sum_sum_abs_pow_mul_iteratedFDeriv_unitVec_norm_le_sum_sum_seminorm0 (k := k) (n := n) (f := f) (x := x)

private lemma norm_pow_mul_iteratedFDeriv_le_card_pow_mul_sum_abs_pow_mul_sum_dir (k n : ℕ) (f : TestFunction) (x : SpaceTime) :
    ‖x‖ ^ (k + 1) * ‖iteratedFDeriv ℝ n f x‖ ≤
      ((Fintype.card (Fin STDimension) : ℝ) ^ k) *
        ((Fintype.card (Fin STDimension) : ℝ) ^ n) *
          ((∑ i : Fin STDimension, |x.ofLp i| ^ (k + 1)) *
            (∑ r : (Fin n → Fin STDimension), ‖iteratedFDeriv ℝ n f x (fun j => unitVec (r j))‖)) := by
  have hx := norm_pow_succ_le_card_pow_mul_sum_abs_pow (x := x) (k := k)
  have hop := opNorm_le_sum_unitVec (n := n) (T := iteratedFDeriv ℝ n f x)
  have hmul := mul_le_mul hx hop (by positivity) (by positivity)
  simpa [mul_assoc, mul_left_comm, mul_comm] using hmul

private lemma norm_pow_mul_iteratedFDeriv_le_card_pow_mul_sum_seminorm0 (k n : ℕ) (f : TestFunction) (x : SpaceTime) :
    ‖x‖ ^ (k + 1) * ‖iteratedFDeriv ℝ n f x‖ ≤
      ((Fintype.card (Fin STDimension) : ℝ) ^ k) *
        ((Fintype.card (Fin STDimension) : ℝ) ^ n) *
          (∑ i : Fin STDimension, ∑ r : (Fin n → Fin STDimension),
            SchwartzMap.seminorm ℝ 0 0 (((mulCoordCLM i)^[k + 1]) (∂^{fun j : Fin n ↦ unitVec (r j)} f))) := by
  have h1 :=
    norm_pow_mul_iteratedFDeriv_le_card_pow_mul_sum_abs_pow_mul_sum_dir (k := k) (n := n) (f := f) (x := x)
  have h2 :=
    sum_abs_pow_mul_sum_iteratedFDeriv_unitVec_norm_le_sum_sum_seminorm0 (k := k) (n := n) (f := f) (x := x)
  refine h1.trans ?_
  exact mul_le_mul_of_nonneg_left h2 (by positivity)

private lemma schwartz_seminorm_succ_le_card_pow_mul_sum_seminorm0
    (k n : ℕ) (f : TestFunction) :
    SchwartzMap.seminorm ℝ (k + 1) n f ≤
      ((Fintype.card (Fin STDimension) : ℝ) ^ k) *
        ((Fintype.card (Fin STDimension) : ℝ) ^ n) *
          (∑ i : Fin STDimension, ∑ r : (Fin n → Fin STDimension),
            SchwartzMap.seminorm ℝ 0 0 (((mulCoordCLM i)^[k + 1])
              (∂^{fun j : Fin n ↦ unitVec (r j)} f))) := by
  refine SchwartzMap.seminorm_le_bound (𝕜 := ℝ) (k := k + 1) (n := n) f (by positivity) ?_
  intro x
  simpa using (norm_pow_mul_iteratedFDeriv_le_card_pow_mul_sum_seminorm0 (k := k) (n := n) (f := f) (x := x))

/-! ## Iterated coordinate operations and coefficient seminorm bounds -/

private lemma coeffSeminormSeq_mulCoordCLM_iter_le
    (ξ : ℝ) (hξ : ξ ≠ 0) (i : Fin STDimension) (k₀ k : ℕ) (f : TestFunction) :
    coeffSeminormSeq ξ hξ k₀ (((mulCoordCLM i)^[k]) f) ≤
      (∏ j ∈ Finset.range k, (‖(ξ / 2 : ℝ)‖ * Real.sqrt 2 * ((2 : ℝ) ^ (k₀ + j) + 1))) *
        coeffSeminormSeq ξ hξ (k₀ + k) f := by
  induction k generalizing k₀ f with
  | zero => simp
  | succ k ih =>
    have hrec := ih (k₀ := k₀) (f := mulCoordCLM i f)
    have hstep := coeffSeminormSeq_mulCoordCLM_le (ξ := ξ) (hξ := hξ) (i := i) (k := k₀ + k) (f := f)
    have hmul := mul_le_mul_of_nonneg_left hstep (by positivity :
      0 ≤ ∏ j ∈ Finset.range k, (‖(ξ / 2 : ℝ)‖ * Real.sqrt 2 * ((2 : ℝ) ^ (k₀ + j) + 1)))
    have := le_trans (by simpa [Function.iterate_succ_apply] using hrec) hmul
    simpa [mul_assoc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Finset.prod_range_succ] using this


/-! ## Complexification and derivatives -/

private lemma fderiv_ofReal (f : TestFunction) (x : SpaceTime) :
    fderiv ℝ (⇑(toComplex f)) x = (Complex.ofRealCLM).comp (fderiv ℝ (⇑f) x) := by
  simpa [toComplex_apply] using
    (fderiv_comp x
      (ContinuousLinearMap.differentiableAt (f := Complex.ofRealCLM) (x := f x))
      (f.differentiableAt (x := x)))

private lemma lineDeriv_ofReal (f : TestFunction) (m x : SpaceTime) :
    (∂_{m} (OSforGFF.ofRealSchwartz f)) x = (∂_{m} f x : ℂ) := by
  simp [OSforGFF.ofRealSchwartz, SchwartzMap.lineDerivOp_apply_eq_fderiv,
    fderiv_ofReal (f := f) (x := x), ContinuousLinearMap.comp_apply]

private lemma lineDeriv_ofReal_eq (f : TestFunction) (m : SpaceTime) :
    ∂_{m} (OSforGFF.ofRealSchwartz f) = OSforGFF.ofRealSchwartz (∂_{m} f) := by
  ext x
  simpa [OSforGFF.ofRealSchwartz_apply] using (lineDeriv_ofReal (f := f) (m := m) (x := x))

private lemma lineDeriv_toComplex_eq (f : TestFunction) (m : SpaceTime) :
    ∂_{m} (toComplex f) = toComplex (∂_{m} f) := by
  simpa [OSforGFF.ofRealSchwartz, toComplexCLM_apply] using (lineDeriv_ofReal_eq (f := f) (m := m))

private lemma laplacian_ofReal_eq (f : TestFunction) :
    Δ (OSforGFF.ofRealSchwartz f) = OSforGFF.ofRealSchwartz (Δ f) := by
  let b : OrthonormalBasis (Fin (Module.finrank ℝ SpaceTime)) ℝ SpaceTime :=
    stdOrthonormalBasis ℝ SpaceTime
  simp [SchwartzMap.laplacian_eq_sum (b := b), b, map_sum, lineDeriv_toComplex_eq]

lemma norm_le_sum_norm_coord (x : SpaceTime) :
    ‖x‖ ≤ ∑ i : Fin STDimension, ‖x i‖ := by
  have hsq :
      ‖x‖ ^ 2 ≤ (∑ i : Fin STDimension, ‖x i‖) ^ 2 := by
    simpa [EuclideanSpace.norm_sq_eq] using
      (Finset.sum_sq_le_sq_sum_of_nonneg (s := (Finset.univ : Finset (Fin STDimension)))
        (f := fun i : Fin STDimension => ‖x i‖)
        (hf := by
          intro i hi
          exact norm_nonneg _))
  exact (abs_le_of_sq_le_sq' hsq (by positivity)).2

private lemma norm_pow_succ_le_card_pow_mul_sum_norm_pow (x : SpaceTime) (k : ℕ) :
    ‖x‖ ^ (k + 1) ≤ (Fintype.card (Fin STDimension) : ℝ) ^ k * ∑ i : Fin STDimension, ‖x i‖ ^ (k + 1) := by
  have hx := norm_le_sum_norm_coord x
  have hxpow : ‖x‖ ^ (k + 1) ≤ (∑ i : Fin STDimension, ‖x i‖) ^ (k + 1) :=
    pow_le_pow_left₀ (norm_nonneg _) hx _
  have hpow :
      (∑ i : Fin STDimension, ‖x i‖) ^ (k + 1) ≤
        (Fintype.card (Fin STDimension) : ℝ) ^ k * ∑ i : Fin STDimension, ‖x i‖ ^ (k + 1) := by
    simpa using
      (pow_sum_le_card_mul_sum_pow (s := (Finset.univ : Finset (Fin STDimension)))
        (f := fun i : Fin STDimension => ‖x i‖) (hf := by intro i hi; simp) k)
  exact hxpow.trans hpow

lemma norm_pow_le_card_pow_mul_sum_norm_pow (x : SpaceTime) (k : ℕ) :
    ‖x‖ ^ k ≤ (Fintype.card (Fin STDimension) : ℝ) ^ (k - 1) * ∑ i : Fin STDimension, ‖x i‖ ^ k := by
  cases k with
  | zero =>
      simp
  | succ k =>
      simpa [Nat.succ_eq_add_one, Nat.add_sub_cancel] using
        (norm_pow_succ_le_card_pow_mul_sum_norm_pow (x := x) (k := k))

/-! ## A Sobolev-type sup-norm estimate for Schwartz functions on spacetime -/
-- (Fourier–Laplacian identity will be proved later, but we do not need it explicitly for the
-- Sobolev step: we will work with the Fourier rule for line derivatives and expand `‖·‖^2`
-- as a sum of squares in an orthonormal basis.)

private lemma fourierInv_fourier_apply_eq_integral (g : TestFunctionℂ) (x : SpaceTime) :
    g x = ∫ ξ : SpaceTime, 𝐞 ⟪ξ, x⟫ • (𝓕 g) ξ := by
  have hx : g x = (𝓕⁻ (𝓕 g)) x := by simp
  have hx' :
      (𝓕⁻ (𝓕 g)) x = 𝓕⁻ ((𝓕 g : TestFunctionℂ) : SpaceTime → ℂ) x := by
    simpa using congrArg (fun h => h x) (SchwartzMap.fourierInv_coe (f := 𝓕 g))
  have hx'' :
      𝓕⁻ ((𝓕 g : TestFunctionℂ) : SpaceTime → ℂ) x = ∫ ξ : SpaceTime, 𝐞 ⟪ξ, x⟫ • (𝓕 g) ξ := by
    simpa using (Real.fourierInv_eq (f := ((𝓕 g : TestFunctionℂ) : SpaceTime → ℂ)) x)
  exact hx.trans (hx'.trans hx'')

private lemma norm_le_integral_norm_fourier (g : TestFunctionℂ) (x : SpaceTime) :
    ‖g x‖ ≤ ∫ ξ : SpaceTime, ‖(𝓕 g) ξ‖ ∂(volume : Measure SpaceTime) := by
  have hx : g x = ∫ ξ : SpaceTime, 𝐞 ⟪ξ, x⟫ • (𝓕 g) ξ :=
    fourierInv_fourier_apply_eq_integral (g := g) (x := x)
  have hnorm :
      ‖∫ ξ : SpaceTime, 𝐞 ⟪ξ, x⟫ • (𝓕 g) ξ‖ ≤ ∫ ξ : SpaceTime, ‖(𝓕 g) ξ‖ := by
    refine (norm_integral_le_integral_norm (f := fun ξ : SpaceTime => 𝐞 ⟪ξ, x⟫ • (𝓕 g) ξ)).trans ?_
    refine le_of_eq ?_
    refine integral_congr_ae ?_
    filter_upwards with ξ
    simp
  simpa [hx] using hnorm

/-!
### Weighted Cauchy–Schwarz for the Fourier inversion integral

We use the weight `w(ξ) = (1 + ‖ξ‖^2)^{-2}`. In spacetime dimension `4`, we have `w ∈ L²`
since `w^2 = (1 + ‖ξ‖^2)^{-4}` is integrable (strictly subcritical decay in dimension `4`).
-/

private def fourierWeight (ξ : SpaceTime) : ℂ :=
  (((((1 : ℝ) + ‖ξ‖ ^ 2) ^ (-2 : ℝ)) : ℝ) : ℂ)

private def fourierWeightInv (ξ : SpaceTime) : ℂ :=
  (((((1 : ℝ) + ‖ξ‖ ^ 2) ^ (2 : ℝ)) : ℝ) : ℂ)

private lemma integrable_weight_sq :
    Integrable (fun ξ : SpaceTime ↦ ((1 : ℝ) + ‖ξ‖ ^ 2) ^ (-(8 * (2 : ℝ)⁻¹)))
      (volume : Measure SpaceTime) := by
  have hdim : (Module.finrank ℝ SpaceTime : ℝ) < (8 : ℝ) := by
    simpa [SpaceTime, STDimension] using (by norm_num : (4 : ℝ) < 8)
  simpa [div_eq_mul_inv] using
    (integrable_rpow_neg_one_add_norm_sq (E := SpaceTime) (μ := (volume : Measure SpaceTime))
      (r := (8 : ℝ)) hdim)

private lemma norm_weight_rpow_two (ξ : SpaceTime) :
    ‖fourierWeight ξ‖ ^ (2 : ℝ) =
      ((1 : ℝ) + ‖ξ‖ ^ 2) ^ (-(8 * (2 : ℝ)⁻¹)) := by
  have hx : 0 ≤ (1 : ℝ) + ‖ξ‖ ^ 2 := by positivity
  have habs :
      ‖fourierWeight ξ‖ =
        ((1 : ℝ) + ‖ξ‖ ^ 2) ^ (-2 : ℝ) := by
    exact Complex.norm_of_nonneg (Real.rpow_nonneg hx _)
  calc
    ‖fourierWeight ξ‖ ^ (2 : ℝ)
        = (((1 : ℝ) + ‖ξ‖ ^ 2) ^ (-2 : ℝ)) ^ (2 : ℝ) := by
            simpa [fourierWeight] using congrArg (fun t : ℝ => t ^ (2 : ℝ)) habs
    _ = ((1 : ℝ) + ‖ξ‖ ^ 2) ^ ((-2 : ℝ) * (2 : ℝ)) := by
          simpa using (Real.rpow_mul (x := (1 : ℝ) + ‖ξ‖ ^ 2) (y := (-2 : ℝ)) (z := (2 : ℝ)) hx).symm
    _ = ((1 : ℝ) + ‖ξ‖ ^ 2) ^ (-(8 * (2 : ℝ)⁻¹)) := by ring_nf

private lemma memLp_weight_two :
    MemLp fourierWeight
      (ENNReal.ofReal (2 : ℝ)) (volume : Measure SpaceTime) := by
  have h2 : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by norm_num
  have hw : MemLp fourierWeight (2 : ℝ≥0∞) (volume : Measure SpaceTime) := by
    have hMeas : AEStronglyMeasurable fourierWeight (volume : Measure SpaceTime) := by
      refine Measurable.aestronglyMeasurable ?_
      change
        Measurable (fun ξ : SpaceTime ↦ (((((1 : ℝ) + ‖ξ‖ ^ 2) ^ (-2 : ℝ)) : ℝ) : ℂ))
      fun_prop
    refine (memLp_two_iff_integrable_sq_norm (μ := (volume : Measure SpaceTime))
      hMeas).2 ?_
    have hInt : Integrable (fun ξ : SpaceTime ↦ ‖fourierWeight ξ‖ ^ (2 : ℝ))
        (volume : Measure SpaceTime) := by
      refine integrable_weight_sq.congr ?_
      exact Filter.Eventually.of_forall (fun ξ => by
        simpa using (norm_weight_rpow_two (ξ := ξ)).symm)
    simpa [Real.rpow_natCast] using hInt
  simpa [h2] using hw

/-!
### Converting an \(L^2\) integral to `‖·.toLp 2‖`

For Schwartz functions we can rewrite \((∫ ‖f‖^2)^{1/2}\) as the `L²` norm of `f.toLp 2`.
We will use this to rewrite the weighted factor in the Cauchy–Schwarz estimate.
-/

private lemma toReal_eLpNorm_two_eq (h : TestFunctionℂ) :
    ENNReal.toReal (eLpNorm h (2 : ℝ≥0∞) (volume : Measure SpaceTime)) =
      (∫ ξ : SpaceTime, ‖h ξ‖ ^ (2 : ℝ) ∂(volume : Measure SpaceTime)) ^ ((2 : ℝ)⁻¹) := by
  have hm : MemLp (fun ξ : SpaceTime => h ξ) (2 : ℝ≥0∞) (volume : Measure SpaceTime) :=
    h.memLp (p := (2 : ℝ≥0∞)) (μ := (volume : Measure SpaceTime))
  have hnonneg : 0 ≤ (∫ ξ : SpaceTime, ‖h ξ‖ ^ (2 : ℝ) ∂(volume : Measure SpaceTime)) ^ ((2 : ℝ)⁻¹) :=
    by positivity
  have he : eLpNorm h (2 : ℝ≥0∞) (volume : Measure SpaceTime) =
      ENNReal.ofReal
        ((∫ ξ : SpaceTime, ‖h ξ‖ ^ (2 : ℝ) ∂(volume : Measure SpaceTime)) ^ ((2 : ℝ)⁻¹)) := by
    simpa using (MeasureTheory.MemLp.eLpNorm_eq_integral_rpow_norm (μ := (volume : Measure SpaceTime))
      (hp1 := (by norm_num)) (hp2 := (by norm_num)) hm)
  rw [he]
  simpa using (ENNReal.toReal_ofReal hnonneg)

private lemma toReal_eLpNorm_two_eq_real (h : TestFunction) :
    ENNReal.toReal (eLpNorm h (2 : ℝ≥0∞) (volume : Measure SpaceTime)) =
      (∫ ξ : SpaceTime, ‖h ξ‖ ^ (2 : ℝ) ∂(volume : Measure SpaceTime)) ^ ((2 : ℝ)⁻¹) := by
  have hm : MemLp (fun ξ : SpaceTime => h ξ) (2 : ℝ≥0∞) (volume : Measure SpaceTime) :=
    h.memLp (p := (2 : ℝ≥0∞)) (μ := (volume : Measure SpaceTime))
  have hnonneg : 0 ≤ (∫ ξ : SpaceTime, ‖h ξ‖ ^ (2 : ℝ) ∂(volume : Measure SpaceTime)) ^ ((2 : ℝ)⁻¹) :=
    by positivity
  have he : eLpNorm h (2 : ℝ≥0∞) (volume : Measure SpaceTime) =
      ENNReal.ofReal
        ((∫ ξ : SpaceTime, ‖h ξ‖ ^ (2 : ℝ) ∂(volume : Measure SpaceTime)) ^ ((2 : ℝ)⁻¹)) := by
    simpa using (MeasureTheory.MemLp.eLpNorm_eq_integral_rpow_norm (μ := (volume : Measure SpaceTime))
      (hp1 := (by norm_num)) (hp2 := (by norm_num)) hm)
  rw [he]
  simpa using (ENNReal.toReal_ofReal hnonneg)

private lemma integral_norm_rpow_two_rpow_inv_eq_norm_toLp (h : TestFunctionℂ) :
    (∫ ξ : SpaceTime, ‖h ξ‖ ^ (2 : ℝ) ∂(volume : Measure SpaceTime)) ^ (1 / (2 : ℝ))
      = ‖h.toLp 2 (volume : Measure SpaceTime)‖ := by
  have hnorm :=
    (SchwartzMap.norm_toLp (f := h) (p := (2 : ℝ≥0∞)) (μ := (volume : Measure SpaceTime))).symm
  simpa using (toReal_eLpNorm_two_eq (h := h)).symm.trans hnorm

private lemma integral_norm_rpow_two_rpow_inv_eq_norm_toLp_real (h : TestFunction) :
    (∫ ξ : SpaceTime, ‖h ξ‖ ^ (2 : ℝ) ∂(volume : Measure SpaceTime)) ^ (1 / (2 : ℝ))
      = ‖h.toLp 2 (volume : Measure SpaceTime)‖ := by
  have hnorm :=
    (SchwartzMap.norm_toLp (f := h) (p := (2 : ℝ≥0∞)) (μ := (volume : Measure SpaceTime))).symm
  simpa using (toReal_eLpNorm_two_eq_real (h := h)).symm.trans hnorm

private lemma norm_toLp_ofRealSchwartz_eq (f : TestFunction) :
    ‖(OSforGFF.ofRealSchwartz f).toLp 2 (volume : Measure SpaceTime)‖ =
      ‖f.toLp 2 (volume : Measure SpaceTime)‖ := by
  have hint :
      (∫ ξ : SpaceTime, ‖(OSforGFF.ofRealSchwartz f) ξ‖ ^ (2 : ℝ) ∂(volume : Measure SpaceTime))
        =
        ∫ ξ : SpaceTime, ‖f ξ‖ ^ (2 : ℝ) ∂(volume : Measure SpaceTime) := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with ξ
    simp
  calc
    ‖(OSforGFF.ofRealSchwartz f).toLp 2 (volume : Measure SpaceTime)‖
        =
        (∫ ξ : SpaceTime, ‖(OSforGFF.ofRealSchwartz f) ξ‖ ^ (2 : ℝ) ∂(volume : Measure SpaceTime)) ^
          (1 / (2 : ℝ)) := by
          simpa using (integral_norm_rpow_two_rpow_inv_eq_norm_toLp (h := OSforGFF.ofRealSchwartz f)).symm
    _ =
        (∫ ξ : SpaceTime, ‖f ξ‖ ^ (2 : ℝ) ∂(volume : Measure SpaceTime)) ^ (1 / (2 : ℝ)) := by
          rw [hint]
    _ = ‖f.toLp 2 (volume : Measure SpaceTime)‖ := by
          simpa using (integral_norm_rpow_two_rpow_inv_eq_norm_toLp_real (h := f))

private lemma memLp_fourierWeightInv_smul_fourier (g : TestFunctionℂ) :
    MemLp (fun ξ : SpaceTime ↦ fourierWeightInv ξ • (𝓕 g) ξ)
      (ENNReal.ofReal (2 : ℝ)) (volume : Measure SpaceTime) := by
  have hgrowth : (fun ξ : SpaceTime ↦ fourierWeightInv ξ).HasTemperateGrowth := by
    simpa [fourierWeightInv] using (by
      fun_prop :
        (fun ξ : SpaceTime ↦ (((((1 : ℝ) + ‖ξ‖ ^ 2) ^ (2 : ℝ)) : ℝ) : ℂ)).HasTemperateGrowth)
  let h : TestFunctionℂ := SchwartzMap.smulLeftCLM (F := ℂ) (fun ξ : SpaceTime ↦ fourierWeightInv ξ) (𝓕 g)
  have hh : MemLp h (ENNReal.ofReal (2 : ℝ)) (volume : Measure SpaceTime) := by
    simpa [h] using (h.memLp (p := (ENNReal.ofReal (2 : ℝ))) (μ := (volume : Measure SpaceTime)))
  have hAE :
      (fun ξ : SpaceTime ↦ fourierWeightInv ξ • (𝓕 g) ξ) =ᶠ[ae (volume : Measure SpaceTime)] h := by
    refine Filter.Eventually.of_forall (fun ξ => ?_)
    simpa [h] using (SchwartzMap.smulLeftCLM_apply_apply (hg := hgrowth) (𝓕 g) ξ).symm
  exact (MeasureTheory.memLp_congr_ae hAE).2 hh

private lemma norm_fourierWeight (ξ : SpaceTime) :
    ‖fourierWeight ξ‖ = ((1 : ℝ) + ‖ξ‖ ^ 2) ^ (-2 : ℝ) := by
  have hpos : 0 < (1 : ℝ) + ‖ξ‖ ^ 2 := by positivity
  have hnorm (y : ℝ) : ‖(((((1 : ℝ) + ‖ξ‖ ^ 2) ^ y) : ℝ) : ℂ)‖ = ((1 : ℝ) + ‖ξ‖ ^ 2) ^ y :=
    Complex.norm_of_nonneg (Real.rpow_nonneg (le_of_lt hpos) y)
  dsimp [fourierWeight]
  simpa using (hnorm (-2 : ℝ))

private lemma norm_fourierWeightInv (ξ : SpaceTime) :
    ‖fourierWeightInv ξ‖ = ((1 : ℝ) + ‖ξ‖ ^ 2) ^ (2 : ℝ) := by
  have hpos : 0 < (1 : ℝ) + ‖ξ‖ ^ 2 := by positivity
  have hnorm (y : ℝ) : ‖(((((1 : ℝ) + ‖ξ‖ ^ 2) ^ y) : ℝ) : ℂ)‖ = ((1 : ℝ) + ‖ξ‖ ^ 2) ^ y :=
    Complex.norm_of_nonneg (Real.rpow_nonneg (le_of_lt hpos) y)
  dsimp [fourierWeightInv]
  simpa using (hnorm (2 : ℝ))

private lemma norm_fourierWeight_mul_norm_fourierWeightInv (ξ : SpaceTime) :
    ‖fourierWeight ξ‖ * ‖fourierWeightInv ξ‖ = 1 := by
  have hpos : 0 < (1 : ℝ) + ‖ξ‖ ^ 2 := by positivity
  have hmul : ((1 : ℝ) + ‖ξ‖ ^ 2) ^ (-2 : ℝ) * ((1 : ℝ) + ‖ξ‖ ^ 2) ^ (2 : ℝ) = 1 := by
    simpa [show (-2 : ℝ) + (2 : ℝ) = 0 by ring, Real.rpow_zero] using
      (Real.rpow_add hpos (-2 : ℝ) (2 : ℝ)).symm
  calc
    ‖fourierWeight ξ‖ * ‖fourierWeightInv ξ‖
        = ((1 : ℝ) + ‖ξ‖ ^ 2) ^ (-2 : ℝ) * ((1 : ℝ) + ‖ξ‖ ^ 2) ^ (2 : ℝ) := by
            simp [norm_fourierWeight, norm_fourierWeightInv]
    _ = 1 := hmul

private lemma fourierWeight_factor (g : TestFunctionℂ) :
    (fun ξ : SpaceTime ↦ ‖fourierWeight ξ‖ * ‖fourierWeightInv ξ • (𝓕 g) ξ‖) =
      (fun ξ : SpaceTime ↦ ‖(𝓕 g) ξ‖) := by
  funext ξ
  calc
    ‖fourierWeight ξ‖ * ‖fourierWeightInv ξ • (𝓕 g) ξ‖
        = (‖fourierWeight ξ‖ * ‖fourierWeightInv ξ‖) * ‖(𝓕 g) ξ‖ := by
            simp [norm_smul, mul_assoc, mul_left_comm, mul_comm]
    _ = ‖(𝓕 g) ξ‖ := by
          simpa [norm_fourierWeight_mul_norm_fourierWeightInv, mul_assoc]

private lemma holder_fourierWeight (g : TestFunctionℂ) :
    (∫ ξ : SpaceTime, ‖fourierWeight ξ‖ * ‖fourierWeightInv ξ • (𝓕 g) ξ‖ ∂(volume : Measure SpaceTime)) ≤
      ((∫ ξ : SpaceTime, ‖fourierWeight ξ‖ ^ (2 : ℝ) ∂(volume : Measure SpaceTime)) ^ (1 / (2 : ℝ))) *
        ((∫ ξ : SpaceTime, ‖fourierWeightInv ξ • (𝓕 g) ξ‖ ^ (2 : ℝ) ∂(volume : Measure SpaceTime)) ^
          (1 / (2 : ℝ))) := by
  have hpq : (2 : ℝ).HolderConjugate (2 : ℝ) := Real.HolderConjugate.two_two
  exact integral_mul_norm_le_Lp_mul_Lq (μ := (volume : Measure SpaceTime)) (f := fourierWeight)
    (g := fun ξ : SpaceTime ↦ fourierWeightInv ξ • (𝓕 g) ξ)
    (p := (2 : ℝ)) (q := (2 : ℝ)) hpq memLp_weight_two (memLp_fourierWeightInv_smul_fourier (g := g))

private lemma integral_norm_fourier_le_weighted_L2' (g : TestFunctionℂ) :
    (∫ ξ : SpaceTime, ‖(𝓕 g) ξ‖ ∂(volume : Measure SpaceTime)) ≤
      ((∫ ξ : SpaceTime, ‖fourierWeight ξ‖ ^ (2 : ℝ) ∂(volume : Measure SpaceTime)) ^ (1 / (2 : ℝ))) *
        ((∫ ξ : SpaceTime, ‖fourierWeightInv ξ • (𝓕 g) ξ‖ ^ (2 : ℝ) ∂(volume : Measure SpaceTime)) ^
          (1 / (2 : ℝ))) := by
  have hH := holder_fourierWeight (g := g)
  have hAE :
      (fun ξ : SpaceTime ↦ ‖fourierWeight ξ‖ * ‖fourierWeightInv ξ • (𝓕 g) ξ‖)
        =ᶠ[ae (volume : Measure SpaceTime)] fun ξ : SpaceTime ↦ ‖(𝓕 g) ξ‖ :=
    Filter.EventuallyEq.of_eq (fourierWeight_factor (g := g))
  have hIntEq :
      (∫ ξ : SpaceTime, ‖fourierWeight ξ‖ * ‖fourierWeightInv ξ • (𝓕 g) ξ‖
          ∂(volume : Measure SpaceTime)) =
        ∫ ξ : SpaceTime, ‖(𝓕 g) ξ‖ ∂(volume : Measure SpaceTime) :=
    MeasureTheory.integral_congr_ae hAE
  calc
    (∫ ξ : SpaceTime, ‖(𝓕 g) ξ‖ ∂(volume : Measure SpaceTime)) =
        ∫ ξ : SpaceTime, ‖fourierWeight ξ‖ * ‖fourierWeightInv ξ • (𝓕 g) ξ‖
          ∂(volume : Measure SpaceTime) := by
            simpa using hIntEq.symm
    _ ≤ _ := hH

private lemma integral_norm_fourier_le_weighted_L2 (g : TestFunctionℂ) :
    (∫ ξ : SpaceTime, ‖(𝓕 g) ξ‖ ∂(volume : Measure SpaceTime)) ≤
      ((∫ ξ : SpaceTime, ‖(((((1 : ℝ) + ‖ξ‖ ^ 2) ^ (-2 : ℝ)) : ℝ) : ℂ)‖ ^ (2 : ℝ)
          ∂(volume : Measure SpaceTime)) ^ (1 / (2 : ℝ))) *
        ((∫ ξ : SpaceTime,
              ‖(((((1 : ℝ) + ‖ξ‖ ^ 2) ^ (2 : ℝ)) : ℝ) : ℂ) • (𝓕 g) ξ‖ ^ (2 : ℝ)
            ∂(volume : Measure SpaceTime)) ^ (1 / (2 : ℝ))) := by
  simpa [fourierWeight, fourierWeightInv] using (integral_norm_fourier_le_weighted_L2' (g := g))

/-! ## Laplacian bounds in coefficient seminorms -/

private def coeffDerivConst (ξ : ℝ) : ℕ → ℝ := fun k =>
  ‖(1 / (2 * ξ) : ℝ)‖ * Real.sqrt 2 * ((2 : ℝ) ^ k + 1)

private lemma seminorm_finset_sum_le {α : Type*}
    {𝕜 E : Type*} [SeminormedRing 𝕜] [AddCommGroup E] [SMul 𝕜 E]
    (p : Seminorm 𝕜 E) (s : Finset α) (f : α → E) :
    p (Finset.sum s f) ≤ Finset.sum s (fun a => p (f a)) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha ih
    calc
      p (Finset.sum (insert a s) f) = p (f a + Finset.sum s f) := by
        simpa [Finset.sum_insert, ha]
      _ ≤ p (f a) + p (Finset.sum s f) := map_add_le_add p _ _
      _ ≤ p (f a) + Finset.sum s (fun x => p (f x)) := by
        exact add_le_add (le_rfl) ih
      _ = Finset.sum (insert a s) (fun x => p (f x)) := by
        simpa [Finset.sum_insert, ha, add_assoc]

private lemma seminorm_fintype_sum_le {α : Type*} [Fintype α]
    {𝕜 E : Type*} [SeminormedRing 𝕜] [AddCommGroup E] [SMul 𝕜 E]
    (p : Seminorm 𝕜 E) (f : α → E) :
    p (∑ a : α, f a) ≤ ∑ a : α, p (f a) := by
  -- `∑ a : α, f a` is definitionally the `Finset.univ` sum
  simpa using (seminorm_finset_sum_le (p := p) (s := (Finset.univ : Finset α)) (f := f))

private lemma laplacian_eq_sum_derivCoordCLM (f : TestFunction) :
    Δ f = ∑ i : Fin STDimension, derivCoordCLM i (derivCoordCLM i f) := by
  let b : OrthonormalBasis (Fin STDimension) ℝ SpaceTime := EuclideanSpace.basisFun (Fin STDimension) ℝ
  have hb : ∀ i : Fin STDimension, b i = unitVec i := by intro i; simp [b, unitVec]
  have hcoord2 (i : Fin STDimension) : ∂_{b i} (∂_{b i} f) = derivCoordCLM i (derivCoordCLM i f) := by
    rw [hb i]
    calc
      ∂_{unitVec i} (∂_{unitVec i} f) = ∂_{unitVec i} (derivCoordCLM i f) := by
        simpa using congrArg (fun g : TestFunction => ∂_{unitVec i} g) (derivCoordCLM_apply (i := i) (f := f)).symm
      _ = derivCoordCLM i (derivCoordCLM i f) := by
        simpa using (derivCoordCLM_apply (i := i) (f := derivCoordCLM i f)).symm
  simpa [b, hb, hcoord2] using (SchwartzMap.laplacian_eq_sum (b := b) (f := f))

private lemma coeffDerivConst_nonneg (ξ : ℝ) (k : ℕ) : 0 ≤ coeffDerivConst ξ k := by
  dsimp [coeffDerivConst]
  positivity

private lemma coeffSeminormSeq_laplacian_le_sum (ξ : ℝ) (hξ : ξ ≠ 0) (k : ℕ) (f : TestFunction) :
    coeffSeminormSeq ξ hξ k (Δ f) ≤
      ∑ i : Fin STDimension, coeffSeminormSeq ξ hξ k (derivCoordCLM i (derivCoordCLM i f)) := by
  simpa [laplacian_eq_sum_derivCoordCLM] using
    (seminorm_fintype_sum_le (p := (coeffSeminormSeq ξ hξ k))
      (f := fun i : Fin STDimension => derivCoordCLM i (derivCoordCLM i f)))

private lemma coeffSeminormSeq_derivCoordCLM_derivCoordCLM_le
    (ξ : ℝ) (hξ : ξ ≠ 0) (k : ℕ) (i : Fin STDimension) (f : TestFunction) :
    coeffSeminormSeq ξ hξ k (derivCoordCLM i (derivCoordCLM i f)) ≤
      (coeffDerivConst ξ k) * (coeffDerivConst ξ (k + 1)) * coeffSeminormSeq ξ hξ (k + 2) f := by
  have h2 :
      coeffSeminormSeq ξ hξ (k + 1) (derivCoordCLM i f) ≤
        (coeffDerivConst ξ (k + 1)) * coeffSeminormSeq ξ hξ (k + 2) f := by
    simpa [coeffDerivConst, Nat.add_assoc] using
      (coeffSeminormSeq_derivCoordCLM_le (ξ := ξ) (hξ := hξ) (i := i) (k := k + 1) (f := f))
  have hk : 0 ≤ coeffDerivConst ξ k := coeffDerivConst_nonneg (ξ := ξ) (k := k)
  calc
    coeffSeminormSeq ξ hξ k (derivCoordCLM i (derivCoordCLM i f)) ≤
        (coeffDerivConst ξ k) * coeffSeminormSeq ξ hξ (k + 1) (derivCoordCLM i f) := by
          simpa [coeffDerivConst] using
            (coeffSeminormSeq_derivCoordCLM_le (ξ := ξ) (hξ := hξ) (i := i) (k := k)
              (f := derivCoordCLM i f))
    _ ≤ (coeffDerivConst ξ k) * ((coeffDerivConst ξ (k + 1)) * coeffSeminormSeq ξ hξ (k + 2) f) := by
          exact mul_le_mul_of_nonneg_left h2 hk
    _ = (coeffDerivConst ξ k) * (coeffDerivConst ξ (k + 1)) * coeffSeminormSeq ξ hξ (k + 2) f := by
          ring

private lemma coeffSeminormSeq_laplacian_le (ξ : ℝ) (hξ : ξ ≠ 0) (k : ℕ) (f : TestFunction) :
    coeffSeminormSeq ξ hξ k (Δ f) ≤
      (Fintype.card (Fin STDimension) : ℝ) *
        (coeffDerivConst ξ k) * (coeffDerivConst ξ (k + 1)) *
          coeffSeminormSeq ξ hξ (k + 2) f := by
  have hsum := coeffSeminormSeq_laplacian_le_sum (ξ := ξ) (hξ := hξ) (k := k) (f := f)
  have hterm : ∀ i : Fin STDimension,
      coeffSeminormSeq ξ hξ k (derivCoordCLM i (derivCoordCLM i f)) ≤
        (coeffDerivConst ξ k) * (coeffDerivConst ξ (k + 1)) * coeffSeminormSeq ξ hξ (k + 2) f := by
    intro i; simpa [mul_assoc] using (coeffSeminormSeq_derivCoordCLM_derivCoordCLM_le (ξ := ξ) (hξ := hξ) (k := k) (i := i) (f := f))
  have hsum' :
      (∑ i : Fin STDimension, coeffSeminormSeq ξ hξ k (derivCoordCLM i (derivCoordCLM i f))) ≤
        (Fintype.card (Fin STDimension) : ℝ) *
          ((coeffDerivConst ξ k) * (coeffDerivConst ξ (k + 1)) * coeffSeminormSeq ξ hξ (k + 2) f) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (sum_le_card_mul_of_pointwise_le
        (f := fun i : Fin STDimension => coeffSeminormSeq ξ hξ k (derivCoordCLM i (derivCoordCLM i f)))
        (C := (coeffDerivConst ξ k) * (coeffDerivConst ξ (k + 1)) * coeffSeminormSeq ξ hξ (k + 2) f) hterm)
  have h := le_trans hsum hsum'
  simpa [mul_assoc, mul_left_comm, mul_comm] using h

/-! ## A Sobolev bound for the Fourier weight `(1 + ‖ξ‖^2)^2` -/

private def sobolevWeight : SpaceTime → ℝ := fun ξ : SpaceTime =>
  (1 + ‖ξ‖ ^ 2) ^ 2

private def quadWeight : SpaceTime → ℝ := fun ξ : SpaceTime => ‖ξ‖ ^ 2

set_option maxHeartbeats 800000 in
private lemma norm_toLp_fourierMultiplierCLM_sobolevWeight_le (g : TestFunctionℂ) :
    ‖(SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) sobolevWeight g).toLp 2
        (volume : Measure SpaceTime)‖ ≤
      (1 : ℝ) * ‖g.toLp 2 (volume : Measure SpaceTime)‖
        + ((2 : ℝ) / ((2 * Real.pi) ^ 2)) * ‖(Δ g).toLp 2 (volume : Measure SpaceTime)‖
        + (1 / ((2 * Real.pi) ^ 4)) * ‖(Δ (Δ g)).toLp 2 (volume : Measure SpaceTime)‖ := by
  set w : SpaceTime → ℝ := sobolevWeight with hw
  set n2 : SpaceTime → ℝ := quadWeight with hn2_def
  set h : TestFunctionℂ := SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) w g
  -- rewrite the goal in terms of `h`
  have hh :
      (SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) sobolevWeight g).toLp 2
          (volume : Measure SpaceTime)
        =
      h.toLp 2 (volume : Measure SpaceTime) := by
    simpa [h, w, hw]
  have hh_norm :
      ‖(SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) sobolevWeight g).toLp 2
            (volume : Measure SpaceTime)‖
        =
      ‖h.toLp 2 (volume : Measure SpaceTime)‖ := by
    simpa using congrArg (fun z => ‖z‖) hh
  -- from now on, prove the bound for `h`
  suffices hbound :
      ‖h.toLp 2 (volume : Measure SpaceTime)‖ ≤
        (1 : ℝ) * ‖g.toLp 2 (volume : Measure SpaceTime)‖
          + ((2 : ℝ) / ((2 * Real.pi) ^ 2)) * ‖(Δ g).toLp 2 (volume : Measure SpaceTime)‖
          + (1 / ((2 * Real.pi) ^ 4)) * ‖(Δ (Δ g)).toLp 2 (volume : Measure SpaceTime)‖ by
    -- rewrite back using `hh`
    simpa [hh_norm] using hbound
  -- rewrite `w` as `1 + 2*n2 + n2^2`
  have hw_poly :
      w = fun ξ : SpaceTime ↦ (1 : ℝ) + (2 : ℝ) * n2 ξ + n2 ξ * n2 ξ := by
    funext ξ'
    simp [w, sobolevWeight, n2, quadWeight, pow_two]
    ring
  have hn2 : n2.HasTemperateGrowth := by
    have : (fun ξ : SpaceTime ↦ ‖ξ‖ ^ 2).HasTemperateGrowth := by
      fun_prop
    simpa [hn2_def, quadWeight] using this
  have hn2sq : (fun ξ : SpaceTime ↦ n2 ξ * n2 ξ).HasTemperateGrowth := by
    have : (fun ξ : SpaceTime ↦ (‖ξ‖ ^ 2) * (‖ξ‖ ^ 2)).HasTemperateGrowth := by
      fun_prop
    simpa [hn2_def, quadWeight] using this
  -- decompose `h` into the three Fourier multiplier terms
  have hdecomp :
      h =
        SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) (fun _ : SpaceTime ↦ (1 : ℝ)) g
          + SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) (fun ξ : SpaceTime ↦ (2 : ℝ) * n2 ξ) g
          + SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) (fun ξ : SpaceTime ↦ n2 ξ * n2 ξ) g := by
    -- rewrite `w` via `hw_poly`, then expand using `fourierMultiplierCLM_add` twice
    have h1 :
        SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) w g =
          SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ)
              (fun ξ : SpaceTime ↦ (1 : ℝ) + (2 : ℝ) * n2 ξ) g
            + SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) (fun ξ : SpaceTime ↦ n2 ξ * n2 ξ) g := by
      have hsum :
          (fun ξ : SpaceTime ↦ (1 : ℝ) + (2 : ℝ) * n2 ξ + n2 ξ * n2 ξ)
            =
            (fun ξ : SpaceTime ↦ (1 : ℝ) + (2 : ℝ) * n2 ξ) + fun ξ : SpaceTime ↦ n2 ξ * n2 ξ := by
        funext ξ; simp [add_assoc]
      have hadd :=
        SchwartzMap.fourierMultiplierCLM_add (F := (ℂ))
          (g₁ := fun ξ : SpaceTime ↦ (1 : ℝ) + (2 : ℝ) * n2 ξ)
          (g₂ := fun ξ : SpaceTime ↦ n2 ξ * n2 ξ)
          (by fun_prop) hn2sq
      simpa [hw_poly, hsum] using congrArg (fun T => T g) hadd
    have h2 :
        SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) (fun ξ : SpaceTime ↦ (1 : ℝ) + (2 : ℝ) * n2 ξ) g =
          SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) (fun _ : SpaceTime ↦ (1 : ℝ)) g
            + SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) (fun ξ : SpaceTime ↦ (2 : ℝ) * n2 ξ) g := by
      have hadd :=
        SchwartzMap.fourierMultiplierCLM_add (F := (ℂ))
          (g₁ := fun _ : SpaceTime ↦ (1 : ℝ))
          (g₂ := fun ξ : SpaceTime ↦ (2 : ℝ) * n2 ξ)
          (by fun_prop) (by fun_prop)
      simpa [add_comm, add_left_comm, add_assoc] using congrArg (fun T => T g) hadd
    calc
      h = SchwartzMap.fourierMultiplierCLM (F := ℂ) w g := rfl
      _ =
          SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ)
              (fun ξ : SpaceTime ↦ (1 : ℝ) + (2 : ℝ) * n2 ξ) g
            + SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) (fun ξ : SpaceTime ↦ n2 ξ * n2 ξ) g := h1
      _ =
          (SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) (fun _ : SpaceTime ↦ (1 : ℝ)) g
            + SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) (fun ξ : SpaceTime ↦ (2 : ℝ) * n2 ξ) g)
            + SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) (fun ξ : SpaceTime ↦ n2 ξ * n2 ξ) g := by
            simpa [h2, add_assoc]
      _ =
          SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) (fun _ : SpaceTime ↦ (1 : ℝ)) g
            + SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) (fun ξ : SpaceTime ↦ (2 : ℝ) * n2 ξ) g
            + SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) (fun ξ : SpaceTime ↦ n2 ξ * n2 ξ) g := by
            simp [add_assoc]

  -- constant multiplier is the identity
  have hconst :
      SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) (fun _ : SpaceTime ↦ (1 : ℝ)) g = g := by
    simpa using congrArg (fun T => T g)
      (SchwartzMap.fourierMultiplierCLM_const (F := (ℂ)) (E := SpaceTime) (F := ℂ) (c := (1 : ℝ)))

  -- Laplacian identity for the `‖·‖^2` symbol
  have hlap : Δ g = -((2 * Real.pi) ^ 2 : ℝ) • SchwartzMap.fourierMultiplierCLM (F := ℂ) n2 g := by
    -- now `n2` is definitionally `‖·‖^2 : SpaceTime → ℝ`, so the Laplacian identity applies directly
    simpa [n2, quadWeight] using (SchwartzMap.laplacian_eq_fourierMultiplierCLM (F := (ℂ)) (f := g))

  have hmul2 :
      SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) n2 g =
        (-((2 * Real.pi) ^ 2 : ℝ))⁻¹ • Δ g := by
    -- rearrange the Laplacian identity `Δ g = c • M` with `c = -((2π)^2)`
    set c : ℝ := -((2 * Real.pi) ^ 2 : ℝ)
    have hc : c ≠ 0 := by
      have h2 : (2 : ℝ) ≠ 0 := by norm_num
      have hpi : (2 * Real.pi : ℝ) ≠ 0 := mul_ne_zero h2 Real.pi_ne_zero
      have hpow : (2 * Real.pi : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hpi
      simpa [c] using neg_ne_zero.mpr hpow
    have hlap' : Δ g = c • SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) n2 g := by
      simpa [c] using hlap
    -- multiply the Laplacian identity by `c⁻¹`
    have hmul : c⁻¹ • Δ g = SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) n2 g := by
      have := congrArg (fun z : TestFunctionℂ => c⁻¹ • z) hlap'
      simpa [smul_smul, hc] using this
    simpa [c] using hmul.symm

  have hmul4 :
      SchwartzMap.fourierMultiplierCLM (F := ℂ) (fun ξ : SpaceTime ↦ n2 ξ * n2 ξ) g =
        (-((2 * Real.pi) ^ 2 : ℝ))⁻¹ • ((-((2 * Real.pi) ^ 2 : ℝ))⁻¹ • Δ (Δ g)) := by
    -- use composition of Fourier multipliers
    have hcomp :
        SchwartzMap.fourierMultiplierCLM (F := ℂ) (fun ξ : SpaceTime ↦ n2 ξ * n2 ξ) g =
          SchwartzMap.fourierMultiplierCLM (F := ℂ) n2 (SchwartzMap.fourierMultiplierCLM (F := ℂ) n2 g) := by
      have :=
        (SchwartzMap.fourierMultiplierCLM_fourierMultiplierCLM_apply (F := (ℂ))
          (g₁ := n2) (g₂ := n2) hn2 hn2 g)
      simpa [Pi.mul_def] using this.symm
    -- rewrite the inner term using `hmul2`, then apply `hmul2` again to `Δ g`
    have hlapΔ :
        Δ (Δ g) = -((2 * Real.pi) ^ 2 : ℝ) • SchwartzMap.fourierMultiplierCLM (F := ℂ) n2 (Δ g) := by
      simpa [n2, quadWeight] using
        (SchwartzMap.laplacian_eq_fourierMultiplierCLM (F := (ℂ)) (f := (Δ g)))
    have hmul2Δ :
        SchwartzMap.fourierMultiplierCLM (F := ℂ) n2 (Δ g) = (-((2 * Real.pi) ^ 2 : ℝ))⁻¹ • Δ (Δ g) := by
      -- same rearrangement as `hmul2`, but applied to `Δ g`
      set c : ℝ := -((2 * Real.pi) ^ 2 : ℝ)
      have hc : c ≠ 0 := by
        have h2 : (2 : ℝ) ≠ 0 := by norm_num
        have hpi : (2 * Real.pi : ℝ) ≠ 0 := mul_ne_zero h2 Real.pi_ne_zero
        have hpow : (2 * Real.pi : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hpi
        simpa [c] using neg_ne_zero.mpr hpow
      have hlap' : Δ (Δ g) = c • SchwartzMap.fourierMultiplierCLM (F := ℂ) n2 (Δ g) := by
        simpa [c] using hlapΔ
      have hmul : c⁻¹ • Δ (Δ g) = SchwartzMap.fourierMultiplierCLM (F := ℂ) n2 (Δ g) := by
        have := congrArg (fun z : TestFunctionℂ => c⁻¹ • z) hlap'
        simpa [smul_smul, hc] using this
      simpa [c] using hmul.symm
    -- abbreviate the scalar constant
    set c : ℝ := (-((2 * Real.pi) ^ 2 : ℝ))⁻¹ with hc
    -- put everything together
    calc
      SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) (fun ξ : SpaceTime ↦ n2 ξ * n2 ξ) g
          =
        SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) n2
          (SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) n2 g) := hcomp
      _ =
        SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) n2 (c • Δ g) := by
            -- rewrite the inner term using `hmul2`
            -- (then `c` is the same scalar)
            -- NB: `rw` is much cheaper than `simp` here.
            rw [hmul2]
      _ = c •
            SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) n2 (Δ g) := by
            -- linearity in the Schwartz-function argument
            simpa using
              (SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) n2).map_smul c (Δ g)
      _ = c • (c • Δ (Δ g)) := by
            -- rewrite the inner multiplier term using `hmul2Δ`
            rw [hmul2Δ]
      _ = (-((2 * Real.pi) ^ 2 : ℝ))⁻¹ • ((-((2 * Real.pi) ^ 2 : ℝ))⁻¹ • Δ (Δ g)) := by
            -- unfold the abbreviation `c` (if present); otherwise this is definitional
            simpa [hc]
  have hdecomp' :
      h = g + (2 : ℝ) • SchwartzMap.fourierMultiplierCLM (F := ℂ) n2 g
        + SchwartzMap.fourierMultiplierCLM (F := ℂ) (fun ξ : SpaceTime ↦ n2 ξ * n2 ξ) g := by
    have hsmul :
        SchwartzMap.fourierMultiplierCLM (F := ℂ) (fun ξ : SpaceTime ↦ (2 : ℝ) * n2 ξ) g =
          (2 : ℝ) • SchwartzMap.fourierMultiplierCLM (F := ℂ) n2 g := by
      simpa [smul_eq_mul] using
        (SchwartzMap.fourierMultiplierCLM_smul_apply (F := (ℂ)) (hg := hn2) (c := (2 : ℝ)) (f := g))
    simpa [hconst, hsmul, add_assoc] using hdecomp
  have htri :
      ‖h.toLp 2 (volume : Measure SpaceTime)‖
        ≤ ‖g.toLp 2 (volume : Measure SpaceTime)‖
          + ‖((2 : ℝ) • SchwartzMap.fourierMultiplierCLM (F := ℂ) n2 g).toLp 2
              (volume : Measure SpaceTime)‖
          + ‖(SchwartzMap.fourierMultiplierCLM (F := ℂ) (fun ξ : SpaceTime ↦ n2 ξ * n2 ξ) g).toLp 2
              (volume : Measure SpaceTime)‖ := by
    have : h.toLp 2 (volume : Measure SpaceTime)
        = g.toLp 2 (volume : Measure SpaceTime)
          + ((2 : ℝ) • SchwartzMap.fourierMultiplierCLM (F := ℂ) n2 g).toLp 2
              (volume : Measure SpaceTime)
          + (SchwartzMap.fourierMultiplierCLM (F := ℂ) (fun ξ : SpaceTime ↦ n2 ξ * n2 ξ) g).toLp 2
              (volume : Measure SpaceTime) := by
      let T := SchwartzMap.toLpCLM (𝕜 := ℝ) (F := ℂ) (E := SpaceTime) (p := (2 : ℝ≥0∞))
        (μ := (volume : Measure SpaceTime))
      have hEq := congrArg (fun u : TestFunctionℂ => T u) hdecomp'
      -- expand the `T` image of the three-term sum using linearity (avoid heavy `simp`)
      have hEq' :
          T h =
            T g
              + T ((2 : ℝ) • SchwartzMap.fourierMultiplierCLM (F := ℂ) n2 g)
              + T (SchwartzMap.fourierMultiplierCLM (F := ℂ) (fun ξ : SpaceTime ↦ n2 ξ * n2 ξ) g) := by
        -- `hdecomp'` is left-associated: `g + (2•M) + M2 = (g + (2•M)) + M2`
        have h1 :
            T (g + (2 : ℝ) • SchwartzMap.fourierMultiplierCLM (F := ℂ) n2 g +
                SchwartzMap.fourierMultiplierCLM (F := ℂ) (fun ξ : SpaceTime ↦ n2 ξ * n2 ξ) g)
              =
              T (g + (2 : ℝ) • SchwartzMap.fourierMultiplierCLM (F := ℂ) n2 g)
                + T (SchwartzMap.fourierMultiplierCLM (F := ℂ) (fun ξ : SpaceTime ↦ n2 ξ * n2 ξ) g) := by
          simpa [add_assoc] using
            (T.map_add (g + (2 : ℝ) • SchwartzMap.fourierMultiplierCLM (F := ℂ) n2 g)
              (SchwartzMap.fourierMultiplierCLM (F := ℂ) (fun ξ : SpaceTime ↦ n2 ξ * n2 ξ) g))
        have h2 :
            T (g + (2 : ℝ) • SchwartzMap.fourierMultiplierCLM (F := ℂ) n2 g)
              =
              T g + T ((2 : ℝ) • SchwartzMap.fourierMultiplierCLM (F := ℂ) n2 g) := by
          simpa using
            (T.map_add g ((2 : ℝ) • SchwartzMap.fourierMultiplierCLM (F := ℂ) n2 g))
        -- rewrite `hEq` using `h1` and `h2`
        calc
          T h = T (g + (2 : ℝ) • SchwartzMap.fourierMultiplierCLM (F := ℂ) n2 g +
                SchwartzMap.fourierMultiplierCLM (F := ℂ) (fun ξ : SpaceTime ↦ n2 ξ * n2 ξ) g) := hEq
          _ = T (g + (2 : ℝ) • SchwartzMap.fourierMultiplierCLM (F := ℂ) n2 g)
                + T (SchwartzMap.fourierMultiplierCLM (F := ℂ) (fun ξ : SpaceTime ↦ n2 ξ * n2 ξ) g) := h1
          _ = (T g + T ((2 : ℝ) • SchwartzMap.fourierMultiplierCLM (F := ℂ) n2 g))
                + T (SchwartzMap.fourierMultiplierCLM (F := ℂ) (fun ξ : SpaceTime ↦ n2 ξ * n2 ξ) g) := by
                simpa [h2]
          _ = T g
                + T ((2 : ℝ) • SchwartzMap.fourierMultiplierCLM (F := ℂ) n2 g)
                + T (SchwartzMap.fourierMultiplierCLM (F := ℂ) (fun ξ : SpaceTime ↦ n2 ξ * n2 ξ) g) := by
                simp [add_assoc]
      -- finally, unfold `T` as `toLp`
      -- (both sides are now expressions in `T`; rewrite them to `.toLp`)
      simpa [T, SchwartzMap.toLpCLM_apply] using hEq'
    -- triangle inequality for a three-term sum (avoid misapplying `norm_add_le`)
    let a : Lp ℂ 2 (volume : Measure SpaceTime) :=
      g.toLp 2 (volume : Measure SpaceTime)
    let b : Lp ℂ 2 (volume : Measure SpaceTime) :=
      ((2 : ℝ) • SchwartzMap.fourierMultiplierCLM (F := ℂ) n2 g).toLp 2
        (volume : Measure SpaceTime)
    let c : Lp ℂ 2 (volume : Measure SpaceTime) :=
      (SchwartzMap.fourierMultiplierCLM (F := ℂ) (fun ξ : SpaceTime ↦ n2 ξ * n2 ξ) g).toLp 2
        (volume : Measure SpaceTime)
    have hab : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le a b
    have habc : ‖(a + b) + c‖ ≤ ‖a + b‖ + ‖c‖ := norm_add_le (a + b) c
    have hsum : ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
      have h' : ‖a + b + c‖ ≤ ‖a + b‖ + ‖c‖ := habc
      have h'' : ‖a + b‖ + ‖c‖ ≤ (‖a‖ + ‖b‖) + ‖c‖ :=
        add_le_add hab le_rfl
      exact le_trans h' h''
    simpa [this, a, b, c, add_assoc] using hsum

  -- rewrite the two multiplier terms via `Δ` and `Δ²`, and simplify scalar norms
  have hterm2 :
      ‖((2 : ℝ) • SchwartzMap.fourierMultiplierCLM (F := ℂ) n2 g).toLp 2
            (volume : Measure SpaceTime)‖
        = ((2 : ℝ) / ((2 * Real.pi) ^ 2)) * ‖(Δ g).toLp 2 (volume : Measure SpaceTime)‖ := by
    -- stay `ℝ`-linear throughout to avoid `ℝ`/`ℂ` coercion heartbeats
    let T' :
        TestFunctionℂ →L[ℝ] ↥(Lp ℂ 2 (volume : Measure SpaceTime)) :=
      SchwartzMap.toLpCLM (𝕜 := ℝ) (F := ℂ) (E := SpaceTime)
        (p := (2 : ℝ≥0∞)) (μ := (volume : Measure SpaceTime))
    have htoLpΔ :
        (((2 : ℝ) • SchwartzMap.fourierMultiplierCLM (F := ℂ) n2 g).toLp 2
              (volume : Measure SpaceTime))
          =
        ((2 : ℝ) * (-((2 * Real.pi) ^ 2 : ℝ))⁻¹) • (Δ g).toLp 2 (volume : Measure SpaceTime) := by
      -- rewrite the multiplier via `hmul2`, combine scalars, then move `smul` through `toLp`
      have :
          T' (((2 : ℝ) • SchwartzMap.fourierMultiplierCLM (F := ℂ) n2 g))
            =
          ((2 : ℝ) * (-((2 * Real.pi) ^ 2 : ℝ))⁻¹) • T' (Δ g) := by
        -- first rewrite `fourierMultiplierCLM … n2 g`
        rw [hmul2]
        -- push the two scalars through `T'` one at a time
        calc
          T' ((2 : ℝ) • ((-((2 * Real.pi) ^ 2 : ℝ))⁻¹ • Δ g))
              = (2 : ℝ) • T' ((-((2 * Real.pi) ^ 2 : ℝ))⁻¹ • Δ g) := by
                  simpa using (T'.map_smul (2 : ℝ) ((-((2 * Real.pi) ^ 2 : ℝ))⁻¹ • Δ g))
          _ = (2 : ℝ) • ((-((2 * Real.pi) ^ 2 : ℝ))⁻¹ • T' (Δ g)) := by
                  -- rewrite the inner `T'` using linearity
                  rw [T'.map_smul (-((2 * Real.pi) ^ 2 : ℝ))⁻¹ (Δ g)]
          _ = ((2 : ℝ) * (-((2 * Real.pi) ^ 2 : ℝ))⁻¹) • T' (Δ g) := by
                  -- combine the scalar factors
                  simpa [smul_smul, mul_assoc]
      simpa [T', SchwartzMap.toLpCLM_apply] using this
    -- take norms and compute the scalar factor
    have hpos : 0 < (2 * Real.pi : ℝ) ^ 2 := by
      have h2 : (0 : ℝ) < 2 := by norm_num
      have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
      have : (0 : ℝ) < 2 * Real.pi := mul_pos h2 hpi
      exact sq_pos_of_pos this
    have hscal :
        ‖(2 : ℝ) * (-((2 * Real.pi) ^ 2 : ℝ))⁻¹‖ = (2 : ℝ) / ((2 * Real.pi) ^ 2) := by
      -- `‖x‖ = |x|` in `ℝ`
      -- and `|(-a)⁻¹| = a⁻¹` for `a>0`.
      have habs : |(-((2 * Real.pi) ^ 2 : ℝ))⁻¹| = 1 / (2 * Real.pi) ^ 2 := by
        have ha : 0 < (2 * Real.pi : ℝ) ^ 2 := hpos
        calc
          |(-((2 * Real.pi) ^ 2 : ℝ))⁻¹| = |((2 * Real.pi : ℝ) ^ 2)⁻¹| := by simp
          _ = ((2 * Real.pi : ℝ) ^ 2)⁻¹ := by
                simpa [abs_of_pos (inv_pos.2 ha)]
          _ = 1 / (2 * Real.pi) ^ 2 := by simp [one_div]
      -- now finish
      calc
        ‖(2 : ℝ) * (-((2 * Real.pi) ^ 2 : ℝ))⁻¹‖
            = ‖(2 : ℝ)‖ * ‖(-((2 * Real.pi) ^ 2 : ℝ))⁻¹‖ := by
                simpa using (norm_mul (2 : ℝ) (-((2 * Real.pi) ^ 2 : ℝ))⁻¹)
        _ = |(2 : ℝ)| * |(-((2 * Real.pi) ^ 2 : ℝ))⁻¹| := by
                -- rewrite `‖·‖` as `|·|` without simplifying the `abs` terms further
                rw [Real.norm_eq_abs, Real.norm_eq_abs]
        _ = (2 : ℝ) * |(-((2 * Real.pi) ^ 2 : ℝ))⁻¹| := by
                have h2 : |(2 : ℝ)| = (2 : ℝ) := by simp
                -- only rewrite the `|2|` factor
                rw [h2]
        _ = (2 : ℝ) * (1 / (2 * Real.pi) ^ 2) := by
              -- multiply `habs` by the scalar `(2 : ℝ)`
              exact congrArg (fun t : ℝ => (2 : ℝ) * t) habs
        _ = (2 : ℝ) / ((2 * Real.pi) ^ 2) := by
              simp [div_eq_mul_inv, one_div, mul_assoc]
    -- avoid `calc`-step bookkeeping: rewrite to a scalar multiple, then take norms
    have hn :
        ‖((2 : ℝ) • SchwartzMap.fourierMultiplierCLM (F := ℂ) n2 g).toLp 2
              (volume : Measure SpaceTime)‖
          =
        ‖((2 : ℝ) * (-((2 * Real.pi) ^ 2 : ℝ))⁻¹)‖ *
          ‖(Δ g).toLp 2 (volume : Measure SpaceTime)‖ := by
      -- use `htoLpΔ` and `norm_smul`
      have hn0 :
          ‖((2 : ℝ) • SchwartzMap.fourierMultiplierCLM (F := ℂ) n2 g).toLp 2
                (volume : Measure SpaceTime)‖
            =
          ‖((2 : ℝ) * (-((2 * Real.pi) ^ 2 : ℝ))⁻¹) • (Δ g).toLp 2
                (volume : Measure SpaceTime)‖ :=
        congrArg (fun z : Lp ℂ 2 (volume : Measure SpaceTime) => ‖z‖) htoLpΔ
      -- rewrite `‖scalar • x‖` without simplifying the scalar norm (avoid `|π|`)
      exact hn0.trans (norm_smul ((2 : ℝ) * (-((2 * Real.pi) ^ 2 : ℝ))⁻¹)
        ((Δ g).toLp 2 (volume : Measure SpaceTime)))
    -- finish by rewriting the scalar norm using `hscal`
    -- (avoid any `calc.step` bookkeeping)
    have hmul :
        ‖((2 : ℝ) * (-((2 * Real.pi) ^ 2 : ℝ))⁻¹)‖ * ‖(Δ g).toLp 2 (volume : Measure SpaceTime)‖
          =
        ((2 : ℝ) / ((2 * Real.pi) ^ 2)) * ‖(Δ g).toLp 2 (volume : Measure SpaceTime)‖ :=
      congrArg
        (fun t : ℝ => t * ‖(Δ g).toLp 2 (volume : Measure SpaceTime)‖)
        hscal
    exact hn.trans hmul

  have hterm3 :
      ‖(SchwartzMap.fourierMultiplierCLM (F := ℂ) (fun ξ : SpaceTime ↦ n2 ξ * n2 ξ) g).toLp 2
            (volume : Measure SpaceTime)‖
        = (1 / ((2 * Real.pi) ^ 4)) * ‖(Δ (Δ g)).toLp 2 (volume : Measure SpaceTime)‖ := by
    -- stay `ℝ`-linear throughout (no coercions to `ℂ` scalars)
    let T :
        TestFunctionℂ →L[ℝ] ↥(Lp ℂ 2 (volume : Measure SpaceTime)) :=
      SchwartzMap.toLpCLM (𝕜 := ℝ) (F := ℂ) (E := SpaceTime)
        (p := (2 : ℝ≥0∞)) (μ := (volume : Measure SpaceTime))
    have htoLp :
        (SchwartzMap.fourierMultiplierCLM (F := ℂ) (fun ξ : SpaceTime ↦ n2 ξ * n2 ξ) g).toLp 2
            (volume : Measure SpaceTime)
          =
          (-((2 * Real.pi) ^ 2 : ℝ))⁻¹ • ((-((2 * Real.pi) ^ 2 : ℝ))⁻¹ • (Δ (Δ g)).toLp 2
              (volume : Measure SpaceTime)) := by
      have h := congrArg (fun u : TestFunctionℂ => T u) hmul4
      -- unfold `T` to rewrite back to `.toLp`
      simpa [T, SchwartzMap.toLpCLM_apply, map_smul] using h
    have hpos : 0 < (2 * Real.pi : ℝ) ^ 2 := by
      have h2 : (0 : ℝ) < 2 := by norm_num
      have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
      have : (0 : ℝ) < 2 * Real.pi := mul_pos h2 hpi
      exact sq_pos_of_pos this
    have habs : |(-((2 * Real.pi) ^ 2 : ℝ))⁻¹| = 1 / (2 * Real.pi) ^ 2 := by
      have ha : 0 < (2 * Real.pi : ℝ) ^ 2 := hpos
      calc
        |(-((2 * Real.pi) ^ 2 : ℝ))⁻¹| = |((2 * Real.pi : ℝ) ^ 2)⁻¹| := by simp
        _ = ((2 * Real.pi : ℝ) ^ 2)⁻¹ := by
              simpa [abs_of_pos (inv_pos.2 ha)]
        _ = 1 / (2 * Real.pi) ^ 2 := by simp [one_div]
    have hscal : ‖(-((2 * Real.pi) ^ 2 : ℝ))⁻¹‖ = 1 / (2 * Real.pi) ^ 2 := by
      -- `‖x‖ = |x|` in `ℝ`
      rw [Real.norm_eq_abs]
      exact habs
    -- take norms, use `norm_smul` twice, and compute the scalar square
    have htoLp_norm :
        ‖(SchwartzMap.fourierMultiplierCLM (F := ℂ) (fun ξ : SpaceTime ↦ n2 ξ * n2 ξ) g).toLp 2
              (volume : Measure SpaceTime)‖
          =
        ‖(-((2 * Real.pi) ^ 2 : ℝ))⁻¹‖ *
          (‖(-((2 * Real.pi) ^ 2 : ℝ))⁻¹‖ *
            ‖(Δ (Δ g)).toLp 2 (volume : Measure SpaceTime)‖) := by
      -- rewrite using `htoLp`, then peel norms with `norm_smul`
      have hn0 :
          ‖(SchwartzMap.fourierMultiplierCLM (F := ℂ) (fun ξ : SpaceTime ↦ n2 ξ * n2 ξ) g).toLp 2
                (volume : Measure SpaceTime)‖
            =
          ‖(-((2 * Real.pi) ^ 2 : ℝ))⁻¹ •
              ((-((2 * Real.pi) ^ 2 : ℝ))⁻¹ • (Δ (Δ g)).toLp 2 (volume : Measure SpaceTime))‖ :=
        congrArg (fun z : Lp ℂ 2 (volume : Measure SpaceTime) => ‖z‖) htoLp
      -- apply `norm_smul` twice without `calc` (avoids `calc.step` goals)
      have hs1 :
          ‖(-((2 * Real.pi) ^ 2 : ℝ))⁻¹ •
              ((-((2 * Real.pi) ^ 2 : ℝ))⁻¹ • (Δ (Δ g)).toLp 2 (volume : Measure SpaceTime))‖
            =
          ‖(-((2 * Real.pi) ^ 2 : ℝ))⁻¹‖ *
              ‖(-((2 * Real.pi) ^ 2 : ℝ))⁻¹ • (Δ (Δ g)).toLp 2 (volume : Measure SpaceTime)‖ :=
        norm_smul _ _
      have hs2 :
          ‖(-((2 * Real.pi) ^ 2 : ℝ))⁻¹‖ *
                ‖(-((2 * Real.pi) ^ 2 : ℝ))⁻¹ • (Δ (Δ g)).toLp 2 (volume : Measure SpaceTime)‖
            =
          ‖(-((2 * Real.pi) ^ 2 : ℝ))⁻¹‖ *
              (‖(-((2 * Real.pi) ^ 2 : ℝ))⁻¹‖ *
                ‖(Δ (Δ g)).toLp 2 (volume : Measure SpaceTime)‖) :=
        congrArg
          (fun t : ℝ => ‖(-((2 * Real.pi) ^ 2 : ℝ))⁻¹‖ * t)
          (norm_smul (-((2 * Real.pi) ^ 2 : ℝ))⁻¹
            ((Δ (Δ g)).toLp 2 (volume : Measure SpaceTime)))
      exact hn0.trans (hs1.trans hs2)
    have hprod :
        ‖(-((2 * Real.pi) ^ 2 : ℝ))⁻¹‖ * ‖(-((2 * Real.pi) ^ 2 : ℝ))⁻¹‖
          = 1 / ((2 * Real.pi) ^ 4) := by
      -- rewrite both factors using `hscal` and the elementary identity `(1/a^2)^2 = 1/a^4`
      -- first reduce to `(1/(2π)^2) * (1/(2π)^2)`
      rw [hscal]
      -- discharge the remaining scalar identity explicitly
      -- (keep it elementary to avoid `simp` rewriting `|π|`)
      -- now compute the product
      have hmul : (2 : ℕ) * 2 = 4 := by norm_num
      set a : ℝ := (2 * Real.pi) with ha
      have : (1 / a ^ 2) * (1 / a ^ 2) = 1 / a ^ 4 := by
        calc
          (1 / a ^ 2) * (1 / a ^ 2) = (a ^ 2)⁻¹ * (a ^ 2)⁻¹ := by
            simp [one_div]
          _ = ((a ^ 2)⁻¹) ^ 2 := by
            symm
            simp [pow_two]
          _ = ((a ^ 2) ^ 2)⁻¹ := by
            simpa using (inv_pow (a ^ 2) 2)
          _ = (a ^ 4)⁻¹ := by
            have : (a ^ 2) ^ 2 = a ^ 4 := by
              calc
                (a ^ 2) ^ 2 = a ^ ((2 : ℕ) * 2) := by
                  simpa using (pow_mul a 2 2).symm
                _ = a ^ 4 := by simpa [hmul]
            simpa [this]
          _ = 1 / a ^ 4 := by
            simp [one_div]
      simpa [ha] using this
    -- assemble without `calc` (avoids `calc.step` goal bookkeeping)
    have hassoc :
        ‖(-((2 * Real.pi) ^ 2 : ℝ))⁻¹‖ *
              (‖(-((2 * Real.pi) ^ 2 : ℝ))⁻¹‖ *
                ‖(Δ (Δ g)).toLp 2 (volume : Measure SpaceTime)‖)
            =
          (‖(-((2 * Real.pi) ^ 2 : ℝ))⁻¹‖ * ‖(-((2 * Real.pi) ^ 2 : ℝ))⁻¹‖) *
            ‖(Δ (Δ g)).toLp 2 (volume : Measure SpaceTime)‖ :=
      (mul_assoc _ _ _).symm
    have hmul :
        (‖(-((2 * Real.pi) ^ 2 : ℝ))⁻¹‖ * ‖(-((2 * Real.pi) ^ 2 : ℝ))⁻¹‖) *
              ‖(Δ (Δ g)).toLp 2 (volume : Measure SpaceTime)‖
            =
          (1 / ((2 * Real.pi) ^ 4)) * ‖(Δ (Δ g)).toLp 2 (volume : Measure SpaceTime)‖ :=
      congrArg
        (fun t : ℝ => t * ‖(Δ (Δ g)).toLp 2 (volume : Measure SpaceTime)‖)
        hprod
    have hfinal :
        ‖(-((2 * Real.pi) ^ 2 : ℝ))⁻¹‖ *
              (‖(-((2 * Real.pi) ^ 2 : ℝ))⁻¹‖ *
                ‖(Δ (Δ g)).toLp 2 (volume : Measure SpaceTime)‖)
            =
          (1 / ((2 * Real.pi) ^ 4)) * ‖(Δ (Δ g)).toLp 2 (volume : Measure SpaceTime)‖ :=
      Eq.trans hassoc hmul
    exact Eq.trans htoLp_norm hfinal

  -- finish by rewriting `htri` using `hterm2` and `hterm3`
  have htri' := htri
  rw [hterm2, hterm3] at htri'
  simpa [one_mul, add_assoc] using htri'

set_option maxHeartbeats 800000 in
theorem schwartz_seminorm0_le_coeffSeminormSeq_four (ξ : ℝ) (hξ : ξ ≠ 0) :
    ∃ C : ℝ≥0, ∀ f : TestFunction,
      SchwartzMap.seminorm ℝ 0 0 f ≤ ((C : ℝ≥0) • (coeffSeminormSeq ξ hξ 4)) f := by
  -- Fix the Fourier weight constants.
  set wInv : SpaceTime → ℂ := fun ξ : SpaceTime ↦ (((((1 : ℝ) + ‖ξ‖ ^ 2) ^ (-2 : ℝ)) : ℝ) : ℂ)
  set A : ℝ :=
    ((∫ ξ : SpaceTime, ‖wInv ξ‖ ^ (2 : ℝ) ∂(volume : Measure SpaceTime)) ^ (1 / (2 : ℝ)))
  have hA0 : 0 ≤ A := by
    have hInt :
        0 ≤ ∫ ξ : SpaceTime, ‖wInv ξ‖ ^ (2 : ℝ) ∂(volume : Measure SpaceTime) := by
      refine MeasureTheory.integral_nonneg ?_
      intro ξ'
      positivity
    dsimp [A]
    exact Real.rpow_nonneg hInt _

  -- A Sobolev-type constant, coming from bounding the `L²` multiplier norm by `Δ`-graph norms.
  -- We keep the numerical constant opaque: it only needs to depend on `ξ`.
  -- constants for one coordinate derivative step, at the relevant coefficient indices
  let d : ℕ → ℝ := coeffDerivConst ξ
  -- crude (dimension-dependent) bounds for `‖Δ f‖_{L²}` and `‖Δ² f‖_{L²}`
  -- (we keep the dimension as `Fintype.card` to avoid rewriting `STDimension = 4` repeatedly)
  let CΔ : ℝ := (Fintype.card (Fin STDimension) : ℝ) * (d 0) * (d 1)
  let CΔΔ : ℝ := (Fintype.card (Fin STDimension) : ℝ) ^ 2 * (d 0) * (d 1) * (d 2) * (d 3)
  -- Sobolev constant for the Fourier-weight `((1 + ‖·‖^2)^2)`.
  -- The factors `((2 * π)^2)⁻¹` and `((2 * π)^4)⁻¹` come from converting `‖·‖^2` and `‖·‖^4`
  -- multipliers to Laplacian iterates using `SchwartzMap.laplacian_eq_fourierMultiplierCLM`.
  let Csob : ℝ :=
    (1 : ℝ)
      + ((2 : ℝ) / ((2 * Real.pi) ^ 2)) * CΔ
      + ((2 * Real.pi) ^ 4)⁻¹ * CΔΔ

  have hd0 : 0 ≤ d 0 := by
    dsimp [d, coeffDerivConst]; positivity
  have hd1 : 0 ≤ d 1 := by
    dsimp [d, coeffDerivConst]; positivity
  have hd2 : 0 ≤ d 2 := by
    dsimp [d, coeffDerivConst]; positivity
  have hd3 : 0 ≤ d 3 := by
    dsimp [d, coeffDerivConst]; positivity
  have hCΔ0 : 0 ≤ CΔ := by
    dsimp [CΔ]; positivity
  have hCΔΔ0 : 0 ≤ CΔΔ := by
    dsimp [CΔΔ]; positivity
  have hCsob0 : 0 ≤ Csob := by
    dsimp [Csob]
    positivity

  refine ⟨Real.toNNReal (Csob * A), ?_⟩
  intro f
  -- Reduce to a pointwise bound.
  have hbound :
      ∀ x : SpaceTime, ‖x‖ ^ (0 : ℕ) * ‖iteratedFDeriv ℝ (0 : ℕ) f x‖ ≤
        (A * Csob) * coeffSeminormSeq ξ hξ 4 f := by
    intro x
    simp only [pow_zero, one_mul, norm_iteratedFDeriv_zero]
    -- Work with the complexification `g`.
    let g : TestFunctionℂ := OSforGFF.ofRealSchwartz f
    have hx0 : ‖f x‖ = ‖g x‖ := by
      simp [g, OSforGFF.ofRealSchwartz_apply]
    -- Fourier inversion + weighted Cauchy–Schwarz.
    have hx1 : ‖g x‖ ≤ ∫ ξ : SpaceTime, ‖(𝓕 g) ξ‖ ∂(volume : Measure SpaceTime) :=
      norm_le_integral_norm_fourier g x
    have hx2 :
        (∫ ξ : SpaceTime, ‖(𝓕 g) ξ‖ ∂(volume : Measure SpaceTime)) ≤
          A *
            ((∫ ξ : SpaceTime,
                  ‖(((((1 : ℝ) + ‖ξ‖ ^ 2) ^ (2 : ℝ)) : ℝ) : ℂ) • (𝓕 g) ξ‖ ^ (2 : ℝ)
                ∂(volume : Measure SpaceTime)) ^ (1 / (2 : ℝ))) := by
      simpa [A, wInv] using (integral_norm_fourier_le_weighted_L2 (g := g))
    have hx3 :
        ‖g x‖ ≤
          A *
            ((∫ ξ : SpaceTime,
                  ‖(((((1 : ℝ) + ‖ξ‖ ^ 2) ^ (2 : ℝ)) : ℝ) : ℂ) • (𝓕 g) ξ‖ ^ (2 : ℝ)
                ∂(volume : Measure SpaceTime)) ^ (1 / (2 : ℝ))) :=
      le_trans hx1 hx2

    -- Convert the second factor into an `L²` norm.
    have hw_growth :
        (fun ξ : SpaceTime ↦ (((((1 : ℝ) + ‖ξ‖ ^ 2) ^ (2 : ℝ)) : ℝ) : ℂ)).HasTemperateGrowth := by
      fun_prop
    let hW : TestFunctionℂ :=
      SchwartzMap.smulLeftCLM (F := ℂ)
        (fun ξ : SpaceTime ↦ (((((1 : ℝ) + ‖ξ‖ ^ 2) ^ (2 : ℝ)) : ℝ) : ℂ)) (𝓕 g)
    have hW_apply (ξ' : SpaceTime) :
        hW ξ' =
          (((((1 : ℝ) + ‖ξ'‖ ^ 2) ^ (2 : ℝ)) : ℝ) : ℂ) * (𝓕 g) ξ' := by
      simpa [hW, smul_eq_mul] using
        (SchwartzMap.smulLeftCLM_apply_apply (F := ℂ)
          (g := fun ξ : SpaceTime ↦ (((((1 : ℝ) + ‖ξ‖ ^ 2) ^ (2 : ℝ)) : ℝ) : ℂ))
          hw_growth (𝓕 g) ξ')
    have hB :
        ((∫ ξ : SpaceTime,
              ‖(((((1 : ℝ) + ‖ξ‖ ^ 2) ^ (2 : ℝ)) : ℝ) : ℂ) • (𝓕 g) ξ‖ ^ (2 : ℝ)
            ∂(volume : Measure SpaceTime)) ^ (1 / (2 : ℝ)))
          = ‖hW.toLp 2 (volume : Measure SpaceTime)‖ := by
      have hint :
          (∫ ξ : SpaceTime,
                ‖(((((1 : ℝ) + ‖ξ‖ ^ 2) ^ (2 : ℝ)) : ℝ) : ℂ) • (𝓕 g) ξ‖ ^ (2 : ℝ)
              ∂(volume : Measure SpaceTime))
            =
            ∫ ξ : SpaceTime, ‖hW ξ‖ ^ (2 : ℝ) ∂(volume : Measure SpaceTime) := by
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards with ξ'
        simp [hW_apply, smul_eq_mul]
      have hLp :
          (∫ ξ : SpaceTime, ‖hW ξ‖ ^ (2 : ℝ) ∂(volume : Measure SpaceTime)) ^ (1 / (2 : ℝ))
            =
            ‖hW.toLp 2 (volume : Measure SpaceTime)‖ :=
        integral_norm_rpow_two_rpow_inv_eq_norm_toLp (h := hW)
      calc
        ((∫ ξ : SpaceTime,
              ‖(((((1 : ℝ) + ‖ξ‖ ^ 2) ^ (2 : ℝ)) : ℝ) : ℂ) • (𝓕 g) ξ‖ ^ (2 : ℝ)
            ∂(volume : Measure SpaceTime)) ^ (1 / (2 : ℝ)))
            =
            ((∫ ξ : SpaceTime, ‖hW ξ‖ ^ (2 : ℝ) ∂(volume : Measure SpaceTime)) ^ (1 / (2 : ℝ))) := by
              rw [hint]
        _ = ‖hW.toLp 2 (volume : Measure SpaceTime)‖ := hLp

    -- rewrite the Hölder term as an `L²` norm
    have hx4 : ‖g x‖ ≤ A * ‖hW.toLp 2 (volume : Measure SpaceTime)‖ := by
      -- avoid `simp`: `hx3` simplifies the integrand, but `hB` is stated for the unsimplified one
      have hx3' := hx3
      -- rewrite the `((∫ …) ^ (1/2))` term using `hB`
      -- (this is purely a definitional rewrite, no simp-normalization)
      rw [hB] at hx3'
      exact hx3'

    -- Bound the `L²` norm of `hW` by coefficient seminorms (Plancherel + derivative ladder bounds).
    have hW_le : ‖hW.toLp 2 (volume : Measure SpaceTime)‖ ≤ Csob * coeffSeminormSeq ξ hξ 4 f := by
      -- We will convert `hW` to a Fourier transform of a polynomial in `Δ`, then bound `Δ`-iterates
      -- by repeated coordinate-derivative bounds in `coeffSeminormSeq`.
      -- (Implementation continues below.)
      -- Reduce to the physical-space Fourier multiplier via Plancherel.
      let w : SpaceTime → ℝ := sobolevWeight
      let h : TestFunctionℂ := SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) w g
      have hFourier : 𝓕 h = hW := by
        -- `𝓕 (fourierMultiplier w g) = w • (𝓕 g)` by definition.
        -- Avoid `simp` here: `fourier_fourierMultiplierCLM` is a `[simp]` lemma, so `simp` can
        -- simplify its own statement to `True`.
        have hfour :
            𝓕 h = (SchwartzMap.smulLeftCLM (F := ℂ) w) (𝓕 g) := by
          -- unfold `h`, then apply the Fourier-multiplier identity
          dsimp [h]
          exact (SchwartzMap.fourier_fourierMultiplierCLM (𝕜 := ℝ) (F := (ℂ)) (g := w) (f := g))
        -- rewrite the RHS into the complex-valued weight used to define `hW`
        have hw' :
            (SchwartzMap.smulLeftCLM (F := ℂ) w) (𝓕 g) = hW := by
          -- `smulLeftCLM` with a real-valued symbol agrees with `smulLeftCLM` for its `ℂ`-cast
          -- (use the standard `ofReal` lemma).
          -- Here the cast is `fun ξ ↦ (w ξ : ℂ)`.
          -- `fun_prop` does not see through the local `let w := sobolevWeight`, so unfold it.
          have hwg : Function.HasTemperateGrowth w := by
            -- `sobolevWeight` is opaque, so unfold it explicitly.
            dsimp [w]
            simpa [sobolevWeight] using
              (by
                fun_prop : Function.HasTemperateGrowth (fun ξ : SpaceTime ↦ (1 + ‖ξ‖ ^ 2) ^ 2))
          simpa [hW, w, sobolevWeight] using
            (SchwartzMap.smulLeftCLM_ofReal (𝕜' := ℂ) (F := (ℂ)) (g := w) (hg := hwg)
              (f := (𝓕 g))).symm
        exact hfour.trans hw'
      have hPlanch : ‖hW.toLp 2 (volume : Measure SpaceTime)‖ = ‖h.toLp 2 (volume : Measure SpaceTime)‖ := by
        -- `‖𝓕 h‖₂ = ‖h‖₂` and `𝓕 h = hW`.
        have := (SchwartzMap.norm_fourier_toL2_eq (f := h))
        -- `toLp` uses `volume` by default, so this is definitional.
        simpa [hFourier] using this
      -- It suffices to bound the `L²` norm of `h`.
      rw [hPlanch]

      -- A helper: `‖f‖₂` is controlled by `coeffSeminormSeq .. 4 f` via monotonicity.
      have hmono : Monotone (coeffSeminormSeq ξ hξ) := coeffSeminormSeq_mono ξ hξ
      have hL2_le_coeff4 : ‖f.toLp 2 (volume : Measure SpaceTime)‖ ≤ coeffSeminormSeq ξ hξ 4 f := by
        -- identify `‖f‖₂` with `coeffSeminormSeq .. 0 f`
        have hf0 :
            coeffSeminormSeq ξ hξ 0 f = ‖f.toLp 2 (volume : Measure SpaceTime)‖ := by
          -- avoid `simp` on the full lemma (can be expensive); only rewrite `k = 0` explicitly
          have hf0' :=
            coeffSeminormSeq_eq_norm_toLp_numAllPowCLM (ξ := ξ) (hξ := hξ) (k := 0) (f := f)
          -- `numAllPowCLM ξ 0 = 1`, hence `numAllPowCLM ξ 0 f = f`
          rw [numAllPowCLM_zero (ξ := ξ)] at hf0'
          -- `1` is the identity continuous linear map
          -- (avoid `simp` on the full expression: it can unfold `coeffSeminormSeq`)
          rw [ContinuousLinearMap.one_apply] at hf0'
          exact hf0'
        -- now use monotonicity `0 ≤ 4`
        have h04 : coeffSeminormSeq ξ hξ 0 f ≤ coeffSeminormSeq ξ hξ 4 f := hmono (Nat.zero_le 4) f
        -- rewrite `coeffSeminormSeq .. 0 f` into `‖f‖₂` without `simp`
        have h04' : ‖f.toLp 2 (volume : Measure SpaceTime)‖ ≤ coeffSeminormSeq ξ hξ 4 f := by
          calc
            ‖f.toLp 2 (volume : Measure SpaceTime)‖ = coeffSeminormSeq ξ hξ 0 f := hf0.symm
            _ ≤ coeffSeminormSeq ξ hξ 4 f := h04
        exact h04'

      -- Bound `‖Δ f‖₂` by `CΔ * coeffSeminormSeq .. 4 f`.
      have hL2Δ_le : ‖(Δ f).toLp 2 (volume : Measure SpaceTime)‖ ≤ CΔ * coeffSeminormSeq ξ hξ 4 f := by
        -- rewrite `‖·‖₂` as `coeffSeminormSeq .. 0`
        have hL2_as_coeff0 (u : TestFunction) :
            ‖u.toLp 2 (volume : Measure SpaceTime)‖ = coeffSeminormSeq ξ hξ 0 u := by
          have hu :=
            coeffSeminormSeq_eq_norm_toLp_numAllPowCLM (ξ := ξ) (hξ := hξ) (k := 0) (f := u)
          rw [numAllPowCLM_zero (ξ := ξ)] at hu
          rw [ContinuousLinearMap.one_apply] at hu
          exact hu.symm
        have h24 : coeffSeminormSeq ξ hξ 2 f ≤ coeffSeminormSeq ξ hξ 4 f := hmono (by decide) f
        have hcoeff :
            coeffSeminormSeq ξ hξ 0 (Δ f) ≤ CΔ * coeffSeminormSeq ξ hξ 4 f := by
          -- Laplacian bound at level `0`, then monotonicity `2 ≤ 4`
          have hΔ0 :
              coeffSeminormSeq ξ hξ 0 (Δ f) ≤
                (Fintype.card (Fin STDimension) : ℝ) * (d 0) * (d 1) * coeffSeminormSeq ξ hξ 2 f := by
            -- avoid `simp`: only unfold the local abbreviations and simplify Nat arithmetic
            dsimp [d]
            have h :=
              (coeffSeminormSeq_laplacian_le (ξ := ξ) (hξ := hξ) (k := 0) (f := f))
            simp only [Nat.zero_add] at h
            exact h
          have hdd : 0 ≤ (Fintype.card (Fin STDimension) : ℝ) * (d 0) * (d 1) := by
            -- unfold `CΔ` in the already-proved nonnegativity lemma
            have h := hCΔ0
            dsimp [CΔ] at h
            exact h
          have hΔ0' :
              (Fintype.card (Fin STDimension) : ℝ) * (d 0) * (d 1) * coeffSeminormSeq ξ hξ 2 f
                ≤ (Fintype.card (Fin STDimension) : ℝ) * (d 0) * (d 1) * coeffSeminormSeq ξ hξ 4 f := by
            exact mul_le_mul_of_nonneg_left h24 hdd
          have : coeffSeminormSeq ξ hξ 0 (Δ f) ≤
              (Fintype.card (Fin STDimension) : ℝ) * (d 0) * (d 1) * coeffSeminormSeq ξ hξ 4 f :=
            le_trans hΔ0 hΔ0'
          -- rewrite `CΔ` and close by definitional equality
          dsimp [CΔ]
          exact this
        -- convert back to `‖·‖₂`
        -- avoid `simp` on `hL2_as_coeff0`: rewrite explicitly
        calc
          ‖(Δ f).toLp 2 (volume : Measure SpaceTime)‖
              = coeffSeminormSeq ξ hξ 0 (Δ f) := by
                exact (hL2_as_coeff0 (u := Δ f))
          _ ≤ CΔ * coeffSeminormSeq ξ hξ 4 f := hcoeff

      -- Bound `‖Δ² f‖₂` similarly.
      have hL2ΔΔ_le :
          ‖(Δ (Δ f)).toLp 2 (volume : Measure SpaceTime)‖ ≤ CΔΔ * coeffSeminormSeq ξ hξ 4 f := by
        have hL2_as_coeff0 (u : TestFunction) :
            ‖u.toLp 2 (volume : Measure SpaceTime)‖ = coeffSeminormSeq ξ hξ 0 u := by
          have hu :=
            coeffSeminormSeq_eq_norm_toLp_numAllPowCLM (ξ := ξ) (hξ := hξ) (k := 0) (f := u)
          rw [numAllPowCLM_zero (ξ := ξ)] at hu
          rw [ContinuousLinearMap.one_apply] at hu
          exact hu.symm
        -- apply the Laplacian bound twice: at levels `0` and `2`
        have h0 :
            coeffSeminormSeq ξ hξ 0 (Δ (Δ f)) ≤
              (Fintype.card (Fin STDimension) : ℝ) * (d 0) * (d 1) * coeffSeminormSeq ξ hξ 2 (Δ f) := by
          -- avoid `simp`: only unfold the local abbreviations and simplify Nat arithmetic
          dsimp [d]
          have h :=
            (coeffSeminormSeq_laplacian_le (ξ := ξ) (hξ := hξ) (k := 0) (f := Δ f))
          simp only [Nat.zero_add] at h
          exact h
        have h2 :
            coeffSeminormSeq ξ hξ 2 (Δ f) ≤
              (Fintype.card (Fin STDimension) : ℝ) * (d 2) * (d 3) * coeffSeminormSeq ξ hξ 4 f := by
          -- avoid `simp`: only unfold the local abbreviations
          dsimp [d]
          exact (coeffSeminormSeq_laplacian_le (ξ := ξ) (hξ := hξ) (k := 2) (f := f))
        have hcoeff :
            coeffSeminormSeq ξ hξ 0 (Δ (Δ f)) ≤ CΔΔ * coeffSeminormSeq ξ hξ 4 f := by
          have hdd0 : 0 ≤ (Fintype.card (Fin STDimension) : ℝ) * (d 0) * (d 1) := by
            have h := hCΔ0
            dsimp [CΔ] at h
            exact h
          have h0' :
              (Fintype.card (Fin STDimension) : ℝ) * (d 0) * (d 1) * coeffSeminormSeq ξ hξ 2 (Δ f)
                ≤ (Fintype.card (Fin STDimension) : ℝ) * (d 0) * (d 1) *
                    ((Fintype.card (Fin STDimension) : ℝ) * (d 2) * (d 3) * coeffSeminormSeq ξ hξ 4 f) := by
            exact mul_le_mul_of_nonneg_left h2 hdd0
          have : coeffSeminormSeq ξ hξ 0 (Δ (Δ f)) ≤
              ((Fintype.card (Fin STDimension) : ℝ) ^ 2 * (d 0) * (d 1) * (d 2) * (d 3)) *
                coeffSeminormSeq ξ hξ 4 f := by
            -- chain and reassociate
            refine le_trans h0 ?_
            -- rewrite the RHS of `h0'` and normalize products
            -- normalize the scalar product; avoid heavy `simp` by using `ring`
            have hscal :
                (Fintype.card (Fin STDimension) : ℝ) * (d 0) * (d 1) *
                    ((Fintype.card (Fin STDimension) : ℝ) * (d 2) * (d 3) * coeffSeminormSeq ξ hξ 4 f)
                  =
                  ((Fintype.card (Fin STDimension) : ℝ) ^ 2 * (d 0) * (d 1) * (d 2) * (d 3)) *
                    coeffSeminormSeq ξ hξ 4 f := by
              -- `ring` is faster here than `simp` with commutativity
              ring
            -- rewrite the RHS of `h0'` using `hscal` (avoid `simp`)
            have h0'' := h0'
            rw [hscal] at h0''
            exact h0''
          dsimp [CΔΔ]
          exact this
        -- convert back to `‖·‖₂`
        -- avoid `simp` on `hL2_as_coeff0`: rewrite explicitly
        calc
          ‖(Δ (Δ f)).toLp 2 (volume : Measure SpaceTime)‖
              = coeffSeminormSeq ξ hξ 0 (Δ (Δ f)) := by
                exact (hL2_as_coeff0 (u := Δ (Δ f)))
          _ ≤ CΔΔ * coeffSeminormSeq ξ hξ 4 f := hcoeff

      -- Now control `‖h‖₂` by the graph norms `‖f‖₂`, `‖Δ f‖₂`, `‖Δ² f‖₂`.
      -- Rewrite the multiplier polynomially and bound by the triangle inequality.
      have hbound_h :
          ‖h.toLp 2 (volume : Measure SpaceTime)‖ ≤
            (1 : ℝ) * ‖g.toLp 2 (volume : Measure SpaceTime)‖
              + ((2 : ℝ) / ((2 * Real.pi) ^ 2)) * ‖(Δ g).toLp 2 (volume : Measure SpaceTime)‖
              + (1 / ((2 * Real.pi) ^ 4)) * ‖(Δ (Δ g)).toLp 2 (volume : Measure SpaceTime)‖ := by
        -- Reuse the global Sobolev bound lemma.
        -- Avoid `simp`: rewrite the left-hand side explicitly.
        -- (This prevents large definitional reductions from exhausting the default heartbeat budget.)
        have h' :=
          (norm_toLp_fourierMultiplierCLM_sobolevWeight_le (g := g))
        -- `h = fourierMultiplierCLM .. w g` and `w = sobolevWeight` by definition.
        -- Rewrite the LHS of `h'` into `‖h.toLp 2‖`.
        simpa [h, w] using h'


      -- Transfer `g` and its Laplacian iterates back to the real function `f`.
      have hgL2 : ‖g.toLp 2 (volume : Measure SpaceTime)‖ ≤ coeffSeminormSeq ξ hξ 4 f := by
        -- `‖g‖₂ = ‖f‖₂` and `‖f‖₂ ≤ coeffSeminormSeq .. 4 f`.
        simpa [g] using (le_trans (by
          simpa [g] using (norm_toLp_ofRealSchwartz_eq (f := f)).le) hL2_le_coeff4)
      have hΔg :
          ‖(Δ g).toLp 2 (volume : Measure SpaceTime)‖ ≤ CΔ * coeffSeminormSeq ξ hξ 4 f := by
        -- commute `Δ` with complexification and use `hL2Δ_le`
        have : Δ g = OSforGFF.ofRealSchwartz (Δ f) := by
          simpa [g] using (laplacian_ofReal_eq (f := f))
        -- compare L² norms
        have hnorm : ‖(Δ g).toLp 2 (volume : Measure SpaceTime)‖ = ‖(Δ f).toLp 2 (volume : Measure SpaceTime)‖ := by
          -- rewrite and use the norm comparison lemma
          simpa [this] using (norm_toLp_ofRealSchwartz_eq (f := Δ f))
        simpa [hnorm] using hL2Δ_le
      have hΔΔg :
          ‖(Δ (Δ g)).toLp 2 (volume : Measure SpaceTime)‖ ≤ CΔΔ * coeffSeminormSeq ξ hξ 4 f := by
        have hΔg' : Δ g = OSforGFF.ofRealSchwartz (Δ f) := by
          simpa [g] using (laplacian_ofReal_eq (f := f))
        have : Δ (Δ g) = OSforGFF.ofRealSchwartz (Δ (Δ f)) := by
          -- apply `laplacian_ofReal_eq` to `Δ f`, after rewriting `Δ g`
          simpa [hΔg'] using (laplacian_ofReal_eq (f := Δ f))
        have hnorm : ‖(Δ (Δ g)).toLp 2 (volume : Measure SpaceTime)‖ =
            ‖(Δ (Δ f)).toLp 2 (volume : Measure SpaceTime)‖ := by
          simpa [this] using (norm_toLp_ofRealSchwartz_eq (f := Δ (Δ f)))
        simpa [hnorm] using hL2ΔΔ_le

      -- Combine everything and match the definition of `Csob`.
      -- `hbound_h` gives the analytic inequality, then we bound each term by `coeffSeminormSeq .. 4 f`.
      -- (The coefficients are chosen so that the final constant is exactly `Csob`.)
      have : ‖h.toLp 2 (volume : Measure SpaceTime)‖ ≤ Csob * coeffSeminormSeq ξ hξ 4 f := by
        -- use `hbound_h` and substitute the three bounds.
        -- Note: `Csob = 1 + (2/(2π)^2)*CΔ + (1/(2π)^4)*CΔΔ`.
        -- We keep the arithmetic explicit.
        have hnonneg : 0 ≤ coeffSeminormSeq ξ hξ 4 f := by positivity
        have h1 :
            (1 : ℝ) * ‖g.toLp 2 (volume : Measure SpaceTime)‖
              + ((2 : ℝ) / ((2 * Real.pi) ^ 2)) * ‖(Δ g).toLp 2 (volume : Measure SpaceTime)‖
              + ((2 * Real.pi) ^ 4)⁻¹ * ‖(Δ (Δ g)).toLp 2 (volume : Measure SpaceTime)‖
              ≤
            (1 : ℝ) * coeffSeminormSeq ξ hξ 4 f
              + ((2 : ℝ) / ((2 * Real.pi) ^ 2)) * (CΔ * coeffSeminormSeq ξ hξ 4 f)
              + ((2 * Real.pi) ^ 4)⁻¹ * (CΔΔ * coeffSeminormSeq ξ hξ 4 f) := by
          have hA :
              (1 : ℝ) * ‖g.toLp 2 (volume : Measure SpaceTime)‖
                ≤ (1 : ℝ) * coeffSeminormSeq ξ hξ 4 f := by
            simpa [one_mul] using hgL2
          have hB :
              ((2 : ℝ) / ((2 * Real.pi) ^ 2)) * ‖(Δ g).toLp 2 (volume : Measure SpaceTime)‖
                ≤ ((2 : ℝ) / ((2 * Real.pi) ^ 2)) * (CΔ * coeffSeminormSeq ξ hξ 4 f) := by
            exact mul_le_mul_of_nonneg_left hΔg (by positivity)
          have hC :
              ((2 * Real.pi) ^ 4)⁻¹ * ‖(Δ (Δ g)).toLp 2 (volume : Measure SpaceTime)‖
                ≤ ((2 * Real.pi) ^ 4)⁻¹ * (CΔΔ * coeffSeminormSeq ξ hξ 4 f) := by
            exact mul_le_mul_of_nonneg_left hΔΔg (by positivity)
          -- add the three inequalities (note: `a + b + c` is left-associated)
          have hAB :
              (1 : ℝ) * ‖g.toLp 2 (volume : Measure SpaceTime)‖
                  + ((2 : ℝ) / ((2 * Real.pi) ^ 2)) * ‖(Δ g).toLp 2 (volume : Measure SpaceTime)‖
                ≤
                (1 : ℝ) * coeffSeminormSeq ξ hξ 4 f
                  + ((2 : ℝ) / ((2 * Real.pi) ^ 2)) * (CΔ * coeffSeminormSeq ξ hξ 4 f) :=
            add_le_add hA hB
          exact (add_le_add hAB hC)
        have h2 : ‖h.toLp 2 (volume : Measure SpaceTime)‖ ≤
            (1 : ℝ) * coeffSeminormSeq ξ hξ 4 f
              + ((2 : ℝ) / ((2 * Real.pi) ^ 2)) * (CΔ * coeffSeminormSeq ξ hξ 4 f)
              + ((2 * Real.pi) ^ 4)⁻¹ * (CΔΔ * coeffSeminormSeq ξ hξ 4 f) := by
          -- rewrite `1 / _` in `hbound_h` as `(_ : ℝ)⁻¹` to match `h1`
          exact le_trans (by simpa [one_div] using hbound_h) h1
        -- factor out `coeffSeminormSeq .. 4 f` and match the definition of `Csob`
        have : ‖h.toLp 2 (volume : Measure SpaceTime)‖ ≤
            ((1 : ℝ)
                + ((2 : ℝ) / ((2 * Real.pi) ^ 2)) * CΔ
                + ((2 * Real.pi) ^ 4)⁻¹ * CΔΔ) * coeffSeminormSeq ξ hξ 4 f := by
          -- purely algebraic: factor `coeffSeminormSeq .. 4 f` out of the RHS of `h2`
          set c : ℝ := coeffSeminormSeq ξ hξ 4 f
          have hEq :
              c
                  + ((2 : ℝ) / ((2 * Real.pi) ^ 2)) * (CΔ * c)
                  + ((2 * Real.pi) ^ 4)⁻¹ * (CΔΔ * c)
                =
                ((1 : ℝ)
                    + ((2 : ℝ) / ((2 * Real.pi) ^ 2)) * CΔ
                    + ((2 * Real.pi) ^ 4)⁻¹ * CΔΔ) * c := by
            ring
          -- rewrite `h2` using `c` and then use the equality
          have h2' : ‖h.toLp 2 (volume : Measure SpaceTime)‖ ≤
              c
                + ((2 : ℝ) / ((2 * Real.pi) ^ 2)) * (CΔ * c)
                + ((2 * Real.pi) ^ 4)⁻¹ * (CΔΔ * c) := by
            simpa [c, mul_assoc] using h2
          -- finish
          simpa [hEq] using h2'
        -- unfold `Csob` and close by definitional equality
        dsimp [Csob]
        exact this
      exact this

    have hx5 : ‖f x‖ ≤ (A * Csob) * coeffSeminormSeq ξ hξ 4 f := by
      have hfx : ‖f x‖ ≤ A * ‖hW.toLp 2 (volume : Measure SpaceTime)‖ := by
        simpa [hx0] using hx4
      -- combine the pointwise bound with the `L²` bound on `hW`
      have hmul :
          A * ‖hW.toLp 2 (volume : Measure SpaceTime)‖ ≤
            A * (Csob * coeffSeminormSeq ξ hξ 4 f) :=
        mul_le_mul_of_nonneg_left hW_le hA0
      -- reassociate scalars
      calc
        ‖f x‖ ≤ A * ‖hW.toLp 2 (volume : Measure SpaceTime)‖ := hfx
        _ ≤ A * (Csob * coeffSeminormSeq ξ hξ 4 f) := hmul
        _ = (A * Csob) * coeffSeminormSeq ξ hξ 4 f := by ring_nf

    exact hx5

  have hMp : 0 ≤ (A * Csob) * coeffSeminormSeq ξ hξ 4 f := by
    positivity
  have hsem := SchwartzMap.seminorm_le_bound (𝕜 := ℝ) (k := 0) (n := 0) f hMp hbound
  have hCto : (Real.toNNReal (Csob * A) : ℝ) = Csob * A := by
    have hAC : 0 ≤ Csob * A := mul_nonneg hCsob0 hA0
    -- `Real.toNNReal_of_nonneg` is stated in `ℝ≥0`; coerce to `ℝ`.
    have h' : (Real.toNNReal (Csob * A) : ℝ≥0) = ⟨Csob * A, hAC⟩ :=
      Real.toNNReal_of_nonneg hAC
    have h'' := congrArg (fun t : ℝ≥0 => (t : ℝ)) h'
    simpa using h''
  -- rewrite `A * Csob` as `Csob * A` to match `hCto`
  have hsem' : SchwartzMap.seminorm ℝ 0 0 f ≤ (Csob * A) * coeffSeminormSeq ξ hξ 4 f := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using hsem
  have hAC : 0 ≤ Csob * A := mul_nonneg hCsob0 hA0
  -- finish by rewriting the RHS as evaluation of the scaled seminorm
  simpa [Seminorm.smul_apply, NNReal.smul_def, Real.toNNReal_of_nonneg hAC, hCto,
    mul_assoc, mul_comm, mul_left_comm] using hsem'

/-! ## Iterated coordinate-derivative bounds for `coeffSeminormSeq` -/

private lemma coeffSeminormSeq_iteratedLineDerivOp_unitVec_le (ξ : ℝ) (hξ : ξ ≠ 0)
    {n : ℕ} (r : Fin n → Fin STDimension) (k₀ : ℕ) (f : TestFunction) :
    coeffSeminormSeq ξ hξ k₀ (∂^{fun j : Fin n ↦ unitVec (r j)} f) ≤
      (∏ j ∈ Finset.range n,
          (‖(1 / (2 * ξ) : ℝ)‖ * Real.sqrt 2 * ((2 : ℝ) ^ (k₀ + j) + 1))) *
        coeffSeminormSeq ξ hξ (k₀ + n) f := by
  induction n generalizing k₀ with
  | zero =>
    simp
  | succ n ih =>
    -- one-step bound at index `k₀`, then induct on the tail at index `k₀+1`
    have hstep :
        coeffSeminormSeq ξ hξ k₀ (∂^{fun j : Fin (n + 1) ↦ unitVec (r j)} f) ≤
          (‖(1 / (2 * ξ) : ℝ)‖ * Real.sqrt 2 * ((2 : ℝ) ^ k₀ + 1)) *
            coeffSeminormSeq ξ hξ (k₀ + 1) (∂^{fun j : Fin n ↦ unitVec (r j.succ)} f) := by
      -- `∂^{m} = ∂_{m 0} (∂^{tail m})` and `∂_{unitVec i} = derivCoordCLM i`
      simpa [LineDeriv.iteratedLineDerivOp_succ_left, Fin.tail_def] using
        (coeffSeminormSeq_derivCoordCLM_le (ξ := ξ) (hξ := hξ) (i := r 0) (k := k₀)
          (f := (∂^{fun j : Fin n ↦ unitVec (r j.succ)} f)))
    have hrec :
        coeffSeminormSeq ξ hξ (k₀ + 1) (∂^{fun j : Fin n ↦ unitVec (r j.succ)} f) ≤
          (∏ j ∈ Finset.range n,
              (‖(1 / (2 * ξ) : ℝ)‖ * Real.sqrt 2 * ((2 : ℝ) ^ (k₀ + 1 + j) + 1))) *
            coeffSeminormSeq ξ hξ (k₀ + 1 + n) f := by
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (ih (r := fun j : Fin n ↦ r j.succ) (k₀ := k₀ + 1))
    -- rewrite the product as `j=0` term times the shifted tail-product
    have hmul :
        (‖(1 / (2 * ξ) : ℝ)‖ * Real.sqrt 2 * ((2 : ℝ) ^ k₀ + 1)) *
              (∏ j ∈ Finset.range n,
                (‖(1 / (2 * ξ) : ℝ)‖ * Real.sqrt 2 * ((2 : ℝ) ^ (k₀ + 1 + j) + 1)))
          =
          ∏ j ∈ Finset.range (n + 1),
            (‖(1 / (2 * ξ) : ℝ)‖ * Real.sqrt 2 * ((2 : ℝ) ^ (k₀ + j) + 1)) := by
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, mul_comm, mul_left_comm, mul_assoc] using
        (Finset.prod_range_succ' (fun j : ℕ ↦
          (‖(1 / (2 * ξ) : ℝ)‖ * Real.sqrt 2 * ((2 : ℝ) ^ (k₀ + j) + 1))) n).symm
    -- finish by chaining `hstep` and the inductive bound
    have :
        coeffSeminormSeq ξ hξ k₀ (∂^{fun j : Fin (n + 1) ↦ unitVec (r j)} f) ≤
          (∏ j ∈ Finset.range (n + 1),
              (‖(1 / (2 * ξ) : ℝ)‖ * Real.sqrt 2 * ((2 : ℝ) ^ (k₀ + j) + 1))) *
            coeffSeminormSeq ξ hξ (k₀ + (n + 1)) f := by
      -- multiply the inductive estimate by the leading scalar and reassociate
      have this :=
        mul_le_mul_of_nonneg_left hrec
          (by positivity : 0 ≤ (‖(1 / (2 * ξ) : ℝ)‖ * Real.sqrt 2 * ((2 : ℝ) ^ k₀ + 1)))
      have this' :
          (‖(1 / (2 * ξ) : ℝ)‖ * Real.sqrt 2 * ((2 : ℝ) ^ k₀ + 1)) *
              coeffSeminormSeq ξ hξ (k₀ + 1) (∂^{fun j : Fin n ↦ unitVec (r j.succ)} f)
            ≤
            ((‖(1 / (2 * ξ) : ℝ)‖ * Real.sqrt 2 * ((2 : ℝ) ^ k₀ + 1)) *
                (∏ j ∈ Finset.range n,
                  (‖(1 / (2 * ξ) : ℝ)‖ * Real.sqrt 2 * ((2 : ℝ) ^ (k₀ + 1 + j) + 1)))) *
              coeffSeminormSeq ξ hξ (k₀ + 1 + n) f := by
        simpa [mul_assoc] using this
      -- chain with the one-step bound and rewrite indices/products
      refine le_trans hstep ?_
      have : (‖(1 / (2 * ξ) : ℝ)‖ * Real.sqrt 2 * ((2 : ℝ) ^ k₀ + 1)) *
            coeffSeminormSeq ξ hξ (k₀ + 1) (∂^{fun j : Fin n ↦ unitVec (r j.succ)} f)
          ≤
          (∏ j ∈ Finset.range (n + 1),
              (‖(1 / (2 * ξ) : ℝ)‖ * Real.sqrt 2 * ((2 : ℝ) ^ (k₀ + j) + 1))) *
            coeffSeminormSeq ξ hξ (k₀ + (n + 1)) f := by
        -- rewrite the scalar-product on the RHS using `hmul`
        have hmul' :
            ((‖(1 / (2 * ξ) : ℝ)‖ * Real.sqrt 2 * ((2 : ℝ) ^ k₀ + 1)) *
                  (∏ j ∈ Finset.range n,
                    (‖(1 / (2 * ξ) : ℝ)‖ * Real.sqrt 2 * ((2 : ℝ) ^ (k₀ + 1 + j) + 1)))) *
                coeffSeminormSeq ξ hξ (k₀ + 1 + n) f
              =
              (∏ j ∈ Finset.range (n + 1),
                  (‖(1 / (2 * ξ) : ℝ)‖ * Real.sqrt 2 * ((2 : ℝ) ^ (k₀ + j) + 1))) *
                coeffSeminormSeq ξ hξ (k₀ + 1 + n) f := by
          -- apply `hmul` and then multiply on the right by the remaining factor
          exact congrArg (fun t : ℝ ↦ t * coeffSeminormSeq ξ hξ (k₀ + 1 + n) f) hmul
        -- avoid `simp` normalizing the scalar `‖1/(2*ξ)‖`; rewrite the goal and close by `this'`
        have hidx : k₀ + (n + 1) = k₀ + 1 + n := by
          simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
        rw [hidx]
        -- rewrite the RHS into the form appearing in `this'`
        rw [← hmul']
        exact this'
      exact this
    exact this

/-! ## Bounding general Schwartz seminorms by `coeffSeminormSeq` -/

private lemma schwartz_seminorm_le_coeffSeminormSeq_of_seminorm0
    (ξ : ℝ) (hξ : ξ ≠ 0) (C00 : ℝ≥0)
    (hC00 : ∀ f : TestFunction,
      SchwartzMap.seminorm ℝ 0 0 f ≤ ((C00 : ℝ≥0) • coeffSeminormSeq ξ hξ 4) f)
    (k n : ℕ) :
    ∃ C : ℝ≥0, ∀ f : TestFunction,
      SchwartzMap.seminorm ℝ k n f ≤ ((C : ℝ≥0) • coeffSeminormSeq ξ hξ (4 + k + n)) f := by
  -- dimension constant
  let d : ℝ := (Fintype.card (Fin STDimension) : ℝ)
  -- size of the `r : Fin n → Fin STDimension` index set
  let cardR : ℝ := (Fintype.card (Fin n → Fin STDimension) : ℝ)
  cases k with
  | zero =>
    -- no coordinate weights
    let Cder : ℝ :=
      ∏ j ∈ Finset.range n,
        (‖(1 / (2 * ξ) : ℝ)‖ * Real.sqrt 2 * ((2 : ℝ) ^ (4 + j) + 1))
    let C : ℝ := (d ^ n) * cardR * (C00 : ℝ) * Cder
    refine ⟨⟨C, by
      dsimp [C]; positivity⟩, ?_⟩
    intro f
    -- Step 1: bound `SchwartzMap.seminorm 0 n` by a finite sum of `SchwartzMap.seminorm 0 0` of
    -- iterated coordinate derivatives.
    let M : ℝ :=
      (d ^ n) *
        (∑ r : (Fin n → Fin STDimension),
          SchwartzMap.seminorm ℝ 0 0 (∂^{fun j : Fin n ↦ unitVec (r j)} f))
    have hsem : SchwartzMap.seminorm ℝ 0 n f ≤ M := by
      simpa [M, d] using (schwartz_seminorm0_le_card_pow_mul_sum_seminorm0 (n := n) (f := f))

    -- Step 2: bound the RHS by `coeffSeminormSeq ξ hξ (4+n) f` using `hC00` and
    -- the iterated-derivative bound on `coeffSeminormSeq`.
    have hM :
        M ≤ C * coeffSeminormSeq ξ hξ (4 + n) f := by
      -- bound each term in the sum uniformly
      have hterm :
          ∀ r : (Fin n → Fin STDimension),
            SchwartzMap.seminorm ℝ 0 0 (∂^{fun j : Fin n ↦ unitVec (r j)} f)
              ≤ (C00 : ℝ) * Cder * coeffSeminormSeq ξ hξ (4 + n) f := by
        intro r
        -- `seminorm 0 0` controlled by `coeffSeminormSeq .. 4`
        have h00 :
            SchwartzMap.seminorm ℝ 0 0 (∂^{fun j : Fin n ↦ unitVec (r j)} f) ≤
              (C00 : ℝ) * coeffSeminormSeq ξ hξ 4 (∂^{fun j : Fin n ↦ unitVec (r j)} f) := by
          -- expand the scaled seminorm evaluation
          have := hC00 (∂^{fun j : Fin n ↦ unitVec (r j)} f)
          simpa [Seminorm.smul_apply, NNReal.smul_def, mul_assoc] using this
        -- apply the iterated coordinate-derivative bound on `coeffSeminormSeq`
        have hder :
            coeffSeminormSeq ξ hξ 4 (∂^{fun j : Fin n ↦ unitVec (r j)} f) ≤
              Cder * coeffSeminormSeq ξ hξ (4 + n) f := by
          -- `coeffSeminormSeq_iteratedLineDerivOp_unitVec_le` with base index `4`
          simpa [Cder, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            (coeffSeminormSeq_iteratedLineDerivOp_unitVec_le (ξ := ξ) (hξ := hξ)
              (r := r) (k₀ := 4) (f := f))
        -- chain inequalities and reassociate
        calc
          SchwartzMap.seminorm ℝ 0 0 (∂^{fun j : Fin n ↦ unitVec (r j)} f)
              ≤ (C00 : ℝ) * coeffSeminormSeq ξ hξ 4 (∂^{fun j : Fin n ↦ unitVec (r j)} f) := h00
          _ ≤ (C00 : ℝ) * (Cder * coeffSeminormSeq ξ hξ (4 + n) f) := by
                exact mul_le_mul_of_nonneg_left hder (by positivity)
          _ = (C00 : ℝ) * Cder * coeffSeminormSeq ξ hξ (4 + n) f := by ring
      -- sum the uniform bound and multiply by the front factor `(d^n)`
      have hsum :
          (∑ r : (Fin n → Fin STDimension),
              SchwartzMap.seminorm ℝ 0 0 (∂^{fun j : Fin n ↦ unitVec (r j)} f))
            ≤ cardR * ((C00 : ℝ) * Cder * coeffSeminormSeq ξ hξ (4 + n) f) := by
        -- uniform bound + `Fintype.card` estimate
        have hsum' :
            (∑ r : (Fin n → Fin STDimension),
                SchwartzMap.seminorm ℝ 0 0 (∂^{fun j : Fin n ↦ unitVec (r j)} f))
              ≤ (Fintype.card (Fin n → Fin STDimension) : ℝ) *
                  ((C00 : ℝ) * Cder * coeffSeminormSeq ξ hξ (4 + n) f) := by
          refine sum_le_card_mul_of_pointwise_le (f := fun r : (Fin n → Fin STDimension) =>
            SchwartzMap.seminorm ℝ 0 0 (∂^{fun j : Fin n ↦ unitVec (r j)} f))
            (C := (C00 : ℝ) * Cder * coeffSeminormSeq ξ hξ (4 + n) f) ?_
          intro r
          simpa [mul_assoc] using (hterm r)
        -- rewrite `Fintype.card` as `cardR`
        simpa [cardR] using hsum'
      -- finish
      have hsum' :
          d ^ n *
              (∑ r : (Fin n → Fin STDimension),
                SchwartzMap.seminorm ℝ 0 0 (∂^{fun j : Fin n ↦ unitVec (r j)} f))
            ≤
            d ^ n * (cardR * ((C00 : ℝ) * Cder * coeffSeminormSeq ξ hξ (4 + n) f)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      -- reassociate to match `M` and `C`
      -- (`M = d^n * sum`, `C = d^n * cardR * C00 * Cder`)
      simpa [M, C, mul_assoc, mul_left_comm, mul_comm] using hsum'

    -- conclude
    have : SchwartzMap.seminorm ℝ 0 n f ≤ C * coeffSeminormSeq ξ hξ (4 + n) f := by
      exact le_trans hsem hM
    -- rewrite as evaluation of the scaled seminorm (with `4 + 0 + n = 4 + n`)
    -- avoid `simp` (can be slow here); change the goal to the multiplicative form
    -- and use the inequality we already proved.
    -- (`(⟨C, _⟩ : ℝ≥0) • p` evaluates to `C * p`.)
    change SchwartzMap.seminorm ℝ 0 n f ≤ C * coeffSeminormSeq ξ hξ (4 + n) f
    exact this

  | succ k =>
    -- include coordinate weights (use a crude bound via a sum of coordinate monomials)
    let Cmul : ℝ :=
      ∏ j ∈ Finset.range (k + 1),
        (‖(ξ / 2 : ℝ)‖ * Real.sqrt 2 * ((2 : ℝ) ^ (4 + j) + 1))
    let Cder : ℝ :=
      ∏ j ∈ Finset.range n,
        (‖(1 / (2 * ξ) : ℝ)‖ * Real.sqrt 2 * ((2 : ℝ) ^ (4 + (k + 1) + j) + 1))
    let C : ℝ := (d ^ k) * (d ^ n) * d * cardR * (C00 : ℝ) * Cmul * Cder
    refine ⟨⟨C, by
      dsimp [C]; positivity⟩, ?_⟩
    intro f
    -- Step 1: bound `SchwartzMap.seminorm (k+1) n` by a finite sum of `SchwartzMap.seminorm 0 0` of
    -- `(mulCoordCLM i)^[k+1] (∂^{unitVec∘r} f)`.
    have hsem :
        SchwartzMap.seminorm ℝ (k + 1) n f ≤
          (d ^ k) * (d ^ n) *
            (∑ i : Fin STDimension, ∑ r : (Fin n → Fin STDimension),
              SchwartzMap.seminorm ℝ 0 0
                (((mulCoordCLM i)^[k + 1]) (∂^{fun j : Fin n ↦ unitVec (r j)} f))) := by
      simpa [d] using
        (schwartz_seminorm_succ_le_card_pow_mul_sum_seminorm0 (k := k) (n := n) (f := f))

    -- Step 2: bound the RHS by `coeffSeminormSeq ξ hξ (4 + (k+1) + n)` using `hC00`,
    -- and the operator iteration bounds.
    have hM :
        (d ^ k) * (d ^ n) *
            (∑ i : Fin STDimension, ∑ r : (Fin n → Fin STDimension),
              SchwartzMap.seminorm ℝ 0 0
                (((mulCoordCLM i)^[k + 1]) (∂^{fun j : Fin n ↦ unitVec (r j)} f)))
          ≤ C * coeffSeminormSeq ξ hξ (4 + (k + 1) + n) f := by
      -- uniform bound for each `(i,r)` term
      have hterm (i : Fin STDimension) (r : Fin n → Fin STDimension) :
          SchwartzMap.seminorm ℝ 0 0 (((mulCoordCLM i)^[k + 1]) (∂^{fun j : Fin n ↦ unitVec (r j)} f))
            ≤ (C00 : ℝ) * Cmul * Cder * coeffSeminormSeq ξ hξ (4 + (k + 1) + n) f := by
        -- first apply `hC00`
        have h00 :
            SchwartzMap.seminorm ℝ 0 0 (((mulCoordCLM i)^[k + 1]) (∂^{fun j : Fin n ↦ unitVec (r j)} f))
              ≤ (C00 : ℝ) * coeffSeminormSeq ξ hξ 4 (((mulCoordCLM i)^[k + 1]) (∂^{fun j : Fin n ↦ unitVec (r j)} f)) := by
          have := hC00 (((mulCoordCLM i)^[k + 1]) (∂^{fun j : Fin n ↦ unitVec (r j)} f))
          simpa [Seminorm.smul_apply, NNReal.smul_def, mul_assoc] using this
        -- bound the multiplication iterates on `coeffSeminormSeq`
        have hmul :
            coeffSeminormSeq ξ hξ 4 (((mulCoordCLM i)^[k + 1]) (∂^{fun j : Fin n ↦ unitVec (r j)} f))
              ≤ Cmul * coeffSeminormSeq ξ hξ (4 + (k + 1)) (∂^{fun j : Fin n ↦ unitVec (r j)} f) := by
          -- `coeffSeminormSeq_mulCoordCLM_iter_le` with base index `4`
          dsimp [Cmul]
          exact
            (coeffSeminormSeq_mulCoordCLM_iter_le (ξ := ξ) (hξ := hξ) (i := i)
              (k₀ := 4) (k := k + 1) (f := (∂^{fun j : Fin n ↦ unitVec (r j)} f)))
        -- bound iterated derivatives in `coeffSeminormSeq`
        have hder :
            coeffSeminormSeq ξ hξ (4 + (k + 1)) (∂^{fun j : Fin n ↦ unitVec (r j)} f) ≤
              Cder * coeffSeminormSeq ξ hξ (4 + (k + 1) + n) f := by
          dsimp [Cder]
          exact
            (coeffSeminormSeq_iteratedLineDerivOp_unitVec_le (ξ := ξ) (hξ := hξ)
              (r := r) (k₀ := 4 + (k + 1)) (f := f))
        -- chain
        calc
          SchwartzMap.seminorm ℝ 0 0 (((mulCoordCLM i)^[k + 1]) (∂^{fun j : Fin n ↦ unitVec (r j)} f))
              ≤ (C00 : ℝ) * coeffSeminormSeq ξ hξ 4 (((mulCoordCLM i)^[k + 1]) (∂^{fun j : Fin n ↦ unitVec (r j)} f)) := h00
          _ ≤ (C00 : ℝ) * (Cmul * coeffSeminormSeq ξ hξ (4 + (k + 1)) (∂^{fun j : Fin n ↦ unitVec (r j)} f)) := by
                -- multiply by the nonnegative scalar `C00`
                exact mul_le_mul_of_nonneg_left hmul (by positivity)
          _ ≤ (C00 : ℝ) * (Cmul * (Cder * coeffSeminormSeq ξ hξ (4 + (k + 1) + n) f)) := by
                -- multiply by the nonnegative scalar `C00*Cmul`
                have hnonneg : 0 ≤ (C00 : ℝ) * Cmul := by positivity
                have hmul' := mul_le_mul_of_nonneg_left hder hnonneg
                -- rewrite both sides by associativity (avoid `simp`)
                rw [mul_assoc] at hmul'
                rw [mul_assoc] at hmul'
                exact hmul'
          _ = (C00 : ℝ) * Cmul * Cder * coeffSeminormSeq ξ hξ (4 + (k + 1) + n) f := by ring
      -- sum over `i` and `r`, then multiply by the front scalar `(d^k)*(d^n)`
      have hsum :
          (∑ i : Fin STDimension, ∑ r : (Fin n → Fin STDimension),
              SchwartzMap.seminorm ℝ 0 0 (((mulCoordCLM i)^[k + 1]) (∂^{fun j : Fin n ↦ unitVec (r j)} f)))
            ≤ (d * cardR) * ((C00 : ℝ) * Cmul * Cder * coeffSeminormSeq ξ hξ (4 + (k + 1) + n) f) := by
        -- two-step `Fintype.card` estimate: first in `r`, then in `i`
        have hsum_r :
            ∀ i : Fin STDimension,
              (∑ r : (Fin n → Fin STDimension),
                  SchwartzMap.seminorm ℝ 0 0
                    (((mulCoordCLM i)^[k + 1]) (∂^{fun j : Fin n ↦ unitVec (r j)} f)))
                ≤ cardR * ((C00 : ℝ) * Cmul * Cder * coeffSeminormSeq ξ hξ (4 + (k + 1) + n) f) := by
          intro i
          have hsum' :
              (∑ r : (Fin n → Fin STDimension),
                  SchwartzMap.seminorm ℝ 0 0
                    (((mulCoordCLM i)^[k + 1]) (∂^{fun j : Fin n ↦ unitVec (r j)} f)))
                ≤ (Fintype.card (Fin n → Fin STDimension) : ℝ) *
                    ((C00 : ℝ) * Cmul * Cder * coeffSeminormSeq ξ hξ (4 + (k + 1) + n) f) := by
            refine sum_le_card_mul_of_pointwise_le
              (f := fun r : (Fin n → Fin STDimension) =>
                SchwartzMap.seminorm ℝ 0 0
                  (((mulCoordCLM i)^[k + 1]) (∂^{fun j : Fin n ↦ unitVec (r j)} f)))
              (C := (C00 : ℝ) * Cmul * Cder * coeffSeminormSeq ξ hξ (4 + (k + 1) + n) f) ?_
            intro r
            exact hterm i r
          dsimp [cardR]
          exact hsum'
        -- sum over `i` and apply the `card` estimate again
        have hsum_i :
            (∑ i : Fin STDimension,
                (∑ r : (Fin n → Fin STDimension),
                    SchwartzMap.seminorm ℝ 0 0
                      (((mulCoordCLM i)^[k + 1]) (∂^{fun j : Fin n ↦ unitVec (r j)} f))))
              ≤ (Fintype.card (Fin STDimension) : ℝ) *
                  (cardR * ((C00 : ℝ) * Cmul * Cder * coeffSeminormSeq ξ hξ (4 + (k + 1) + n) f)) := by
          refine sum_le_card_mul_of_pointwise_le
            (f := fun i : Fin STDimension =>
              (∑ r : (Fin n → Fin STDimension),
                SchwartzMap.seminorm ℝ 0 0
                  (((mulCoordCLM i)^[k + 1]) (∂^{fun j : Fin n ↦ unitVec (r j)} f))))
            (C := cardR * ((C00 : ℝ) * Cmul * Cder * coeffSeminormSeq ξ hξ (4 + (k + 1) + n) f)) ?_
          intro i
          exact hsum_r i
        -- rewrite `Fintype.card` as `d` and reassociate
        have hsum_i' := hsum_i
        rw [← mul_assoc] at hsum_i'
        dsimp [d]
        exact hsum_i'
      -- multiply `hsum` by the nonnegative prefactor `(d^k)*(d^n)` to match `M`
      have hsum' :
          (d ^ k) * (d ^ n) *
              (∑ i : Fin STDimension, ∑ r : (Fin n → Fin STDimension),
                SchwartzMap.seminorm ℝ 0 0
                  (((mulCoordCLM i)^[k + 1]) (∂^{fun j : Fin n ↦ unitVec (r j)} f)))
            ≤
            (d ^ k) * (d ^ n) *
              ((d * cardR) * ((C00 : ℝ) * Cmul * Cder *
                coeffSeminormSeq ξ hξ (4 + (k + 1) + n) f)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      refine le_trans hsum' ?_
      dsimp [C]
      have hrhs :
          (d ^ k) * (d ^ n) *
              ((d * cardR) * ((C00 : ℝ) * Cmul * Cder * coeffSeminormSeq ξ hξ (4 + (k + 1) + n) f))
            =
            ((d ^ k) * (d ^ n) * d * cardR * (C00 : ℝ) * Cmul * Cder) *
              coeffSeminormSeq ξ hξ (4 + (k + 1) + n) f := by
        ring_nf
      exact le_of_eq hrhs
    have : SchwartzMap.seminorm ℝ (k + 1) n f ≤ C * coeffSeminormSeq ξ hξ (4 + (k + 1) + n) f :=
      le_trans hsem hM
    -- rewrite as evaluation of the scaled seminorm
    -- unfold the scalar action without `simp` search (this was a heartbeat hotspot)
    rw [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul]
    exact this

/-! ## Main bound: Schwartz seminorm sequence by coefficient seminorm sequence -/

theorem isBounded_coeffSeminormSeq_schwartzSeminormSeq (ξ : ℝ) (hξ : ξ ≠ 0) :
    Seminorm.IsBounded (coeffSeminormSeq ξ hξ) OSforGFF.schwartzSeminormSeq (LinearMap.id) := by
  -- first get the Sobolev estimate for the `0,0` seminorm
  rcases schwartz_seminorm0_le_coeffSeminormSeq_four (ξ := ξ) (hξ := hξ) with ⟨C00, hC00⟩
  -- bound the full Schwartz seminorm family `SchwartzMap.seminorm k n` by `coeffSeminormSeq`
  have hfamily :
      Seminorm.IsBounded (coeffSeminormSeq ξ hξ) OSforGFF.schwartzSeminormFamily_TestFunction
        (LinearMap.id) := by
    intro km
    rcases km with ⟨k, n⟩
    rcases schwartz_seminorm_le_coeffSeminormSeq_of_seminorm0 (ξ := ξ) (hξ := hξ) (C00 := C00)
      (hC00 := hC00) k n with ⟨C, hC⟩
    refine ⟨{4 + k + n}, C, ?_⟩
    -- show the seminorm inequality pointwise
    intro f
    -- `comp id` is trivial and the singleton sup is the underlying seminorm
    simpa [Seminorm.comp_apply] using (hC f)
  -- finally, take the finite supremum defining `schwartzSeminormSeq n`
  intro n
  -- `Seminorm.isBounded_sup` packages boundedness of a family into boundedness of its finite sup
  rcases (Seminorm.isBounded_sup (p := coeffSeminormSeq ξ hξ)
      (q := OSforGFF.schwartzSeminormFamily_TestFunction) (f := LinearMap.id) hfamily
      (s' := Finset.Iic (n, n))) with ⟨C, s, hs⟩
  refine ⟨s, C, ?_⟩
  -- unfold `schwartzSeminormSeq`
  simpa [OSforGFF.schwartzSeminormSeq] using hs

theorem schwartzNuclearInclusion_of_coeffSeminormSeq (ξ : ℝ) (hξ : ξ ≠ 0) :
    OSforGFF.SchwartzNuclearInclusion := by
  exact
    schwartzNuclearInclusion_of_equiv_coeffSeminormSeq (ξ := ξ) (hξ := hξ)
      (hb_sch_le_coeff := isBounded_coeffSeminormSeq_schwartzSeminormSeq (ξ := ξ) (hξ := hξ))

theorem nuclearSpaceStd_TestFunction_of_coeffSeminormSeq (ξ : ℝ) (hξ : ξ ≠ 0) :
    OSforGFF.NuclearSpaceStd TestFunction := by
  exact
    OSforGFF.nuclearSpaceStd_TestFunction_of_schwartzNuclearInclusion
      (schwartzNuclearInclusion_of_coeffSeminormSeq (ξ := ξ) (hξ := hξ))

end SpaceTimeHermite

end

end PhysLean
