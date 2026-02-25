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

* the Schwartz seminorm sequence `OSforGFF.schwartzSeminormSeq`, and
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

private lemma sqrt_sum_norm_sq_le_sum_norm (x : SpaceTime) :
    √(∑ i : Fin STDimension, ‖x i‖ ^ 2) ≤ ∑ i : Fin STDimension, ‖x i‖ := by
  have hsq :
      (∑ i : Fin STDimension, ‖x i‖ ^ 2) ≤ (∑ i : Fin STDimension, ‖x i‖) ^ 2 := by
    simpa [pow_two] using
      (Finset.sum_sq_le_sq_sum_of_nonneg (s := (Finset.univ : Finset (Fin STDimension)))
        (f := fun i : Fin STDimension => ‖x i‖) (by intro i hi; exact norm_nonneg _))
  have hnonneg : 0 ≤ ∑ i : Fin STDimension, ‖x i‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  have h := Real.sqrt_le_sqrt hsq
  -- `simp` tends to rewrite `‖x i‖` into `|x.ofLp i|`, so we remove the absolute value in a
  -- separate step where the nonnegativity hypothesis matches the syntactic expression.
  have hnonneg' : 0 ≤ ∑ i : Fin STDimension, |x.ofLp i| := by
    simpa [Real.norm_eq_abs] using hnonneg
  calc
    √(∑ i : Fin STDimension, ‖x i‖ ^ 2) ≤ √((∑ i : Fin STDimension, ‖x i‖) ^ 2) := h
    _ = |∑ i : Fin STDimension, ‖x i‖| := by simp [Real.sqrt_sq_eq_abs]
    _ = ∑ i : Fin STDimension, |x.ofLp i| := by
          simpa [Real.norm_eq_abs] using (abs_of_nonneg hnonneg')

private lemma norm_le_sum_abs_ofLp (x : SpaceTime) :
    ‖x‖ ≤ ∑ i : Fin STDimension, |x.ofLp i| := by
  calc
    ‖x‖ = √(∑ i : Fin STDimension, ‖x i‖ ^ 2) := by
          simpa using (EuclideanSpace.norm_eq (x := x))
    _ ≤ ∑ i : Fin STDimension, ‖x i‖ := sqrt_sum_norm_sq_le_sum_norm x
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

private lemma sum_sum_le_card_mul_of_pointwise_le {α β : Type*} [Fintype α] [Fintype β]
    {f : α → β → ℝ} {C : ℝ} (hf : ∀ a : α, ∀ b : β, f a b ≤ C) :
    (∑ a : α, ∑ b : β, f a b) ≤ (Fintype.card α : ℝ) * ((Fintype.card β : ℝ) * C) := by
  have hβ : ∀ a : α, (∑ b : β, f a b) ≤ (Fintype.card β : ℝ) * C := by
    intro a
    exact sum_le_card_mul_of_pointwise_le (f := fun b : β => f a b) (C := C) (hf a)
  exact sum_le_card_mul_of_pointwise_le
    (f := fun a : α => ∑ b : β, f a b) (C := (Fintype.card β : ℝ) * C) hβ

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
  have hfac : ∀ j : Fin n, ‖(m j).ofLp (r j)‖ ≤ ∑ i : Fin STDimension, |(m j).ofLp i| := by
    intro j
    have : |(m j).ofLp (r j)| ≤ ∑ i : Fin STDimension, |(m j).ofLp i| := by
      simpa using
        (Finset.single_le_sum (s := (Finset.univ : Finset (Fin STDimension)))
          (f := fun i : Fin STDimension => |(m j).ofLp i|)
          (by intro i hi; exact abs_nonneg _)
          (by simp : r j ∈ (Finset.univ : Finset (Fin STDimension))))
    simpa [Real.norm_eq_abs] using this
  simpa using
    (Finset.prod_le_prod (s := (Finset.univ : Finset (Fin n)))
      (fun j hj => by positivity)
      (fun j hj => hfac j))

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
  simp only [pow_zero, one_mul, Fintype.card_fin, Nat.cast_ofNat]
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

private def coeffMulConst (ξ : ℝ) : ℕ → ℝ := fun k =>
  ‖(ξ / 2 : ℝ)‖ * Real.sqrt 2 * ((2 : ℝ) ^ k + 1)

private def coeffMulProd (ξ : ℝ) (k₀ k : ℕ) : ℝ :=
  ∏ j ∈ Finset.range k, coeffMulConst ξ (k₀ + j)

private def coeffDerivConst (ξ : ℝ) : ℕ → ℝ := fun k =>
  ‖(1 / (2 * ξ) : ℝ)‖ * Real.sqrt 2 * ((2 : ℝ) ^ k + 1)

private def coeffDerivProd (ξ : ℝ) (k₀ n : ℕ) : ℝ :=
  ∏ j ∈ Finset.range n, coeffDerivConst ξ (k₀ + j)

private lemma coeffSeminormSeq_mulCoordCLM_iter_le
    (ξ : ℝ) (hξ : ξ ≠ 0) (i : Fin STDimension) (k₀ k : ℕ) (f : TestFunction) :
    coeffSeminormSeq ξ hξ k₀ (((mulCoordCLM i)^[k]) f) ≤
      coeffMulProd ξ k₀ k *
        coeffSeminormSeq ξ hξ (k₀ + k) f := by
  induction k generalizing k₀ f with
  | zero => simp [coeffMulProd]
  | succ k ih =>
    have hrec := ih (k₀ := k₀) (f := mulCoordCLM i f)
    have hstep := coeffSeminormSeq_mulCoordCLM_le (ξ := ξ) (hξ := hξ) (i := i) (k := k₀ + k) (f := f)
    have hprod_nonneg : 0 ≤ coeffMulProd ξ k₀ k := by
      classical
      unfold coeffMulProd
      refine Finset.prod_nonneg ?_
      intro j hj
      dsimp [coeffMulConst]
      positivity
    have hmul := mul_le_mul_of_nonneg_left hstep hprod_nonneg
    have := le_trans (by simpa [Function.iterate_succ_apply] using hrec) hmul
    simpa [coeffMulProd, coeffMulConst, mul_assoc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
      Finset.prod_range_succ] using this


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
  let μ : Measure SpaceTime := (volume : Measure SpaceTime)
  have hint : (∫ ξ : SpaceTime, ‖(OSforGFF.ofRealSchwartz f) ξ‖ ^ (2 : ℝ) ∂μ)
      = ∫ ξ : SpaceTime, ‖f ξ‖ ^ (2 : ℝ) ∂μ := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with ξ
    simp
  calc
    ‖(OSforGFF.ofRealSchwartz f).toLp 2 μ‖
        = (∫ ξ : SpaceTime, ‖(OSforGFF.ofRealSchwartz f) ξ‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
            simpa using (integral_norm_rpow_two_rpow_inv_eq_norm_toLp (h := OSforGFF.ofRealSchwartz f)).symm
    _ = (∫ ξ : SpaceTime, ‖f ξ‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by simp
    _ = ‖f.toLp 2 μ‖ := by simpa using (integral_norm_rpow_two_rpow_inv_eq_norm_toLp_real (h := f))

private lemma norm_toLp_laplacian_ofRealSchwartz_eq (f : TestFunction) :
    ‖(Δ (OSforGFF.ofRealSchwartz f)).toLp 2 (volume : Measure SpaceTime)‖ =
      ‖(Δ f).toLp 2 (volume : Measure SpaceTime)‖ := by
  have h := norm_toLp_ofRealSchwartz_eq (f := Δ f)
  simpa [← laplacian_ofReal_eq (f := f)] using h

private lemma norm_toLp_laplacian_laplacian_ofRealSchwartz_eq (f : TestFunction) :
    ‖(Δ (Δ (OSforGFF.ofRealSchwartz f))).toLp 2 (volume : Measure SpaceTime)‖ =
      ‖(Δ (Δ f)).toLp 2 (volume : Measure SpaceTime)‖ := by
  have h := norm_toLp_ofRealSchwartz_eq (f := Δ (Δ f))
  have h' := h
  rw [← laplacian_ofReal_eq (f := Δ f)] at h'
  rw [← laplacian_ofReal_eq (f := f)] at h'
  exact h'

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
    (fun ξ : SpaceTime ↦ ‖fourierWeight ξ‖ * (‖fourierWeightInv ξ‖ * ‖(𝓕 g) ξ‖)) =
      (fun ξ : SpaceTime ↦ ‖(𝓕 g) ξ‖) := by
  funext ξ
  calc
    ‖fourierWeight ξ‖ * (‖fourierWeightInv ξ‖ * ‖(𝓕 g) ξ‖)
        = (‖fourierWeight ξ‖ * ‖fourierWeightInv ξ‖) * ‖(𝓕 g) ξ‖ := by
            simp [mul_assoc]
    _ = ‖(𝓕 g) ξ‖ := by
          simp [norm_fourierWeight_mul_norm_fourierWeightInv]

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
  simpa [fourierWeight_factor (g := g)] using (holder_fourierWeight (g := g))

private lemma integral_norm_fourier_le_weighted_L2 (g : TestFunctionℂ) :
    (∫ ξ : SpaceTime, ‖(𝓕 g) ξ‖ ∂(volume : Measure SpaceTime)) ≤
      ((∫ ξ : SpaceTime, ‖(((((1 : ℝ) + ‖ξ‖ ^ 2) ^ (-2 : ℝ)) : ℝ) : ℂ)‖ ^ (2 : ℝ)
          ∂(volume : Measure SpaceTime)) ^ (1 / (2 : ℝ))) *
        ((∫ ξ : SpaceTime,
              ‖(((((1 : ℝ) + ‖ξ‖ ^ 2) ^ (2 : ℝ)) : ℝ) : ℂ) • (𝓕 g) ξ‖ ^ (2 : ℝ)
            ∂(volume : Measure SpaceTime)) ^ (1 / (2 : ℝ))) := by
  simpa [fourierWeight, fourierWeightInv] using (integral_norm_fourier_le_weighted_L2' (g := g))

private lemma integral_norm_fourierWeightInv_smul_fourier_rpow_two_rpow_inv_eq_norm_toLp (g : TestFunctionℂ) :
    ((∫ ξ : SpaceTime, (‖fourierWeightInv ξ‖ * ‖(𝓕 g) ξ‖) ^ (2 : ℝ) ∂(volume : Measure SpaceTime)) ^
        (1 / (2 : ℝ))) =
      ‖(SchwartzMap.smulLeftCLM (F := ℂ) (fun ξ : SpaceTime ↦ fourierWeightInv ξ) (𝓕 g)).toLp 2
        (volume : Measure SpaceTime)‖ := by
  have hgrowth : (fun ξ : SpaceTime ↦ fourierWeightInv ξ).HasTemperateGrowth := by
    simpa [fourierWeightInv] using (by
      fun_prop : (fun ξ : SpaceTime ↦ (((((1 : ℝ) + ‖ξ‖ ^ 2) ^ (2 : ℝ)) : ℝ) : ℂ)).HasTemperateGrowth)
  set hW : TestFunctionℂ :=
    SchwartzMap.smulLeftCLM (F := ℂ) (fun ξ : SpaceTime ↦ fourierWeightInv ξ) (𝓕 g) with hW_def
  have hint : (fun ξ : SpaceTime ↦ ‖hW ξ‖ ^ (2 : ℝ))
      = fun ξ : SpaceTime ↦ (‖fourierWeightInv ξ‖ * ‖(𝓕 g) ξ‖) ^ (2 : ℝ) := by
    funext ξ
    have := SchwartzMap.smulLeftCLM_apply_apply (F := ℂ)
      (g := fun ξ : SpaceTime ↦ fourierWeightInv ξ) (hg := hgrowth) (𝓕 g) ξ
    simpa [hW_def, norm_smul, mul_assoc] using congrArg (fun z : ℂ => ‖z‖ ^ (2 : ℝ)) this
  have hintInt :
      (∫ ξ : SpaceTime, ‖hW ξ‖ ^ (2 : ℝ) ∂(volume : Measure SpaceTime)) =
        ∫ ξ : SpaceTime, (‖fourierWeightInv ξ‖ * ‖(𝓕 g) ξ‖) ^ (2 : ℝ)
          ∂(volume : Measure SpaceTime) := by
    aesop
  have hL2 := (integral_norm_rpow_two_rpow_inv_eq_norm_toLp (h := hW))
  rw [hintInt] at hL2
  exact hL2

private lemma norm_le_fourierWeightL2_mul_norm_toLp_fourierWeightInv_smul_fourier
    (g : TestFunctionℂ) (x : SpaceTime) :
    ‖g x‖ ≤
      ((∫ ξ : SpaceTime, ‖fourierWeight ξ‖ ^ (2 : ℝ) ∂(volume : Measure SpaceTime)) ^ (1 / (2 : ℝ))) *
        ‖(SchwartzMap.smulLeftCLM (F := ℂ) (fun ξ : SpaceTime ↦ fourierWeightInv ξ) (𝓕 g)).toLp 2
            (volume : Measure SpaceTime)‖ := by
  have hx1 : ‖g x‖ ≤ ∫ ξ : SpaceTime, ‖(𝓕 g) ξ‖ ∂(volume : Measure SpaceTime) :=
    norm_le_integral_norm_fourier g x
  have hx2 := integral_norm_fourier_le_weighted_L2' (g := g)
  -- rewrite the `L²` factor as a `toLp` norm of the weighted Fourier transform
  set hW : TestFunctionℂ :=
    SchwartzMap.smulLeftCLM (F := ℂ) (fun ξ : SpaceTime ↦ fourierWeightInv ξ) (𝓕 g)
  have hW_eq :
      (∫ ξ : SpaceTime, ‖fourierWeightInv ξ • (𝓕 g) ξ‖ ^ (2 : ℝ) ∂(volume : Measure SpaceTime)) ^
            (1 / (2 : ℝ))
        = ‖hW.toLp 2 (volume : Measure SpaceTime)‖ := by
    calc
      (∫ ξ : SpaceTime, ‖fourierWeightInv ξ • (𝓕 g) ξ‖ ^ (2 : ℝ) ∂(volume : Measure SpaceTime)) ^
            (1 / (2 : ℝ))
          = ((∫ ξ : SpaceTime, (‖fourierWeightInv ξ‖ * ‖(𝓕 g) ξ‖) ^ (2 : ℝ)
              ∂(volume : Measure SpaceTime)) ^ (1 / (2 : ℝ))) := by
                simp
      _ = ‖hW.toLp 2 (volume : Measure SpaceTime)‖ := by
            simpa [hW] using
              (integral_norm_fourierWeightInv_smul_fourier_rpow_two_rpow_inv_eq_norm_toLp (g := g))
  have hx2' :
      (∫ ξ : SpaceTime, ‖(𝓕 g) ξ‖ ∂(volume : Measure SpaceTime)) ≤
        ((∫ ξ : SpaceTime, ‖fourierWeight ξ‖ ^ (2 : ℝ) ∂(volume : Measure SpaceTime)) ^ (1 / (2 : ℝ))) *
          ‖hW.toLp 2 (volume : Measure SpaceTime)‖ := by
    rw [hW_eq] at hx2
    exact hx2
  exact (le_trans hx1 (by simpa [hW] using hx2'))

/-! ## Laplacian bounds in coefficient seminorms -/

/-- Constant controlling one Laplacian application in coefficient seminorms. -/
private def coeffLaplacianConst (ξ : ℝ) (k : ℕ) : ℝ :=
  (Fintype.card (Fin STDimension) : ℝ) * coeffDerivConst ξ k * coeffDerivConst ξ (k + 1)

/-- Constant controlling two Laplacian applications in coefficient seminorms. -/
private def coeffLaplacianLaplacianConst (ξ : ℝ) : ℝ :=
  coeffLaplacianConst ξ 0 * coeffLaplacianConst ξ 2

/-- Dimension-dependent constant controlling the Sobolev weight `sobolevWeight` by
`‖·‖₂`, `‖Δ·‖₂`, `‖Δ²·‖₂`, then by `coeffSeminormSeq .. 4`. -/
private def sobolevConst (ξ : ℝ) : ℝ :=
  (1 : ℝ)
    + ((2 : ℝ) / ((2 * Real.pi) ^ 2)) * coeffLaplacianConst ξ 0
    + ((2 * Real.pi) ^ 4)⁻¹ * coeffLaplacianLaplacianConst ξ

private lemma sobolevConst_nonneg (ξ : ℝ) : 0 ≤ sobolevConst ξ := by
  dsimp [sobolevConst]
  have hpi : 0 < (2 * Real.pi : ℝ) := by positivity
  have hden2 : 0 ≤ ((2 * Real.pi) ^ 2 : ℝ) := le_of_lt (pow_pos hpi 2)
  have hden4 : 0 ≤ ((2 * Real.pi) ^ 4 : ℝ) := le_of_lt (pow_pos hpi 4)
  have hcoeff0 : 0 ≤ coeffLaplacianConst ξ 0 := by
    dsimp [coeffLaplacianConst, coeffDerivConst]
    positivity
  have hcoeffLL : 0 ≤ coeffLaplacianLaplacianConst ξ := by
    dsimp [coeffLaplacianLaplacianConst, coeffLaplacianConst, coeffDerivConst]
    positivity
  have hterm1 :
      0 ≤ ((2 : ℝ) / ((2 * Real.pi) ^ 2)) * coeffLaplacianConst ξ 0 := by
    exact mul_nonneg (div_nonneg (by positivity) hden2) hcoeff0
  have hterm2 :
      0 ≤ ((2 * Real.pi) ^ 4)⁻¹ * coeffLaplacianLaplacianConst ξ := by
    exact mul_nonneg (inv_nonneg.mpr hden4) hcoeffLL
  exact add_nonneg (add_nonneg (by positivity) hterm1) hterm2

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
        simp [Finset.sum_insert, ha]
      _ ≤ p (f a) + p (Finset.sum s f) := map_add_le_add p _ _
      _ ≤ p (f a) + Finset.sum s (fun x => p (f x)) := by
        exact add_le_add (le_rfl) ih
      _ = Finset.sum (insert a s) (fun x => p (f x)) := by
        simp [Finset.sum_insert, ha]

private lemma seminorm_fintype_sum_le {α : Type*} [Fintype α]
    {𝕜 E : Type*} [SeminormedRing 𝕜] [AddCommGroup E] [SMul 𝕜 E]
    (p : Seminorm 𝕜 E) (f : α → E) :
    p (∑ a : α, f a) ≤ ∑ a : α, p (f a) := by
  simpa using (seminorm_finset_sum_le (p := p) (s := (Finset.univ : Finset α)) (f := f))

private lemma laplacian_eq_sum_derivCoordCLM (f : TestFunction) :
    Δ f = ∑ i : Fin STDimension, derivCoordCLM i (derivCoordCLM i f) := by
  let b : OrthonormalBasis (Fin STDimension) ℝ SpaceTime := EuclideanSpace.basisFun (Fin STDimension) ℝ
  have hb : ∀ i : Fin STDimension, b i = unitVec i := by intro i; simp [b, unitVec]
  have hcoord2 (i : Fin STDimension) : ∂_{b i} (∂_{b i} f) = derivCoordCLM i (derivCoordCLM i f) := by
    rw [hb i]
    calc
      ∂_{unitVec i} (∂_{unitVec i} f) = ∂_{unitVec i} (derivCoordCLM i f) := by
        simp
      _ = derivCoordCLM i (derivCoordCLM i f) := by
        simp
  simpa [b, hb, hcoord2] using (SchwartzMap.laplacian_eq_sum (b := b) (f := f))

private lemma coeffDerivConst_nonneg (ξ : ℝ) (k : ℕ) : 0 ≤ coeffDerivConst ξ k := by
  dsimp [coeffDerivConst]
  positivity

private lemma coeffMulProd_nonneg (ξ : ℝ) (k n : ℕ) : 0 ≤ coeffMulProd ξ k n := by
  classical
  dsimp [coeffMulProd]
  refine Finset.prod_nonneg ?_
  intro j hj
  dsimp [coeffMulConst]
  positivity

private lemma coeffDerivProd_nonneg (ξ : ℝ) (k n : ℕ) : 0 ≤ coeffDerivProd ξ k n := by
  classical
  dsimp [coeffDerivProd]
  refine Finset.prod_nonneg ?_
  intro j hj
  exact coeffDerivConst_nonneg (ξ := ξ) (k := k + j)

private lemma coeffSeminormSeq_laplacian_le_sum (ξ : ℝ) (hξ : ξ ≠ 0) (k : ℕ) (f : TestFunction) :
    coeffSeminormSeq ξ hξ k (Δ f) ≤
      ∑ i : Fin STDimension, coeffSeminormSeq ξ hξ k (derivCoordCLM i (derivCoordCLM i f)) := by
  simpa [laplacian_eq_sum_derivCoordCLM] using
    (seminorm_fintype_sum_le (p := (coeffSeminormSeq ξ hξ k))
      (f := fun i : Fin STDimension => derivCoordCLM i (derivCoordCLM i f)))

private lemma coeffSeminormSeq_derivCoordCLM_le'
    (ξ : ℝ) (hξ : ξ ≠ 0) (k : ℕ) (i : Fin STDimension) (f : TestFunction) :
    coeffSeminormSeq ξ hξ k (derivCoordCLM i f) ≤ (coeffDerivConst ξ k) * coeffSeminormSeq ξ hξ (k + 1) f := by
  simpa [coeffDerivConst, Nat.add_assoc] using
    (coeffSeminormSeq_derivCoordCLM_le (ξ := ξ) (hξ := hξ) (i := i) (k := k) (f := f))

private lemma coeffSeminormSeq_derivCoordCLM_derivCoordCLM_le
    (ξ : ℝ) (hξ : ξ ≠ 0) (k : ℕ) (i : Fin STDimension) (f : TestFunction) :
    coeffSeminormSeq ξ hξ k (derivCoordCLM i (derivCoordCLM i f)) ≤
      (coeffDerivConst ξ k) * (coeffDerivConst ξ (k + 1)) * coeffSeminormSeq ξ hξ (k + 2) f := by
  have hk : 0 ≤ coeffDerivConst ξ k := coeffDerivConst_nonneg (ξ := ξ) (k := k)
  calc
    coeffSeminormSeq ξ hξ k (derivCoordCLM i (derivCoordCLM i f)) ≤
        (coeffDerivConst ξ k) * coeffSeminormSeq ξ hξ (k + 1) (derivCoordCLM i f) := by
          simpa using (coeffSeminormSeq_derivCoordCLM_le' (ξ := ξ) (hξ := hξ) (k := k) (i := i)
            (f := derivCoordCLM i f))
    _ ≤ (coeffDerivConst ξ k) * ((coeffDerivConst ξ (k + 1)) * coeffSeminormSeq ξ hξ (k + 2) f) := by
          exact mul_le_mul_of_nonneg_left
            (by
              simpa [Nat.add_assoc] using
                (coeffSeminormSeq_derivCoordCLM_le' (ξ := ξ) (hξ := hξ) (k := k + 1) (i := i) (f := f)))
            hk
    _ = (coeffDerivConst ξ k) * (coeffDerivConst ξ (k + 1)) * coeffSeminormSeq ξ hξ (k + 2) f := by
          ring

private lemma coeffSeminormSeq_laplacian_le (ξ : ℝ) (hξ : ξ ≠ 0) (k : ℕ) (f : TestFunction) :
    coeffSeminormSeq ξ hξ k (Δ f) ≤
      coeffLaplacianConst ξ k * coeffSeminormSeq ξ hξ (k + 2) f := by
  have hsum := coeffSeminormSeq_laplacian_le_sum (ξ := ξ) (hξ := hξ) (k := k) (f := f)
  set C : ℝ := (coeffDerivConst ξ k) * (coeffDerivConst ξ (k + 1)) * coeffSeminormSeq ξ hξ (k + 2) f
  have hterm : ∀ i : Fin STDimension, coeffSeminormSeq ξ hξ k (derivCoordCLM i (derivCoordCLM i f)) ≤ C := by
    intro i
    simpa [C, mul_assoc] using
      (coeffSeminormSeq_derivCoordCLM_derivCoordCLM_le (ξ := ξ) (hξ := hξ) (k := k) (i := i) (f := f))
  refine (hsum.trans ?_)
  simpa [coeffLaplacianConst, C, mul_assoc, mul_left_comm, mul_comm] using
    (sum_le_card_mul_of_pointwise_le
      (f := fun i : Fin STDimension => coeffSeminormSeq ξ hξ k (derivCoordCLM i (derivCoordCLM i f)))
      (C := C) hterm)

private lemma coeffSeminormSeq_zero_eq_norm_toLp (ξ : ℝ) (hξ : ξ ≠ 0) (f : TestFunction) :
    coeffSeminormSeq ξ hξ 0 f = ‖f.toLp 2 (volume : Measure SpaceTime)‖ := by
  have h :=
    coeffSeminormSeq_eq_norm_toLp_numAllPowCLM (ξ := ξ) (hξ := hξ) (k := 0) (f := f)
  rw [numAllPowCLM_zero (ξ := ξ)] at h
  rw [ContinuousLinearMap.one_apply] at h
  exact h

private lemma norm_toLp_le_coeffSeminormSeq (ξ : ℝ) (hξ : ξ ≠ 0) (k : ℕ) (f : TestFunction) :
    ‖f.toLp 2 (volume : Measure SpaceTime)‖ ≤ coeffSeminormSeq ξ hξ k f := by
  have hmono : Monotone (coeffSeminormSeq ξ hξ) := coeffSeminormSeq_mono ξ hξ
  have hf0 :
      ‖f.toLp 2 (volume : Measure SpaceTime)‖ = coeffSeminormSeq ξ hξ 0 f := by
    simpa using (coeffSeminormSeq_zero_eq_norm_toLp (ξ := ξ) (hξ := hξ) (f := f)).symm
  calc
    ‖f.toLp 2 (volume : Measure SpaceTime)‖ = coeffSeminormSeq ξ hξ 0 f := hf0
    _ ≤ coeffSeminormSeq ξ hξ k f := hmono (Nat.zero_le k) f

private lemma coeffSeminormSeq_zero_laplacian_le_coeffSeminormSeq_four (ξ : ℝ) (hξ : ξ ≠ 0) (f : TestFunction) :
    coeffSeminormSeq ξ hξ 0 (Δ f) ≤ coeffLaplacianConst ξ 0 * coeffSeminormSeq ξ hξ 4 f := by
  have hmono : Monotone (coeffSeminormSeq ξ hξ) := coeffSeminormSeq_mono ξ hξ
  have h24 : coeffSeminormSeq ξ hξ 2 f ≤ coeffSeminormSeq ξ hξ 4 f := hmono (by decide) f
  have hc : 0 ≤ coeffLaplacianConst ξ 0 := by
    dsimp [coeffLaplacianConst]
    positivity [coeffDerivConst_nonneg (ξ := ξ) (k := 0), coeffDerivConst_nonneg (ξ := ξ) (k := 1)]
  have hΔ : coeffSeminormSeq ξ hξ 0 (Δ f) ≤ coeffLaplacianConst ξ 0 * coeffSeminormSeq ξ hξ 2 f := by
    simpa [Nat.zero_add, mul_assoc] using
      (coeffSeminormSeq_laplacian_le (ξ := ξ) (hξ := hξ) (k := 0) (f := f))
  exact le_trans hΔ (mul_le_mul_of_nonneg_left h24 hc)

private lemma norm_toLp_laplacian_le_coeffSeminormSeq_four (ξ : ℝ) (hξ : ξ ≠ 0) (f : TestFunction) :
    ‖(Δ f).toLp 2 (volume : Measure SpaceTime)‖ ≤
      coeffLaplacianConst ξ 0 * coeffSeminormSeq ξ hξ 4 f := by
  have hcoeff := coeffSeminormSeq_zero_laplacian_le_coeffSeminormSeq_four (ξ := ξ) (hξ := hξ) (f := f)
  simpa [coeffSeminormSeq_zero_eq_norm_toLp (ξ := ξ) (hξ := hξ) (f := Δ f)] using hcoeff

private lemma coeffSeminormSeq_zero_laplacian_laplacian_le_coeffSeminormSeq_four (ξ : ℝ) (hξ : ξ ≠ 0)
    (f : TestFunction) :
    coeffSeminormSeq ξ hξ 0 (Δ (Δ f)) ≤
      coeffLaplacianLaplacianConst ξ * coeffSeminormSeq ξ hξ 4 f := by
  have hc0 : 0 ≤ coeffLaplacianConst ξ 0 := by
    dsimp [coeffLaplacianConst]
    positivity [coeffDerivConst_nonneg (ξ := ξ) (k := 0), coeffDerivConst_nonneg (ξ := ξ) (k := 1)]
  have h0 : coeffSeminormSeq ξ hξ 0 (Δ (Δ f)) ≤ coeffLaplacianConst ξ 0 * coeffSeminormSeq ξ hξ 2 (Δ f) := by
    simpa [Nat.zero_add, mul_assoc] using
      (coeffSeminormSeq_laplacian_le (ξ := ξ) (hξ := hξ) (k := 0) (f := Δ f))
  have h2 : coeffSeminormSeq ξ hξ 2 (Δ f) ≤ coeffLaplacianConst ξ 2 * coeffSeminormSeq ξ hξ 4 f := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, mul_assoc] using
      (coeffSeminormSeq_laplacian_le (ξ := ξ) (hξ := hξ) (k := 2) (f := f))
  have h := h0.trans <| mul_le_mul_of_nonneg_left h2 hc0
  simpa [coeffLaplacianLaplacianConst, mul_assoc] using h

private lemma norm_toLp_laplacian_laplacian_le_coeffSeminormSeq_four (ξ : ℝ) (hξ : ξ ≠ 0)
    (f : TestFunction) :
    ‖(Δ (Δ f)).toLp 2 (volume : Measure SpaceTime)‖ ≤
      coeffLaplacianLaplacianConst ξ * coeffSeminormSeq ξ hξ 4 f := by
  have hcoeff :=
    coeffSeminormSeq_zero_laplacian_laplacian_le_coeffSeminormSeq_four (ξ := ξ) (hξ := hξ) (f := f)
  simpa [coeffSeminormSeq_zero_eq_norm_toLp (ξ := ξ) (hξ := hξ) (f := Δ (Δ f))] using hcoeff

/-! ## A Sobolev bound for the Fourier weight `(1 + ‖ξ‖^2)^2` -/

private def sobolevWeight : SpaceTime → ℝ := fun ξ : SpaceTime =>
  (1 + ‖ξ‖ ^ 2) ^ 2

private def quadWeight : SpaceTime → ℝ := fun ξ : SpaceTime => ‖ξ‖ ^ 2

private lemma sobolevWeight_poly :
    sobolevWeight = fun ξ : SpaceTime ↦ (1 : ℝ) + (2 : ℝ) * quadWeight ξ + quadWeight ξ * quadWeight ξ := by
  funext ξ
  simp [sobolevWeight, quadWeight, pow_two]
  ring

private lemma quadWeight_hasTemperateGrowth : quadWeight.HasTemperateGrowth := by
  simpa [quadWeight] using (by
    fun_prop : (fun ξ : SpaceTime ↦ ‖ξ‖ ^ 2).HasTemperateGrowth)

private lemma quadWeight_sq_hasTemperateGrowth :
    (fun ξ : SpaceTime ↦ quadWeight ξ * quadWeight ξ).HasTemperateGrowth := by
  simpa [quadWeight] using (by
    fun_prop : (fun ξ : SpaceTime ↦ (‖ξ‖ ^ 2) * (‖ξ‖ ^ 2)).HasTemperateGrowth)

private lemma sobolevWeight_hasTemperateGrowth : (sobolevWeight : SpaceTime → ℝ).HasTemperateGrowth := by
  simpa [sobolevWeight] using (by
    fun_prop : (fun ξ : SpaceTime ↦ (1 + ‖ξ‖ ^ 2) ^ 2).HasTemperateGrowth)

private lemma two_mul_quadWeight_hasTemperateGrowth :
    (fun ξ : SpaceTime ↦ (2 : ℝ) * quadWeight ξ).HasTemperateGrowth := by
  simpa [quadWeight] using (by
    fun_prop : (fun ξ : SpaceTime ↦ (2 : ℝ) * ‖ξ‖ ^ 2).HasTemperateGrowth)

private lemma one_add_two_mul_quadWeight_hasTemperateGrowth :
    (fun ξ : SpaceTime ↦ (1 : ℝ) + (2 : ℝ) * quadWeight ξ).HasTemperateGrowth := by
  simpa [quadWeight] using (by
    fun_prop : (fun ξ : SpaceTime ↦ (1 : ℝ) + (2 : ℝ) * ‖ξ‖ ^ 2).HasTemperateGrowth)

private lemma fourierMultiplierCLM_add_apply {g₁ g₂ : SpaceTime → ℝ} (hg₁ : g₁.HasTemperateGrowth)
    (hg₂ : g₂.HasTemperateGrowth) (f : TestFunctionℂ) :
    SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) (g₁ + g₂) f =
      SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) g₁ f +
        SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) g₂ f := by
  simpa using
    congrArg (fun T => T f) (SchwartzMap.fourierMultiplierCLM_add (F := (ℂ)) hg₁ hg₂)

private lemma neg_two_mul_pi_sq_ne_zero : (-((2 * Real.pi) ^ 2 : ℝ)) ≠ 0 := by
  have hpos : 0 < ((2 * Real.pi) ^ 2 : ℝ) := by
    have : (0 : ℝ) < 2 * Real.pi := by positivity
    exact sq_pos_of_pos this
  exact neg_ne_zero.mpr (ne_of_gt hpos)

private lemma norm_inv_neg_two_mul_pi_sq :
    ‖(-((2 * Real.pi) ^ 2 : ℝ))⁻¹‖ = (1 : ℝ) / (2 * Real.pi) ^ 2 := by
  have hnonneg : 0 ≤ ((2 * Real.pi) ^ 2 : ℝ) := by positivity
  simp [Real.norm_of_nonneg hnonneg]

private lemma norm_two_mul_inv_neg_two_mul_pi_sq :
    ‖(2 : ℝ) * (-((2 * Real.pi) ^ 2 : ℝ))⁻¹‖ = (2 : ℝ) / (2 * Real.pi) ^ 2 := by
  calc
    ‖(2 : ℝ) * (-((2 * Real.pi) ^ 2 : ℝ))⁻¹‖ = ‖(2 : ℝ)‖ * ‖(-((2 * Real.pi) ^ 2 : ℝ))⁻¹‖ := by
      simp
    _ = (2 : ℝ) * ((1 : ℝ) / (2 * Real.pi) ^ 2) := by
      rw [Real.norm_of_nonneg (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), norm_inv_neg_two_mul_pi_sq]
    _ = (2 : ℝ) / (2 * Real.pi) ^ 2 := by simp [div_eq_mul_inv]

private lemma norm_inv_neg_two_mul_pi_sq_sq :
    ‖(-((2 * Real.pi) ^ 2 : ℝ))⁻¹ * (-((2 * Real.pi) ^ 2 : ℝ))⁻¹‖ = (1 : ℝ) / (2 * Real.pi) ^ 4 := by
  have h0 : (2 * Real.pi : ℝ) ≠ 0 := by
    have : (0 : ℝ) < 2 * Real.pi := by positivity
    exact ne_of_gt this
  calc
    ‖(-((2 * Real.pi) ^ 2 : ℝ))⁻¹ * (-((2 * Real.pi) ^ 2 : ℝ))⁻¹‖
        = ‖(-((2 * Real.pi) ^ 2 : ℝ))⁻¹‖ * ‖(-((2 * Real.pi) ^ 2 : ℝ))⁻¹‖ := by simp
    _ = ((1 : ℝ) / (2 * Real.pi) ^ 2) * ((1 : ℝ) / (2 * Real.pi) ^ 2) := by
          simp_rw [norm_inv_neg_two_mul_pi_sq]
    _ = (1 : ℝ) / (2 * Real.pi) ^ 4 := by
          field_simp [h0]

private lemma fourierMultiplierCLM_quadWeight_eq (g : TestFunctionℂ) :
    SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) quadWeight g =
      (-((2 * Real.pi) ^ 2 : ℝ))⁻¹ • Δ g := by
  set c : ℝ := -((2 * Real.pi) ^ 2 : ℝ)
  have hc : c ≠ 0 := by simp [c]
  have hlap : Δ g = c • SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) quadWeight g := by
    simpa [c, quadWeight] using (SchwartzMap.laplacian_eq_fourierMultiplierCLM (F := (ℂ)) (f := g))
  have hmul : c⁻¹ • Δ g = SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) quadWeight g := by
    have := congrArg (fun z : TestFunctionℂ => c⁻¹ • z) hlap
    simpa [smul_smul, hc] using this
  simpa [c] using hmul.symm

private lemma fourierMultiplierCLM_quadWeight_sq_eq (g : TestFunctionℂ) :
    SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) (fun ξ : SpaceTime ↦ quadWeight ξ * quadWeight ξ) g =
      (-((2 * Real.pi) ^ 2 : ℝ))⁻¹ • ((-((2 * Real.pi) ^ 2 : ℝ))⁻¹ • Δ (Δ g)) := by
  calc
    SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) (fun ξ : SpaceTime ↦ quadWeight ξ * quadWeight ξ) g
        =
        SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) quadWeight
          (SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) quadWeight g) := by
          simpa [Pi.mul_def] using
            (SchwartzMap.fourierMultiplierCLM_fourierMultiplierCLM_apply (F := (ℂ))
              (g₁ := quadWeight) (g₂ := quadWeight) quadWeight_hasTemperateGrowth
              quadWeight_hasTemperateGrowth g).symm
    _ = (-((2 * Real.pi) ^ 2 : ℝ))⁻¹ •
          SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) quadWeight (Δ g) := by
          simp [fourierMultiplierCLM_quadWeight_eq (g := g)]
    _ = (-((2 * Real.pi) ^ 2 : ℝ))⁻¹ • ((-((2 * Real.pi) ^ 2 : ℝ))⁻¹ • Δ (Δ g)) := by
          simp [fourierMultiplierCLM_quadWeight_eq (g := Δ g)]

private lemma fourierMultiplierCLM_two_mul_quadWeight_eq (g : TestFunctionℂ) :
    SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) (fun ξ : SpaceTime ↦ (2 : ℝ) * quadWeight ξ) g =
      (2 : ℝ) • SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) quadWeight g := by
  simpa [smul_eq_mul] using
    (SchwartzMap.fourierMultiplierCLM_smul_apply (F := (ℂ)) (hg := quadWeight_hasTemperateGrowth)
      (c := (2 : ℝ)) (f := g))

private lemma fourierMultiplierCLM_sobolevWeight_eq_add (g : TestFunctionℂ) :
    SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) sobolevWeight g =
      SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ)
          (fun ξ : SpaceTime ↦ (1 : ℝ) + (2 : ℝ) * quadWeight ξ) g
        + SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ)
          (fun ξ : SpaceTime ↦ quadWeight ξ * quadWeight ξ) g := by
  have hs :
      (sobolevWeight : SpaceTime → ℝ) =
        (fun ξ : SpaceTime ↦ (1 : ℝ) + (2 : ℝ) * quadWeight ξ)
          + (fun ξ : SpaceTime ↦ quadWeight ξ * quadWeight ξ) := by
    funext ξ
    simp [sobolevWeight_poly, add_assoc]
  simpa [hs] using
    (fourierMultiplierCLM_add_apply one_add_two_mul_quadWeight_hasTemperateGrowth
      quadWeight_sq_hasTemperateGrowth g)

private lemma fourierMultiplierCLM_one_add_two_mul_quadWeight_eq_add (g : TestFunctionℂ) :
    SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ)
          (fun ξ : SpaceTime ↦ (1 : ℝ) + (2 : ℝ) * quadWeight ξ) g =
      SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) (fun _ : SpaceTime ↦ (1 : ℝ)) g +
        SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ)
          (fun ξ : SpaceTime ↦ (2 : ℝ) * quadWeight ξ) g := by
  simpa using
    (fourierMultiplierCLM_add_apply (g₁ := fun _ : SpaceTime ↦ (1 : ℝ))
      (g₂ := fun ξ : SpaceTime ↦ (2 : ℝ) * quadWeight ξ) (by fun_prop)
      two_mul_quadWeight_hasTemperateGrowth g)

private lemma fourierMultiplierCLM_sobolevWeight_eq_sum (g : TestFunctionℂ) :
    SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) sobolevWeight g =
      SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) (fun _ : SpaceTime ↦ (1 : ℝ)) g
        + SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) (fun ξ : SpaceTime ↦ (2 : ℝ) * quadWeight ξ) g
        + SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) (fun ξ : SpaceTime ↦ quadWeight ξ * quadWeight ξ) g := by
  simpa [fourierMultiplierCLM_one_add_two_mul_quadWeight_eq_add, add_assoc] using
    (fourierMultiplierCLM_sobolevWeight_eq_add (g := g))

private lemma fourierMultiplierCLM_sobolevWeight_decomp (g : TestFunctionℂ) :
    SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) sobolevWeight g =
      g
        + (2 : ℝ) • SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) quadWeight g
        + SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) (fun ξ : SpaceTime ↦ quadWeight ξ * quadWeight ξ) g := by
  have hs := fourierMultiplierCLM_sobolevWeight_eq_sum (g := g)
  simpa [fourierMultiplierCLM_two_mul_quadWeight_eq, add_assoc] using hs

private lemma norm_toLp_two_smul_fourierMultiplierCLM_quadWeight_eq (g : TestFunctionℂ) :
    ‖((2 : ℝ) • SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) quadWeight g).toLp 2
          (volume : Measure SpaceTime)‖
      = ((2 : ℝ) / ((2 * Real.pi) ^ 2)) * ‖(Δ g).toLp 2 (volume : Measure SpaceTime)‖ := by
  let c : ℝ := (2 : ℝ) * (-((2 * Real.pi) ^ 2 : ℝ))⁻¹
  have toLp_smul (a : ℝ) (f : TestFunctionℂ) :
      (a • f).toLp 2 (volume : Measure SpaceTime) = a • f.toLp 2 (volume : Measure SpaceTime) := by
    rfl
  have hsmul :
      (2 : ℝ) • SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) quadWeight g = c • Δ g := by
    simp [c, fourierMultiplierCLM_quadWeight_eq (g := g), smul_smul]
  calc
    ‖((2 : ℝ) • SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) quadWeight g).toLp 2
          (volume : Measure SpaceTime)‖
        = ‖(c • Δ g).toLp 2 (volume : Measure SpaceTime)‖ := by
            simpa using
              congrArg (fun t : TestFunctionℂ => ‖t.toLp 2 (volume : Measure SpaceTime)‖) hsmul
    _ = ‖c • (Δ g).toLp 2 (volume : Measure SpaceTime)‖ := by
          simp [toLp_smul]
    _ = ‖c‖ * ‖(Δ g).toLp 2 (volume : Measure SpaceTime)‖ := by
          exact norm_smul _ _
    _ = ((2 : ℝ) / ((2 * Real.pi) ^ 2)) * ‖(Δ g).toLp 2 (volume : Measure SpaceTime)‖ := by
          have hc : ‖c‖ = ((2 : ℝ) / ((2 * Real.pi) ^ 2)) := by
            dsimp [c]
            simpa using norm_two_mul_inv_neg_two_mul_pi_sq
          rw [hc]
  aesop

private lemma norm_toLp_fourierMultiplierCLM_quadWeight_sq_eq (g : TestFunctionℂ) :
    ‖(SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ)
          (fun ξ : SpaceTime ↦ quadWeight ξ * quadWeight ξ) g).toLp 2
        (volume : Measure SpaceTime)‖
      = (1 / ((2 * Real.pi) ^ 4)) * ‖(Δ (Δ g)).toLp 2 (volume : Measure SpaceTime)‖ := by
  let d : ℝ := (-((2 * Real.pi) ^ 2 : ℝ))⁻¹ * (-((2 * Real.pi) ^ 2 : ℝ))⁻¹
  have toLp_smul (a : ℝ) (f : TestFunctionℂ) :
      (a • f).toLp 2 (volume : Measure SpaceTime) = a • f.toLp 2 (volume : Measure SpaceTime) := by
    rfl
  have hsmul :
      SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ)
          (fun ξ : SpaceTime ↦ quadWeight ξ * quadWeight ξ) g = d • Δ (Δ g) := by
    simp [d, fourierMultiplierCLM_quadWeight_sq_eq (g := g), smul_smul]
  calc
    ‖(SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ)
            (fun ξ : SpaceTime ↦ quadWeight ξ * quadWeight ξ) g).toLp 2
          (volume : Measure SpaceTime)‖
        = ‖(d • Δ (Δ g)).toLp 2 (volume : Measure SpaceTime)‖ := by
            simpa using
              congrArg (fun t : TestFunctionℂ => ‖t.toLp 2 (volume : Measure SpaceTime)‖) hsmul
    _ = ‖d • (Δ (Δ g)).toLp 2 (volume : Measure SpaceTime)‖ := by
          simp [toLp_smul]
    _ = ‖d‖ * ‖(Δ (Δ g)).toLp 2 (volume : Measure SpaceTime)‖ := by
          exact norm_smul _ _
    _ = (1 / ((2 * Real.pi) ^ 4)) * ‖(Δ (Δ g)).toLp 2 (volume : Measure SpaceTime)‖ := by
          have hd : ‖d‖ = (1 / ((2 * Real.pi) ^ 4)) := by
            dsimp [d]
            simpa using norm_inv_neg_two_mul_pi_sq_sq
          rw [hd]
  rfl

private lemma toLp_add_add_add_eq (μ : Measure SpaceTime) [μ.HasTemperateGrowth] (g u v : TestFunctionℂ) :
    (g + u + v).toLp 2 μ = g.toLp 2 μ + u.toLp 2 μ + v.toLp 2 μ := by
  let T : TestFunctionℂ →L[ℝ] ↥(Lp ℂ 2 μ) :=
    SchwartzMap.toLpCLM (𝕜 := ℝ) (F := ℂ) (E := SpaceTime) (p := (2 : ℝ≥0∞)) (μ := μ)
  simpa [T, SchwartzMap.toLpCLM_apply, add_assoc] using (by simp [add_assoc] : T (g + u + v) = T g + T u + T v)

private lemma norm_add_add_le {α : Type*} [SeminormedAddCommGroup α] (a b c : α) :
    ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
  calc
    ‖a + b + c‖ = ‖(a + b) + c‖ := by simp [add_assoc]
    _ ≤ ‖a + b‖ + ‖c‖ := norm_add_le _ _
    _ ≤ (‖a‖ + ‖b‖) + ‖c‖ := by
          gcongr
          exact norm_add_le _ _
    _ = ‖a‖ + ‖b‖ + ‖c‖ := by simp [add_assoc]

private lemma norm_toLp_le_of_eq_add_add_add (μ : Measure SpaceTime) [μ.HasTemperateGrowth]
    {h g u v : TestFunctionℂ}
    (hdecomp : h = g + u + v) :
    ‖h.toLp 2 μ‖ ≤ ‖g.toLp 2 μ‖ + ‖u.toLp 2 μ‖ + ‖v.toLp 2 μ‖ := by
  have htoLp : h.toLp 2 μ = g.toLp 2 μ + u.toLp 2 μ + v.toLp 2 μ := by
    calc
      h.toLp 2 μ = (g + u + v).toLp 2 μ := by
            simpa using congrArg (fun f : TestFunctionℂ => f.toLp 2 μ) hdecomp
      _ = g.toLp 2 μ + u.toLp 2 μ + v.toLp 2 μ := toLp_add_add_add_eq (μ := μ) (g := g) (u := u) (v := v)
  rw [htoLp]
  exact norm_add_add_le (g.toLp 2 μ) (u.toLp 2 μ) (v.toLp 2 μ)

private lemma norm_toLp_fourierMultiplierCLM_sobolevWeight_le (g : TestFunctionℂ) :
    ‖(SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) sobolevWeight g).toLp 2
        (volume : Measure SpaceTime)‖ ≤
      (1 : ℝ) * ‖g.toLp 2 (volume : Measure SpaceTime)‖
        + ((2 : ℝ) / ((2 * Real.pi) ^ 2)) * ‖(Δ g).toLp 2 (volume : Measure SpaceTime)‖
        + (1 / ((2 * Real.pi) ^ 4)) * ‖(Δ (Δ g)).toLp 2 (volume : Measure SpaceTime)‖ := by
  let μ : Measure SpaceTime := (volume : Measure SpaceTime)
  let h : TestFunctionℂ := SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) sobolevWeight g
  let u : TestFunctionℂ := (2 : ℝ) • SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) quadWeight g
  let v : TestFunctionℂ := SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ)
    (fun ξ : SpaceTime ↦ quadWeight ξ * quadWeight ξ) g
  have hdecomp : h = g + u + v := by
    simpa [h, u, v, add_assoc] using (fourierMultiplierCLM_sobolevWeight_decomp (g := g))
  have htri : ‖h.toLp 2 μ‖ ≤ ‖g.toLp 2 μ‖ + ‖u.toLp 2 μ‖ + ‖v.toLp 2 μ‖ :=
    norm_toLp_le_of_eq_add_add_add (μ := μ) hdecomp
  have hu : ‖u.toLp 2 μ‖ = ((2 : ℝ) / ((2 * Real.pi) ^ 2)) * ‖(Δ g).toLp 2 μ‖ := by
    simpa [u, μ] using (norm_toLp_two_smul_fourierMultiplierCLM_quadWeight_eq (g := g))
  have hv : ‖v.toLp 2 μ‖ = (1 / ((2 * Real.pi) ^ 4)) * ‖(Δ (Δ g)).toLp 2 μ‖ := by
    simpa [v, μ] using (norm_toLp_fourierMultiplierCLM_quadWeight_sq_eq (g := g))
  simpa [μ, h, one_mul, add_assoc, hu, hv] using htri

private lemma fourier_fourierMultiplierCLM_sobolevWeight_eq_smulLeftCLM (g : TestFunctionℂ) :
    𝓕 (SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) sobolevWeight g) =
      SchwartzMap.smulLeftCLM (F := ℂ) sobolevWeight (𝓕 g) := by
  exact
    SchwartzMap.fourier_fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) (g := sobolevWeight) (f := g)

private lemma norm_toLp_sobolevWeight_smul_fourier_ofReal_eq (f : TestFunction) :
    ‖(SchwartzMap.smulLeftCLM (F := ℂ) sobolevWeight (𝓕 (OSforGFF.ofRealSchwartz f))).toLp 2
          (volume : Measure SpaceTime)‖ =
      ‖(SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) sobolevWeight
            (OSforGFF.ofRealSchwartz f)).toLp 2 (volume : Measure SpaceTime)‖ := by
  let h : TestFunctionℂ :=
    SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) sobolevWeight (OSforGFF.ofRealSchwartz f)
  have hL2 := (SchwartzMap.norm_fourier_toL2_eq (f := h))
  simpa [h, fourier_fourierMultiplierCLM_sobolevWeight_eq_smulLeftCLM] using hL2

private lemma norm_toLp_ofRealSchwartz_le_coeffSeminormSeq_four (ξ : ℝ) (hξ : ξ ≠ 0) (f : TestFunction) :
    ‖(OSforGFF.ofRealSchwartz f).toLp 2 (volume : Measure SpaceTime)‖ ≤ coeffSeminormSeq ξ hξ 4 f := by
  calc
    ‖(OSforGFF.ofRealSchwartz f).toLp 2 (volume : Measure SpaceTime)‖ = ‖f.toLp 2 (volume : Measure SpaceTime)‖ :=
      norm_toLp_ofRealSchwartz_eq (f := f)
    _ ≤ coeffSeminormSeq ξ hξ 4 f :=
      norm_toLp_le_coeffSeminormSeq (ξ := ξ) (hξ := hξ) (k := 4) (f := f)

private lemma norm_toLp_laplacian_ofRealSchwartz_le_coeffSeminormSeq_four (ξ : ℝ) (hξ : ξ ≠ 0)
    (f : TestFunction) :
    ‖(Δ (OSforGFF.ofRealSchwartz f)).toLp 2 (volume : Measure SpaceTime)‖ ≤
      coeffLaplacianConst ξ 0 * coeffSeminormSeq ξ hξ 4 f := by
  calc
    ‖(Δ (OSforGFF.ofRealSchwartz f)).toLp 2 (volume : Measure SpaceTime)‖ = ‖(Δ f).toLp 2 (volume : Measure SpaceTime)‖ :=
      norm_toLp_laplacian_ofRealSchwartz_eq (f := f)
    _ ≤ coeffLaplacianConst ξ 0 * coeffSeminormSeq ξ hξ 4 f :=
      norm_toLp_laplacian_le_coeffSeminormSeq_four (ξ := ξ) (hξ := hξ) (f := f)

private lemma norm_toLp_laplacian_laplacian_ofRealSchwartz_le_coeffSeminormSeq_four (ξ : ℝ) (hξ : ξ ≠ 0)
    (f : TestFunction) :
    ‖(Δ (Δ (OSforGFF.ofRealSchwartz f))).toLp 2 (volume : Measure SpaceTime)‖ ≤
      coeffLaplacianLaplacianConst ξ * coeffSeminormSeq ξ hξ 4 f := by
  calc
    ‖(Δ (Δ (OSforGFF.ofRealSchwartz f))).toLp 2 (volume : Measure SpaceTime)‖ =
        ‖(Δ (Δ f)).toLp 2 (volume : Measure SpaceTime)‖ :=
      norm_toLp_laplacian_laplacian_ofRealSchwartz_eq (f := f)
    _ ≤ coeffLaplacianLaplacianConst ξ * coeffSeminormSeq ξ hξ 4 f :=
      norm_toLp_laplacian_laplacian_le_coeffSeminormSeq_four (ξ := ξ) (hξ := hξ) (f := f)

private lemma norm_toLp_sobolevWeight_smul_fourier_ofReal_le_coeffSeminormSeq
    (ξ : ℝ) (hξ : ξ ≠ 0) (f : TestFunction) :
    ‖(SchwartzMap.smulLeftCLM (F := ℂ) sobolevWeight (𝓕 (OSforGFF.ofRealSchwartz f))).toLp 2
          (volume : Measure SpaceTime)‖ ≤
      sobolevConst ξ * coeffSeminormSeq ξ hξ 4 f := by
  rw [norm_toLp_sobolevWeight_smul_fourier_ofReal_eq (f := f)]
  set g : TestFunctionℂ := OSforGFF.ofRealSchwartz f
  set c : ℝ := coeffSeminormSeq ξ hξ 4 f
  have hg : ‖g.toLp 2 (volume : Measure SpaceTime)‖ ≤ c := by
    simpa [g, c] using norm_toLp_ofRealSchwartz_le_coeffSeminormSeq_four (ξ := ξ) (hξ := hξ) (f := f)
  have hΔg : ‖(Δ g).toLp 2 (volume : Measure SpaceTime)‖ ≤ coeffLaplacianConst ξ 0 * c := by
    simpa [g, c] using norm_toLp_laplacian_ofRealSchwartz_le_coeffSeminormSeq_four (ξ := ξ) (hξ := hξ) (f := f)
  have hΔΔg : ‖(Δ (Δ g)).toLp 2 (volume : Measure SpaceTime)‖ ≤ coeffLaplacianLaplacianConst ξ * c := by
    simpa [g, c] using norm_toLp_laplacian_laplacian_ofRealSchwartz_le_coeffSeminormSeq_four (ξ := ξ) (hξ := hξ) (f := f)
  have h2 : ‖(SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) sobolevWeight g).toLp 2 (volume : Measure SpaceTime)‖ ≤
      (1 : ℝ) * c + ((2 : ℝ) / ((2 * Real.pi) ^ 2)) * (coeffLaplacianConst ξ 0 * c)
        + (1 / ((2 * Real.pi) ^ 4)) * (coeffLaplacianLaplacianConst ξ * c) :=
    le_trans (norm_toLp_fourierMultiplierCLM_sobolevWeight_le (g := g)) (add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left hg (by positivity)) (mul_le_mul_of_nonneg_left hΔg (by positivity)))
      (mul_le_mul_of_nonneg_left hΔΔg (by positivity)))
  have hEq : (1 : ℝ) * c + ((2 : ℝ) / ((2 * Real.pi) ^ 2)) * (coeffLaplacianConst ξ 0 * c)
        + (1 / ((2 * Real.pi) ^ 4)) * (coeffLaplacianLaplacianConst ξ * c) = sobolevConst ξ * c := by
    dsimp [sobolevConst]; ring
  have h2' :
      ‖(SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) sobolevWeight g).toLp 2
            (volume : Measure SpaceTime)‖ ≤ sobolevConst ξ * c := by
    exact le_trans h2 (le_of_eq hEq)
  simpa [g, c] using h2'

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
  -- Sobolev constant for the Fourier-weight `((1 + ‖·‖^2)^2)`.
  let Csob : ℝ := sobolevConst ξ
  have hCsob0 : 0 ≤ Csob := by
    simpa [Csob] using sobolevConst_nonneg ξ
  refine ⟨⟨Csob * A, mul_nonneg hCsob0 hA0⟩, ?_⟩
  intro f
  have hbound :
      ∀ x : SpaceTime, ‖x‖ ^ (0 : ℕ) * ‖iteratedFDeriv ℝ (0 : ℕ) f x‖ ≤
        (A * Csob) * coeffSeminormSeq ξ hξ 4 f := by
    let g : TestFunctionℂ := OSforGFF.ofRealSchwartz f
    let hW : TestFunctionℂ :=
      SchwartzMap.smulLeftCLM (F := ℂ) sobolevWeight (𝓕 g)
    have hW_le : ‖hW.toLp 2 (volume : Measure SpaceTime)‖ ≤ Csob * coeffSeminormSeq ξ hξ 4 f := by
      have h' :=
        norm_toLp_sobolevWeight_smul_fourier_ofReal_le_coeffSeminormSeq
          (ξ := ξ) (hξ := hξ) (f := f)
      simpa [g, hW, Csob] using h'
    intro x
    simp only [pow_zero, one_mul, norm_iteratedFDeriv_zero]
    have hx0 : ‖f x‖ = ‖g x‖ := by
      simp [g]
    have hx4 : ‖g x‖ ≤ A * ‖hW.toLp 2 (volume : Measure SpaceTime)‖ := by
      have hx :=
        norm_le_fourierWeightL2_mul_norm_toLp_fourierWeightInv_smul_fourier (g := g) (x := x)
      have hW' :
          SchwartzMap.smulLeftCLM (F := ℂ) (fun ξ : SpaceTime ↦ fourierWeightInv ξ) (𝓕 g) =
            SchwartzMap.smulLeftCLM (F := ℂ) sobolevWeight (𝓕 g) := by
        have hgrowthInv : (fun ξ : SpaceTime ↦ fourierWeightInv ξ).HasTemperateGrowth := by
          simpa [fourierWeightInv] using (by
            fun_prop : (fun ξ : SpaceTime ↦ (((((1 : ℝ) + ‖ξ‖ ^ 2) ^ (2 : ℝ)) : ℝ) : ℂ)).HasTemperateGrowth)
        ext ξ
        rw [SchwartzMap.smulLeftCLM_apply_apply (F := ℂ)
          (g := fun ξ : SpaceTime ↦ fourierWeightInv ξ) (hg := hgrowthInv) (𝓕 g) ξ]
        rw [SchwartzMap.smulLeftCLM_apply_apply (F := ℂ)
          (g := sobolevWeight) (hg := sobolevWeight_hasTemperateGrowth) (𝓕 g) ξ]
        simp [fourierWeightInv, sobolevWeight]
      have hx' : ‖g x‖ ≤
          A * ‖(SchwartzMap.smulLeftCLM (F := ℂ) (fun ξ : SpaceTime ↦ fourierWeightInv ξ) (𝓕 g)).toLp 2
                (volume : Measure SpaceTime)‖ := by
        simpa [A, wInv, fourierWeight, fourierWeightInv, Real.rpow_two] using hx
      have hW_toLp_eq :
          ‖(SchwartzMap.smulLeftCLM (F := ℂ) (fun ξ : SpaceTime ↦ fourierWeightInv ξ) (𝓕 g)).toLp 2
                (volume : Measure SpaceTime)‖
            = ‖hW.toLp 2 (volume : Measure SpaceTime)‖ := by
        simpa [hW] using congrArg
          (fun t : TestFunctionℂ => ‖t.toLp 2 (volume : Measure SpaceTime)‖) hW'
      calc
        ‖g x‖ ≤
            A * ‖(SchwartzMap.smulLeftCLM (F := ℂ) (fun ξ : SpaceTime ↦ fourierWeightInv ξ) (𝓕 g)).toLp 2
                  (volume : Measure SpaceTime)‖ := hx'
        _ = A * ‖hW.toLp 2 (volume : Measure SpaceTime)‖ := by rw [hW_toLp_eq]
    have hx5 : ‖f x‖ ≤ (A * Csob) * coeffSeminormSeq ξ hξ 4 f := by
      have hfx : ‖f x‖ ≤ A * ‖hW.toLp 2 (volume : Measure SpaceTime)‖ := by
        simpa [hx0] using hx4
      have hmul :
          A * ‖hW.toLp 2 (volume : Measure SpaceTime)‖ ≤
            A * (Csob * coeffSeminormSeq ξ hξ 4 f) :=
        mul_le_mul_of_nonneg_left hW_le hA0
      calc
        ‖f x‖ ≤ A * ‖hW.toLp 2 (volume : Measure SpaceTime)‖ := hfx
        _ ≤ A * (Csob * coeffSeminormSeq ξ hξ 4 f) := hmul
        _ = (A * Csob) * coeffSeminormSeq ξ hξ 4 f := by ring_nf
    exact hx5
  have hMp : 0 ≤ (A * Csob) * coeffSeminormSeq ξ hξ 4 f := by
    positivity
  have hsem := SchwartzMap.seminorm_le_bound (𝕜 := ℝ) (k := 0) (n := 0) f hMp hbound
  have hsem' : SchwartzMap.seminorm ℝ 0 0 f ≤ (Csob * A) * coeffSeminormSeq ξ hξ 4 f := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using hsem
  simpa [Seminorm.smul_apply, NNReal.smul_def, mul_assoc, mul_comm, mul_left_comm] using hsem'

/-! ## Iterated coordinate-derivative bounds for `coeffSeminormSeq` -/

private lemma coeffSeminormSeq_iteratedLineDerivOp_unitVec_le (ξ : ℝ) (hξ : ξ ≠ 0)
    {n : ℕ} (r : Fin n → Fin STDimension) (k₀ : ℕ) (f : TestFunction) :
    coeffSeminormSeq ξ hξ k₀ (∂^{fun j : Fin n ↦ unitVec (r j)} f) ≤
      coeffDerivProd ξ k₀ n * coeffSeminormSeq ξ hξ (k₀ + n) f := by
  classical
  induction n generalizing k₀ with
  | zero =>
    simp [coeffDerivProd]
  | succ n ih =>
    have hstep :
        coeffSeminormSeq ξ hξ k₀ (∂^{fun j : Fin (n + 1) ↦ unitVec (r j)} f) ≤
          coeffDerivConst ξ k₀ *
            coeffSeminormSeq ξ hξ (k₀ + 1) (∂^{fun j : Fin n ↦ unitVec (r j.succ)} f) := by
      simpa [coeffDerivConst, LineDeriv.iteratedLineDerivOp_succ_left, Fin.tail_def] using
        (coeffSeminormSeq_derivCoordCLM_le (ξ := ξ) (hξ := hξ) (i := r 0) (k := k₀)
          (∂^{fun j : Fin n ↦ unitVec (r j.succ)} f))
    have hrec := ih (fun j : Fin n ↦ r j.succ) (k₀ + 1)
    have hmul := mul_le_mul_of_nonneg_left hrec (coeffDerivConst_nonneg (ξ := ξ) (k := k₀))
    simpa [coeffDerivProd, Finset.prod_range_succ', Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
      mul_assoc, mul_left_comm, mul_comm] using (le_trans hstep hmul)

/-! ## Bounding general Schwartz seminorms by `coeffSeminormSeq` -/

private lemma schwartz_seminorm00_le_mul_coeffSeminormSeq
    (ξ : ℝ) (hξ : ξ ≠ 0) (C00 : ℝ≥0)
    (hC00 : ∀ f : TestFunction,
      SchwartzMap.seminorm ℝ 0 0 f ≤ ((C00 : ℝ≥0) • coeffSeminormSeq ξ hξ 4) f)
    (f : TestFunction) :
    SchwartzMap.seminorm ℝ 0 0 f ≤ (C00 : ℝ) * coeffSeminormSeq ξ hξ 4 f := by
  simpa [Seminorm.smul_apply, NNReal.smul_def, mul_assoc] using hC00 f

private lemma schwartz_seminorm00_iteratedLineDerivOp_unitVec_le
    (ξ : ℝ) (hξ : ξ ≠ 0) (C00 : ℝ≥0)
    (hC00 : ∀ f : TestFunction,
      SchwartzMap.seminorm ℝ 0 0 f ≤ ((C00 : ℝ≥0) • coeffSeminormSeq ξ hξ 4) f)
    {n : ℕ} (r : Fin n → Fin STDimension) (f : TestFunction) :
    SchwartzMap.seminorm ℝ 0 0 (∂^{fun j : Fin n ↦ unitVec (r j)} f) ≤
      (C00 : ℝ) * coeffDerivProd ξ 4 n * coeffSeminormSeq ξ hξ (4 + n) f := by
  have h00 :=
    schwartz_seminorm00_le_mul_coeffSeminormSeq (ξ := ξ) (hξ := hξ) (C00 := C00) (hC00 := hC00)
      (∂^{fun j : Fin n ↦ unitVec (r j)} f)
  have hder :
      coeffSeminormSeq ξ hξ 4 (∂^{fun j : Fin n ↦ unitVec (r j)} f) ≤
        coeffDerivProd ξ 4 n * coeffSeminormSeq ξ hξ (4 + n) f := by
    simpa [coeffDerivProd, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (coeffSeminormSeq_iteratedLineDerivOp_unitVec_le (ξ := ξ) (hξ := hξ) (r := r) (k₀ := 4) (f := f))
  have hmul := mul_le_mul_of_nonneg_left hder (by positivity : 0 ≤ (C00 : ℝ))
  have h := le_trans h00 (by simpa [mul_assoc] using hmul)
  simpa [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using h

private lemma schwartz_seminorm00_mulCoordCLM_iter_iteratedLineDerivOp_unitVec_le
    (ξ : ℝ) (hξ : ξ ≠ 0) (C00 : ℝ≥0)
    (hC00 : ∀ f : TestFunction,
      SchwartzMap.seminorm ℝ 0 0 f ≤ ((C00 : ℝ≥0) • coeffSeminormSeq ξ hξ 4) f)
    (k : ℕ) {n : ℕ} (i : Fin STDimension) (r : Fin n → Fin STDimension) (f : TestFunction) :
    SchwartzMap.seminorm ℝ 0 0
        (((mulCoordCLM i)^[k + 1]) (∂^{fun j : Fin n ↦ unitVec (r j)} f))
      ≤ (C00 : ℝ) * coeffMulProd ξ 4 (k + 1) * coeffDerivProd ξ (4 + (k + 1)) n *
          coeffSeminormSeq ξ hξ (4 + (k + 1) + n) f := by
  set g : TestFunction := ∂^{fun j : Fin n ↦ unitVec (r j)} f
  have h00 := schwartz_seminorm00_le_mul_coeffSeminormSeq (ξ := ξ) (hξ := hξ)
    (C00 := C00) (hC00 := hC00) (((mulCoordCLM i)^[k + 1]) g)
  have hmul := coeffSeminormSeq_mulCoordCLM_iter_le (ξ := ξ) (hξ := hξ) i 4 (k + 1) g
  have hder :=
    coeffSeminormSeq_iteratedLineDerivOp_unitVec_le (ξ := ξ) (hξ := hξ)
      (r := r) (k₀ := 4 + (k + 1)) f
  have hmul' :
      (C00 : ℝ) * coeffSeminormSeq ξ hξ 4 (((mulCoordCLM i)^[k + 1]) g) ≤
        (C00 : ℝ) * (coeffMulProd ξ 4 (k + 1) * coeffSeminormSeq ξ hξ (4 + (k + 1)) g) := by
    exact mul_le_mul_of_nonneg_left hmul (by exact_mod_cast C00.2)
  have hder' :
      (C00 : ℝ) * (coeffMulProd ξ 4 (k + 1) * coeffSeminormSeq ξ hξ (4 + (k + 1)) g) ≤
        (C00 : ℝ) *
          (coeffMulProd ξ 4 (k + 1) *
            (coeffDerivProd ξ (4 + (k + 1)) n * coeffSeminormSeq ξ hξ (4 + (k + 1) + n) f)) := by
    -- apply the derivative bound to `g = ∂^{unitVec∘r} f`
    have hder_g :
        coeffSeminormSeq ξ hξ (4 + (k + 1)) g ≤
          coeffDerivProd ξ (4 + (k + 1)) n * coeffSeminormSeq ξ hξ (4 + (k + 1) + n) f := by
      simpa [g] using hder
    have hmul2 :
        coeffMulProd ξ 4 (k + 1) * coeffSeminormSeq ξ hξ (4 + (k + 1)) g ≤
          coeffMulProd ξ 4 (k + 1) *
            (coeffDerivProd ξ (4 + (k + 1)) n * coeffSeminormSeq ξ hξ (4 + (k + 1) + n) f) := by
      have hCmul : 0 ≤ coeffMulProd ξ 4 (k + 1) :=
        coeffMulProd_nonneg (ξ := ξ) (k := 4) (n := k + 1)
      exact mul_le_mul_of_nonneg_left hder_g hCmul
    exact mul_le_mul_of_nonneg_left hmul2 (by exact_mod_cast C00.2)
  have h := le_trans h00 (le_trans hmul' hder')
  simpa [g, mul_assoc, mul_left_comm, mul_comm] using h

private lemma schwartz_seminorm_zero_le_mul_coeffSeminormSeq_of_seminorm0
    (ξ : ℝ) (hξ : ξ ≠ 0) (C00 : ℝ≥0)
    (hC00 : ∀ f : TestFunction,
      SchwartzMap.seminorm ℝ 0 0 f ≤ ((C00 : ℝ≥0) • coeffSeminormSeq ξ hξ 4) f)
    (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : TestFunction,
      SchwartzMap.seminorm ℝ 0 n f ≤ C * coeffSeminormSeq ξ hξ (4 + n) f := by
  classical
  let d : ℝ := (Fintype.card (Fin STDimension) : ℝ)
  let cardR : ℝ := (Fintype.card (Fin n → Fin STDimension) : ℝ)
  let C : ℝ := (d ^ n) * cardR * (C00 : ℝ) * coeffDerivProd ξ 4 n
  refine ⟨C, ?_, ?_⟩
  · have hd : 0 ≤ d := by
      dsimp [d]
      exact Nat.cast_nonneg _
    have hcardR : 0 ≤ cardR := by
      dsimp [cardR]
      exact Nat.cast_nonneg _
    have hdn : 0 ≤ d ^ n := pow_nonneg hd _
    have hC00' : 0 ≤ (C00 : ℝ) := by
      exact (show (0 : ℝ) ≤ (C00 : ℝ≥0) from C00.2)
    have hder : 0 ≤ coeffDerivProd ξ 4 n :=
      coeffDerivProd_nonneg (ξ := ξ) (k := 4) (n := n)
    dsimp [C]
    have h1 : 0 ≤ (d ^ n) * cardR := mul_nonneg hdn hcardR
    have h2 : 0 ≤ (d ^ n) * cardR * (C00 : ℝ) := mul_nonneg h1 hC00'
    exact mul_nonneg h2 hder
  · intro f
    have h0 := schwartz_seminorm0_le_card_pow_mul_sum_seminorm0 (n := n) (f := f)
    have hsum :
        (∑ r : (Fin n → Fin STDimension),
            SchwartzMap.seminorm ℝ 0 0 (∂^{fun j : Fin n ↦ unitVec (r j)} f))
          ≤ cardR * ((C00 : ℝ) * coeffDerivProd ξ 4 n * coeffSeminormSeq ξ hξ (4 + n) f) := by
      have :
          (∑ r : (Fin n → Fin STDimension),
              SchwartzMap.seminorm ℝ 0 0 (∂^{fun j : Fin n ↦ unitVec (r j)} f))
            ≤ (Fintype.card (Fin n → Fin STDimension) : ℝ) *
                ((C00 : ℝ) * coeffDerivProd ξ 4 n * coeffSeminormSeq ξ hξ (4 + n) f) := by
        refine sum_le_card_mul_of_pointwise_le
          (f := fun r : (Fin n → Fin STDimension) =>
            SchwartzMap.seminorm ℝ 0 0 (∂^{fun j : Fin n ↦ unitVec (r j)} f))
          (C := (C00 : ℝ) * coeffDerivProd ξ 4 n * coeffSeminormSeq ξ hξ (4 + n) f) ?_
        intro r
        simpa [mul_assoc] using
          schwartz_seminorm00_iteratedLineDerivOp_unitVec_le
            (ξ := ξ) (hξ := hξ) (C00 := C00) (hC00 := hC00) (r := r) (f := f)
      simpa [cardR] using this
    have hmul :
        ((Fintype.card (Fin STDimension) : ℝ) ^ n) *
            (∑ r : (Fin n → Fin STDimension),
              SchwartzMap.seminorm ℝ 0 0 (∂^{fun j : Fin n ↦ unitVec (r j)} f))
          ≤ ((Fintype.card (Fin STDimension) : ℝ) ^ n) *
              (cardR * ((C00 : ℝ) * coeffDerivProd ξ 4 n * coeffSeminormSeq ξ hξ (4 + n) f)) := by
      refine mul_le_mul_of_nonneg_left hsum ?_
      have hd : 0 ≤ (Fintype.card (Fin STDimension) : ℝ) := Nat.cast_nonneg _
      exact pow_nonneg hd _
    have h1 := le_trans h0 hmul
    simpa [C, d, cardR, mul_assoc, mul_left_comm, mul_comm] using h1

private lemma schwartz_seminorm_zero_le_coeffSeminormSeq_of_seminorm0
    (ξ : ℝ) (hξ : ξ ≠ 0) (C00 : ℝ≥0)
    (hC00 : ∀ f : TestFunction,
      SchwartzMap.seminorm ℝ 0 0 f ≤ ((C00 : ℝ≥0) • coeffSeminormSeq ξ hξ 4) f)
    (n : ℕ) :
    ∃ C : ℝ≥0, ∀ f : TestFunction,
      SchwartzMap.seminorm ℝ 0 n f ≤ ((C : ℝ≥0) • coeffSeminormSeq ξ hξ (4 + n)) f := by
  rcases schwartz_seminorm_zero_le_mul_coeffSeminormSeq_of_seminorm0
    (ξ := ξ) (hξ := hξ) (C00 := C00) (hC00 := hC00) n with ⟨C, hC0, hC⟩
  refine ⟨⟨C, hC0⟩, ?_⟩
  intro f
  simpa [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul, mul_assoc] using hC f

private lemma schwartz_seminorm_succ_le_coeffSeminormSeq_of_seminorm0
    (ξ : ℝ) (hξ : ξ ≠ 0) (C00 : ℝ≥0)
    (hC00 : ∀ f : TestFunction,
      SchwartzMap.seminorm ℝ 0 0 f ≤ ((C00 : ℝ≥0) • coeffSeminormSeq ξ hξ 4) f)
    (k n : ℕ) :
    ∃ C : ℝ≥0, ∀ f : TestFunction,
      SchwartzMap.seminorm ℝ (k + 1) n f ≤
        ((C : ℝ≥0) • coeffSeminormSeq ξ hξ (4 + (k + 1) + n)) f := by
  -- dimension constant
  let d : ℝ := (Fintype.card (Fin STDimension) : ℝ)
  -- size of the `r : Fin n → Fin STDimension` index set
  let cardR : ℝ := (Fintype.card (Fin n → Fin STDimension) : ℝ)
  -- include coordinate weights (use a crude bound via a sum of coordinate monomials)
  let Cmul : ℝ := coeffMulProd ξ 4 (k + 1)
  let Cder : ℝ := coeffDerivProd ξ (4 + (k + 1)) n
  let C : ℝ := (d ^ k) * (d ^ n) * d * cardR * (C00 : ℝ) * Cmul * Cder
  refine ⟨⟨C, by
    have hCmul : 0 ≤ Cmul := by
      simpa [Cmul] using coeffMulProd_nonneg (ξ := ξ) (k := 4) (n := k + 1)
    have hCder : 0 ≤ Cder := by
      simpa [Cder] using coeffDerivProd_nonneg (ξ := ξ) (k := 4 + (k + 1)) (n := n)
    dsimp [C]
    have hd : 0 ≤ d := by
      dsimp [d]
      exact Nat.cast_nonneg _
    have hcardR : 0 ≤ cardR := by
      dsimp [cardR]
      exact Nat.cast_nonneg _
    have hdkn : 0 ≤ d ^ k := by exact pow_nonneg hd _
    have hdn : 0 ≤ d ^ n := by exact pow_nonneg hd _
    have hC00' : 0 ≤ (C00 : ℝ) := by exact (show (0 : ℝ) ≤ (C00 : ℝ≥0) from C00.2)
    -- close the goal by chaining `mul_nonneg`
    have h1 : 0 ≤ (d ^ k) * (d ^ n) := mul_nonneg hdkn hdn
    have h2 : 0 ≤ (d ^ k) * (d ^ n) * d := mul_nonneg h1 hd
    have h3 : 0 ≤ (d ^ k) * (d ^ n) * d * cardR := mul_nonneg h2 hcardR
    have h4 : 0 ≤ (d ^ k) * (d ^ n) * d * cardR * (C00 : ℝ) := mul_nonneg h3 hC00'
    have h5 : 0 ≤ (d ^ k) * (d ^ n) * d * cardR * (C00 : ℝ) * Cmul := mul_nonneg h4 hCmul
    have h6 : 0 ≤ (d ^ k) * (d ^ n) * d * cardR * (C00 : ℝ) * Cmul * Cder := mul_nonneg h5 hCder
    exact h6⟩, ?_⟩
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
    have hterm (i : Fin STDimension) (r : Fin n → Fin STDimension) :
        SchwartzMap.seminorm ℝ 0 0 (((mulCoordCLM i)^[k + 1]) (∂^{fun j : Fin n ↦ unitVec (r j)} f))
          ≤ (C00 : ℝ) * Cmul * Cder * coeffSeminormSeq ξ hξ (4 + (k + 1) + n) f := by
      have h :=
        schwartz_seminorm00_mulCoordCLM_iter_iteratedLineDerivOp_unitVec_le
          (ξ := ξ) (hξ := hξ) (C00 := C00) (hC00 := hC00) (k := k) (i := i) (r := r) (f := f)
      simpa [Cmul, Cder, mul_assoc, mul_left_comm, mul_comm] using h
    have hsum :
        (∑ i : Fin STDimension, ∑ r : (Fin n → Fin STDimension),
            SchwartzMap.seminorm ℝ 0 0
              (((mulCoordCLM i)^[k + 1]) (∂^{fun j : Fin n ↦ unitVec (r j)} f)))
          ≤ (d * cardR) *
              ((C00 : ℝ) * Cmul * Cder * coeffSeminormSeq ξ hξ (4 + (k + 1) + n) f) := by
      have hsum' :
          (∑ i : Fin STDimension, ∑ r : (Fin n → Fin STDimension),
              SchwartzMap.seminorm ℝ 0 0
                (((mulCoordCLM i)^[k + 1]) (∂^{fun j : Fin n ↦ unitVec (r j)} f)))
            ≤ (Fintype.card (Fin STDimension) : ℝ) *
                ((Fintype.card (Fin n → Fin STDimension) : ℝ) *
                  ((C00 : ℝ) * Cmul * Cder * coeffSeminormSeq ξ hξ (4 + (k + 1) + n) f)) := by
        exact
          sum_sum_le_card_mul_of_pointwise_le
            (f := fun i : Fin STDimension =>
              fun r : (Fin n → Fin STDimension) =>
                SchwartzMap.seminorm ℝ 0 0
                  (((mulCoordCLM i)^[k + 1]) (∂^{fun j : Fin n ↦ unitVec (r j)} f)))
            (C := (C00 : ℝ) * Cmul * Cder * coeffSeminormSeq ξ hξ (4 + (k + 1) + n) f)
            hterm
      simpa [d, cardR, mul_assoc, mul_left_comm, mul_comm] using hsum'
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
  rw [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul]
  exact this

private lemma schwartz_seminorm_le_coeffSeminormSeq_of_seminorm0
    (ξ : ℝ) (hξ : ξ ≠ 0) (C00 : ℝ≥0)
    (hC00 : ∀ f : TestFunction,
      SchwartzMap.seminorm ℝ 0 0 f ≤ ((C00 : ℝ≥0) • coeffSeminormSeq ξ hξ 4) f)
    (k n : ℕ) :
    ∃ C : ℝ≥0, ∀ f : TestFunction,
      SchwartzMap.seminorm ℝ k n f ≤ ((C : ℝ≥0) • coeffSeminormSeq ξ hξ (4 + k + n)) f := by
  cases k with
  | zero =>
    simpa using
      schwartz_seminorm_zero_le_coeffSeminormSeq_of_seminorm0
        (ξ := ξ) (hξ := hξ) (C00 := C00) (hC00 := hC00) (n := n)
  | succ k =>
    simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      schwartz_seminorm_succ_le_coeffSeminormSeq_of_seminorm0
        (ξ := ξ) (hξ := hξ) (C00 := C00) (hC00 := hC00) (k := k) (n := n)

/-! ## Main bound: Schwartz seminorm sequence by coefficient seminorm sequence -/

theorem isBounded_coeffSeminormSeq_schwartzSeminormSeq (ξ : ℝ) (hξ : ξ ≠ 0) :
    Seminorm.IsBounded (coeffSeminormSeq ξ hξ) OSforGFF.schwartzSeminormSeq (LinearMap.id) := by
  rcases schwartz_seminorm0_le_coeffSeminormSeq_four (ξ := ξ) (hξ := hξ) with ⟨C00, hC00⟩
  have hfamily :
      Seminorm.IsBounded (coeffSeminormSeq ξ hξ) OSforGFF.schwartzSeminormFamily_TestFunction
        (LinearMap.id) := by
    intro km
    rcases km with ⟨k, n⟩
    rcases schwartz_seminorm_le_coeffSeminormSeq_of_seminorm0 (ξ := ξ) (hξ := hξ) (C00 := C00)
      (hC00 := hC00) k n with ⟨C, hC⟩
    refine ⟨{4 + k + n}, C, ?_⟩
    intro f
    simpa [Seminorm.comp_apply] using (hC f)
  intro n
  rcases (Seminorm.isBounded_sup (p := coeffSeminormSeq ξ hξ)
      (q := OSforGFF.schwartzSeminormFamily_TestFunction) (f := LinearMap.id) hfamily
      (s' := Finset.Iic (n, n))) with ⟨C, s, hs⟩
  refine ⟨s, C, ?_⟩
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
