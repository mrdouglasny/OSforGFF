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

private lemma sum_sum_le_card_mul_of_pointwise_le {α β : Type*} [Fintype α] [Fintype β]
    {f : α → β → ℝ} {C : ℝ} (hf : ∀ a : α, ∀ b : β, f a b ≤ C) :
    (∑ a : α, ∑ b : β, f a b) ≤ (Fintype.card α : ℝ) * (Fintype.card β : ℝ) * C := by
  have hβ (a : α) : (∑ b : β, f a b) ≤ (Fintype.card β : ℝ) * C := by
    simpa using sum_le_card_mul_of_pointwise_le (f := fun b : β => f a b) (C := C) (hf a)
  have hα :
      (∑ a : α, ∑ b : β, f a b) ≤
        (Fintype.card α : ℝ) * ((Fintype.card β : ℝ) * C) := by
    refine sum_le_card_mul_of_pointwise_le (f := fun a : α => ∑ b : β, f a b)
      (C := (Fintype.card β : ℝ) * C) ?_
    intro a
    exact hβ a
  simpa [mul_assoc] using hα

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
            simp [mul_assoc,]
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

private lemma norm_le_fourierWeightL2_mul_norm_toLp_fourierWeightInv_smul_fourier
    (g : TestFunctionℂ) (x : SpaceTime) :
    ‖g x‖ ≤
      ((∫ ξ : SpaceTime, ‖fourierWeight ξ‖ ^ (2 : ℝ) ∂(volume : Measure SpaceTime)) ^ (1 / (2 : ℝ))) *
        ‖(SchwartzMap.smulLeftCLM (F := ℂ) (fun ξ : SpaceTime ↦ fourierWeightInv ξ) (𝓕 g)).toLp 2
            (volume : Measure SpaceTime)‖ := by
  have hx1 : ‖g x‖ ≤ ∫ ξ : SpaceTime, ‖(𝓕 g) ξ‖ ∂(volume : Measure SpaceTime) :=
    norm_le_integral_norm_fourier g x
  have hx2 := integral_norm_fourier_le_weighted_L2' (g := g)
  -- rewrite the second Hölder factor as an `L²` norm
  let hW : TestFunctionℂ :=
    SchwartzMap.smulLeftCLM (F := ℂ) (fun ξ : SpaceTime ↦ fourierWeightInv ξ) (𝓕 g)
  have hW_eq :
      ((∫ ξ : SpaceTime, ‖fourierWeightInv ξ • (𝓕 g) ξ‖ ^ (2 : ℝ)
            ∂(volume : Measure SpaceTime)) ^ (1 / (2 : ℝ)))
        = ‖hW.toLp 2 (volume : Measure SpaceTime)‖ := by
    have hint :
        (∫ ξ : SpaceTime, ‖fourierWeightInv ξ • (𝓕 g) ξ‖ ^ (2 : ℝ) ∂(volume : Measure SpaceTime)) =
          ∫ ξ : SpaceTime, ‖hW ξ‖ ^ (2 : ℝ) ∂(volume : Measure SpaceTime) := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards with ξ'
      have hgrowth : (fun ξ : SpaceTime ↦ fourierWeightInv ξ).HasTemperateGrowth := by
        simpa [fourierWeightInv] using (by
          fun_prop :
            (fun ξ : SpaceTime ↦ (((((1 : ℝ) + ‖ξ‖ ^ 2) ^ (2 : ℝ)) : ℝ) : ℂ)).HasTemperateGrowth)
      have happly :
          hW ξ' = fourierWeightInv ξ' • (𝓕 g) ξ' := by
        simpa [hW] using
          (SchwartzMap.smulLeftCLM_apply_apply (F := ℂ)
            (g := fun ξ : SpaceTime ↦ fourierWeightInv ξ) (hg := hgrowth) (𝓕 g) ξ')
      -- rewrite the integrand using `happly`
      simp [happly]
    have hLp : (∫ ξ : SpaceTime, ‖hW ξ‖ ^ (2 : ℝ) ∂(volume : Measure SpaceTime)) ^ (1 / (2 : ℝ))
        = ‖hW.toLp 2 (volume : Measure SpaceTime)‖ :=
      integral_norm_rpow_two_rpow_inv_eq_norm_toLp (h := hW)
    -- rewrite by `hint` then apply `hLp`
    rw [hint]
    exact hLp
  have hx2' :
      (∫ ξ : SpaceTime, ‖(𝓕 g) ξ‖ ∂(volume : Measure SpaceTime)) ≤
        ((∫ ξ : SpaceTime, ‖fourierWeight ξ‖ ^ (2 : ℝ) ∂(volume : Measure SpaceTime)) ^ (1 / (2 : ℝ))) *
          ‖hW.toLp 2 (volume : Measure SpaceTime)‖ := by
    -- `hx2` is stated with `fourierWeightInv` explicitly
    have hx2' := hx2
    rw [hW_eq] at hx2'
    exact hx2'
  -- combine the pointwise bound with the weighted Hölder bound
  have := le_trans hx1 hx2'
  simpa [hW] using this

/-! ## Laplacian bounds in coefficient seminorms -/

private def coeffDerivConst (ξ : ℝ) : ℕ → ℝ := fun k =>
  ‖(1 / (2 * ξ) : ℝ)‖ * Real.sqrt 2 * ((2 : ℝ) ^ k + 1)

/-- Dimension-dependent constant controlling the Sobolev weight `sobolevWeight` by
`‖·‖₂`, `‖Δ·‖₂`, `‖Δ²·‖₂`, then by `coeffSeminormSeq .. 4`. -/
private def sobolevConst (ξ : ℝ) : ℝ :=
  let d : ℕ → ℝ := coeffDerivConst ξ
  let CΔ : ℝ := (Fintype.card (Fin STDimension) : ℝ) * (d 0) * (d 1)
  let CΔΔ : ℝ := (Fintype.card (Fin STDimension) : ℝ) ^ 2 * (d 0) * (d 1) * (d 2) * (d 3)
  (1 : ℝ) + ((2 : ℝ) / ((2 * Real.pi) ^ 2)) * CΔ + ((2 * Real.pi) ^ 4)⁻¹ * CΔΔ

private lemma sobolevConst_nonneg (ξ : ℝ) : 0 ≤ sobolevConst ξ := by
  dsimp [sobolevConst, coeffDerivConst]
  positivity

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

private lemma norm_toLp_laplacian_le_coeffSeminormSeq_four (ξ : ℝ) (hξ : ξ ≠ 0) (f : TestFunction) :
    ‖(Δ f).toLp 2 (volume : Measure SpaceTime)‖ ≤
      ((Fintype.card (Fin STDimension) : ℝ) * coeffDerivConst ξ 0 * coeffDerivConst ξ 1) *
        coeffSeminormSeq ξ hξ 4 f := by
  have hmono : Monotone (coeffSeminormSeq ξ hξ) := coeffSeminormSeq_mono ξ hξ
  have h24 : coeffSeminormSeq ξ hξ 2 f ≤ coeffSeminormSeq ξ hξ 4 f := hmono (by decide) f
  set c : ℝ := (Fintype.card (Fin STDimension) : ℝ) * coeffDerivConst ξ 0 * coeffDerivConst ξ 1
  have hc : 0 ≤ c := by
    dsimp [c]
    exact mul_nonneg
      (mul_nonneg (by positivity) (coeffDerivConst_nonneg (ξ := ξ) (k := 0)))
      (coeffDerivConst_nonneg (ξ := ξ) (k := 1))
  have hΔ :
      coeffSeminormSeq ξ hξ 0 (Δ f) ≤ c * coeffSeminormSeq ξ hξ 2 f := by
    have h := coeffSeminormSeq_laplacian_le (ξ := ξ) (hξ := hξ) (k := 0) (f := f)
    simpa [c, Nat.zero_add, mul_assoc] using h
  have hΔ' : c * coeffSeminormSeq ξ hξ 2 f ≤ c * coeffSeminormSeq ξ hξ 4 f :=
    mul_le_mul_of_nonneg_left h24 hc
  have hcoeff : coeffSeminormSeq ξ hξ 0 (Δ f) ≤ c * coeffSeminormSeq ξ hξ 4 f :=
    le_trans hΔ hΔ'
  calc
    ‖(Δ f).toLp 2 (volume : Measure SpaceTime)‖ = coeffSeminormSeq ξ hξ 0 (Δ f) := by
      simpa using
        (coeffSeminormSeq_zero_eq_norm_toLp (ξ := ξ) (hξ := hξ) (f := Δ f)).symm
    _ ≤ c * coeffSeminormSeq ξ hξ 4 f := hcoeff

private lemma norm_toLp_laplacian_laplacian_le_coeffSeminormSeq_four (ξ : ℝ) (hξ : ξ ≠ 0)
    (f : TestFunction) :
    ‖(Δ (Δ f)).toLp 2 (volume : Measure SpaceTime)‖ ≤
      ((Fintype.card (Fin STDimension) : ℝ) ^ 2 * coeffDerivConst ξ 0 * coeffDerivConst ξ 1 *
            coeffDerivConst ξ 2 * coeffDerivConst ξ 3) *
        coeffSeminormSeq ξ hξ 4 f := by
  have hmono : Monotone (coeffSeminormSeq ξ hξ) := coeffSeminormSeq_mono ξ hξ
  set c0 : ℝ := (Fintype.card (Fin STDimension) : ℝ) * coeffDerivConst ξ 0 * coeffDerivConst ξ 1
  set c2 : ℝ := (Fintype.card (Fin STDimension) : ℝ) * coeffDerivConst ξ 2 * coeffDerivConst ξ 3
  have hc0 : 0 ≤ c0 := by
    dsimp [c0]
    exact mul_nonneg
      (mul_nonneg (by positivity) (coeffDerivConst_nonneg (ξ := ξ) (k := 0)))
      (coeffDerivConst_nonneg (ξ := ξ) (k := 1))
  have hc2 : 0 ≤ c2 := by
    dsimp [c2]
    exact mul_nonneg
      (mul_nonneg (by positivity) (coeffDerivConst_nonneg (ξ := ξ) (k := 2)))
      (coeffDerivConst_nonneg (ξ := ξ) (k := 3))
  have h0 :
      coeffSeminormSeq ξ hξ 0 (Δ (Δ f)) ≤ c0 * coeffSeminormSeq ξ hξ 2 (Δ f) := by
    have h := coeffSeminormSeq_laplacian_le (ξ := ξ) (hξ := hξ) (k := 0) (f := Δ f)
    simpa [c0, Nat.zero_add, mul_assoc] using h
  have h2 :
      coeffSeminormSeq ξ hξ 2 (Δ f) ≤ c2 * coeffSeminormSeq ξ hξ 4 f := by
    have h := coeffSeminormSeq_laplacian_le (ξ := ξ) (hξ := hξ) (k := 2) (f := f)
    simpa [c2, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, mul_assoc] using h
  have hmul : c0 * coeffSeminormSeq ξ hξ 2 (Δ f) ≤ c0 * (c2 * coeffSeminormSeq ξ hξ 4 f) :=
    mul_le_mul_of_nonneg_left h2 hc0
  have hcoeff :
      coeffSeminormSeq ξ hξ 0 (Δ (Δ f)) ≤ c0 * (c2 * coeffSeminormSeq ξ hξ 4 f) :=
    le_trans h0 hmul
  have hscal :
      c0 * (c2 * coeffSeminormSeq ξ hξ 4 f) =
        ((Fintype.card (Fin STDimension) : ℝ) ^ 2 * coeffDerivConst ξ 0 * coeffDerivConst ξ 1 *
              coeffDerivConst ξ 2 * coeffDerivConst ξ 3) *
          coeffSeminormSeq ξ hξ 4 f := by
    dsimp [c0, c2]
    ring
  calc
    ‖(Δ (Δ f)).toLp 2 (volume : Measure SpaceTime)‖ = coeffSeminormSeq ξ hξ 0 (Δ (Δ f)) := by
      simpa using
        (coeffSeminormSeq_zero_eq_norm_toLp (ξ := ξ) (hξ := hξ) (f := Δ (Δ f))).symm
    _ ≤ c0 * (c2 * coeffSeminormSeq ξ hξ 4 f) := hcoeff
    _ = _ := hscal

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

private lemma neg_two_mul_pi_sq_ne_zero : (-((2 * Real.pi) ^ 2 : ℝ)) ≠ 0 := by
  have hpos : 0 < ((2 * Real.pi) ^ 2 : ℝ) := by
    have : (0 : ℝ) < 2 * Real.pi := by positivity
    exact sq_pos_of_pos this
  exact neg_ne_zero.mpr (ne_of_gt hpos)

private lemma norm_inv_neg_two_mul_pi_sq :
    ‖(-((2 * Real.pi) ^ 2 : ℝ))⁻¹‖ = (1 : ℝ) / (2 * Real.pi) ^ 2 := by
  have hnonneg : 0 ≤ ((2 * Real.pi) ^ 2 : ℝ) := by positivity
  calc
    ‖(-((2 * Real.pi) ^ 2 : ℝ))⁻¹‖ = ‖(-((2 * Real.pi) ^ 2 : ℝ))‖⁻¹ := by
      simp
    _ = ‖((2 * Real.pi) ^ 2 : ℝ)‖⁻¹ := by simp
    _ = ((2 * Real.pi) ^ 2 : ℝ)⁻¹ := by simp [Real.norm_of_nonneg hnonneg]
    _ = (1 : ℝ) / (2 * Real.pi) ^ 2 := by simp [one_div]

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
  have hg : quadWeight.HasTemperateGrowth := quadWeight_hasTemperateGrowth
  have hcomp :=
    (SchwartzMap.fourierMultiplierCLM_fourierMultiplierCLM_apply (F := (ℂ))
      (g₁ := quadWeight) (g₂ := quadWeight) hg hg g)
  have hcomp' :
      SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) (fun ξ : SpaceTime ↦ quadWeight ξ * quadWeight ξ) g =
        SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) quadWeight
          (SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) quadWeight g) := by
    simpa [Pi.mul_def] using hcomp.symm
  have hq := fourierMultiplierCLM_quadWeight_eq (g := g)
  have hqΔ := fourierMultiplierCLM_quadWeight_eq (g := Δ g)
  calc
    SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) (fun ξ : SpaceTime ↦ quadWeight ξ * quadWeight ξ) g
        =
        SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) quadWeight
          (SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) quadWeight g) := hcomp'
    _ =
        SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) quadWeight ((-((2 * Real.pi) ^ 2 : ℝ))⁻¹ • Δ g) := by
          rw [hq]
    _ = (-((2 * Real.pi) ^ 2 : ℝ))⁻¹ •
          SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) quadWeight (Δ g) := by
          simp
    _ = (-((2 * Real.pi) ^ 2 : ℝ))⁻¹ • ((-((2 * Real.pi) ^ 2 : ℝ))⁻¹ • Δ (Δ g)) := by
          rw [hqΔ]

private lemma fourierMultiplierCLM_sobolevWeight_decomp (g : TestFunctionℂ) :
    SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) sobolevWeight g =
      g
        + (2 : ℝ) • SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) quadWeight g
        + SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) (fun ξ : SpaceTime ↦ quadWeight ξ * quadWeight ξ) g := by
  have h1 :
      SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) sobolevWeight g =
        SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) (fun _ : SpaceTime ↦ (1 : ℝ)) g
          + SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) (fun ξ : SpaceTime ↦ (2 : ℝ) * quadWeight ξ) g
          + SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) (fun ξ : SpaceTime ↦ quadWeight ξ * quadWeight ξ) g := by
    have hsum :
        (fun ξ : SpaceTime ↦ (1 : ℝ) + (2 : ℝ) * quadWeight ξ + quadWeight ξ * quadWeight ξ)
          =
          (fun ξ : SpaceTime ↦ (1 : ℝ) + (2 : ℝ) * quadWeight ξ) +
            (fun ξ : SpaceTime ↦ quadWeight ξ * quadWeight ξ) := by
      funext ξ; simp [add_assoc]
    have hadd1 :=
      SchwartzMap.fourierMultiplierCLM_add (F := (ℂ))
        (g₁ := fun ξ : SpaceTime ↦ (1 : ℝ) + (2 : ℝ) * quadWeight ξ)
        (g₂ := fun ξ : SpaceTime ↦ quadWeight ξ * quadWeight ξ)
        (by
          -- `fun_prop` doesn't unfold `quadWeight`, so we do it explicitly.
          simpa [quadWeight] using (by
            fun_prop : (fun ξ : SpaceTime ↦ (1 : ℝ) + (2 : ℝ) * ‖ξ‖ ^ 2).HasTemperateGrowth))
        quadWeight_sq_hasTemperateGrowth
    have hadd2 :=
      SchwartzMap.fourierMultiplierCLM_add (F := (ℂ))
        (g₁ := fun _ : SpaceTime ↦ (1 : ℝ))
        (g₂ := fun ξ : SpaceTime ↦ (2 : ℝ) * quadWeight ξ)
        (by fun_prop)
        (by
          simpa [quadWeight] using (by
            fun_prop : (fun ξ : SpaceTime ↦ (2 : ℝ) * ‖ξ‖ ^ 2).HasTemperateGrowth))
    have hA :
        SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) (fun ξ : SpaceTime ↦ (1 : ℝ) + (2 : ℝ) * quadWeight ξ) g
          =
          SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) (fun _ : SpaceTime ↦ (1 : ℝ)) g
            + SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) (fun ξ : SpaceTime ↦ (2 : ℝ) * quadWeight ξ) g := by
      simpa using congrArg (fun T => T g) hadd2
    have hB :
        SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ)
              (fun ξ : SpaceTime ↦ (1 : ℝ) + (2 : ℝ) * quadWeight ξ) g
            + SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ)
                (fun ξ : SpaceTime ↦ quadWeight ξ * quadWeight ξ) g
          =
          SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) sobolevWeight g := by
      have this := congrArg (fun T => T g) hadd1
      have hsym :
          (fun ξ : SpaceTime ↦ (1 : ℝ) + (2 : ℝ) * quadWeight ξ) +
              (fun ξ : SpaceTime ↦ quadWeight ξ * quadWeight ξ) =
            sobolevWeight := by
        funext ξ
        simp [sobolevWeight, quadWeight, pow_two]
        ring
      simpa [hsym] using this.symm
    rw [← hB]
    simp [hA, add_assoc]
  have hconst :
      SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) (fun _ : SpaceTime ↦ (1 : ℝ)) g = g := by
    simp
  have hsmul :
      SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) (fun ξ : SpaceTime ↦ (2 : ℝ) * quadWeight ξ) g =
        (2 : ℝ) • SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) quadWeight g := by
    simpa [smul_eq_mul] using
      (SchwartzMap.fourierMultiplierCLM_smul_apply (F := (ℂ)) (hg := quadWeight_hasTemperateGrowth)
        (c := (2 : ℝ)) (f := g))
  simpa [hconst, hsmul, add_assoc] using h1

private lemma norm_toLp_two_smul_fourierMultiplierCLM_quadWeight_eq (g : TestFunctionℂ) :
    ‖((2 : ℝ) • SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) quadWeight g).toLp 2
          (volume : Measure SpaceTime)‖
      = ((2 : ℝ) / ((2 * Real.pi) ^ 2)) * ‖(Δ g).toLp 2 (volume : Measure SpaceTime)‖ := by
  have hq := fourierMultiplierCLM_quadWeight_eq (g := g)
  calc
    ‖((2 : ℝ) • SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) quadWeight g).toLp 2
          (volume : Measure SpaceTime)‖
        = ‖((2 : ℝ) • ((-((2 * Real.pi) ^ 2 : ℝ))⁻¹ • Δ g)).toLp 2
              (volume : Measure SpaceTime)‖ := by
            exact
              congrArg
                (fun t : TestFunctionℂ =>
                  ‖((2 : ℝ) • t).toLp 2 (volume : Measure SpaceTime)‖) hq
    _ = ‖((2 : ℝ) * (-((2 * Real.pi) ^ 2 : ℝ))⁻¹) • (Δ g).toLp 2 (volume : Measure SpaceTime)‖ := by
          have htoLp :
              ((2 : ℝ) • ((-((2 * Real.pi) ^ 2 : ℝ))⁻¹ • Δ g)).toLp 2
                  (volume : Measure SpaceTime)
                =
              ((2 : ℝ) * (-((2 * Real.pi) ^ 2 : ℝ))⁻¹) • (Δ g).toLp 2
                  (volume : Measure SpaceTime) := by
            change (2 : ℝ) • (((-((2 * Real.pi) ^ 2 : ℝ))⁻¹ • Δ g).toLp 2
              (volume : Measure SpaceTime)) = _
            change (2 : ℝ) • ((-((2 * Real.pi) ^ 2 : ℝ))⁻¹ • (Δ g).toLp 2
              (volume : Measure SpaceTime)) = _
            simp only [smul_smul, mul_assoc]
          exact congrArg (fun z => ‖z‖) htoLp
    _ = ‖(2 : ℝ) * (-((2 * Real.pi) ^ 2 : ℝ))⁻¹‖ * ‖(Δ g).toLp 2 (volume : Measure SpaceTime)‖ := by
          exact norm_smul ((2 : ℝ) * (-((2 * Real.pi) ^ 2 : ℝ))⁻¹)
            ((Δ g).toLp 2 (volume : Measure SpaceTime))
    _ = ((2 : ℝ) / ((2 * Real.pi) ^ 2)) * ‖(Δ g).toLp 2 (volume : Measure SpaceTime)‖ := by
          have hscal :
              ‖(2 : ℝ) * (-((2 * Real.pi) ^ 2 : ℝ))⁻¹‖ = (2 : ℝ) / (2 * Real.pi) ^ 2 := by
            calc
              ‖(2 : ℝ) * (-((2 * Real.pi) ^ 2 : ℝ))⁻¹‖
                  = ‖(2 : ℝ)‖ * ‖(-((2 * Real.pi) ^ 2 : ℝ))⁻¹‖ := by
                      simpa using (norm_mul (2 : ℝ) (-((2 * Real.pi) ^ 2 : ℝ))⁻¹)
              _ = (2 : ℝ) * ((1 : ℝ) / (2 * Real.pi) ^ 2) := by
                    rw [Real.norm_of_nonneg (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
                    rw [norm_inv_neg_two_mul_pi_sq]
              _ = (2 : ℝ) / (2 * Real.pi) ^ 2 := by
                    simp [div_eq_mul_inv]
          rw [hscal]
  aesop

private lemma norm_toLp_fourierMultiplierCLM_quadWeight_sq_eq (g : TestFunctionℂ) :
    ‖(SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ)
          (fun ξ : SpaceTime ↦ quadWeight ξ * quadWeight ξ) g).toLp 2
        (volume : Measure SpaceTime)‖
      = (1 / ((2 * Real.pi) ^ 4)) * ‖(Δ (Δ g)).toLp 2 (volume : Measure SpaceTime)‖ := by
  have toLp_smul (c : ℝ) (f : TestFunctionℂ) :
      (c • f).toLp 2 (volume : Measure SpaceTime) = c • f.toLp 2 (volume : Measure SpaceTime) := by
    rfl
  have hq2 := fourierMultiplierCLM_quadWeight_sq_eq (g := g)
  calc
    ‖(SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ)
            (fun ξ : SpaceTime ↦ quadWeight ξ * quadWeight ξ) g).toLp 2
          (volume : Measure SpaceTime)‖
        = ‖((-((2 * Real.pi) ^ 2 : ℝ))⁻¹ • ((-((2 * Real.pi) ^ 2 : ℝ))⁻¹ • Δ (Δ g))).toLp 2
              (volume : Measure SpaceTime)‖ := by
              exact
                congrArg
                  (fun t : TestFunctionℂ =>
                    ‖t.toLp 2 (volume : Measure SpaceTime)‖) hq2
    _ = ‖((-((2 * Real.pi) ^ 2 : ℝ))⁻¹ * (-((2 * Real.pi) ^ 2 : ℝ))⁻¹) •
            (Δ (Δ g)).toLp 2 (volume : Measure SpaceTime)‖ := by
          simp only [toLp_smul, smul_smul, mul_assoc]
    _ = ‖(-((2 * Real.pi) ^ 2 : ℝ))⁻¹ * (-((2 * Real.pi) ^ 2 : ℝ))⁻¹‖ *
          ‖(Δ (Δ g)).toLp 2 (volume : Measure SpaceTime)‖ := by
          exact norm_smul
            ((-((2 * Real.pi) ^ 2 : ℝ))⁻¹ * (-((2 * Real.pi) ^ 2 : ℝ))⁻¹)
            ((Δ (Δ g)).toLp 2 (volume : Measure SpaceTime))
    _ = (1 / ((2 * Real.pi) ^ 4)) * ‖(Δ (Δ g)).toLp 2 (volume : Measure SpaceTime)‖ := by
          have hscal :
              ‖(-((2 * Real.pi) ^ 2 : ℝ))⁻¹ * (-((2 * Real.pi) ^ 2 : ℝ))⁻¹‖ =
                (1 : ℝ) / (2 * Real.pi) ^ 4 := by
            calc
              ‖(-((2 * Real.pi) ^ 2 : ℝ))⁻¹ * (-((2 * Real.pi) ^ 2 : ℝ))⁻¹‖
                  =
                  ‖(-((2 * Real.pi) ^ 2 : ℝ))⁻¹‖ * ‖(-((2 * Real.pi) ^ 2 : ℝ))⁻¹‖ := by
                    exact norm_mul (-((2 * Real.pi) ^ 2 : ℝ))⁻¹ (-((2 * Real.pi) ^ 2 : ℝ))⁻¹
              _ = ((1 : ℝ) / (2 * Real.pi) ^ 2) * ((1 : ℝ) / (2 * Real.pi) ^ 2) := by
                    rw [norm_inv_neg_two_mul_pi_sq, ← norm_inv_neg_two_mul_pi_sq]
              _ = (1 : ℝ) / (2 * Real.pi) ^ 4 := by
                    have h0 : (2 * Real.pi : ℝ) ≠ 0 := by
                      have h2 : (2 : ℝ) ≠ 0 := by norm_num
                      exact mul_ne_zero h2 Real.pi_ne_zero
                    field_simp [h0]
          rw [hscal]
  aesop

set_option maxHeartbeats 800000 in
private lemma norm_toLp_fourierMultiplierCLM_sobolevWeight_le (g : TestFunctionℂ) :
    ‖(SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) sobolevWeight g).toLp 2
        (volume : Measure SpaceTime)‖ ≤
      (1 : ℝ) * ‖g.toLp 2 (volume : Measure SpaceTime)‖
        + ((2 : ℝ) / ((2 * Real.pi) ^ 2)) * ‖(Δ g).toLp 2 (volume : Measure SpaceTime)‖
        + (1 / ((2 * Real.pi) ^ 4)) * ‖(Δ (Δ g)).toLp 2 (volume : Measure SpaceTime)‖ := by
  -- Refactored proof: decompose the multiplier into `1 + 2‖·‖² + ‖·‖⁴`
  -- and convert the polynomial symbols into Laplacian iterates.
  set h : TestFunctionℂ :=
    SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) sobolevWeight g with hh
  have hdecomp :
      h =
        g
          + (2 : ℝ) • SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) quadWeight g
          + SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ)
              (fun ξ : SpaceTime ↦ quadWeight ξ * quadWeight ξ) g := by
    simpa [hh] using (fourierMultiplierCLM_sobolevWeight_decomp (g := g))
  let T :
      TestFunctionℂ →L[ℝ] ↥(Lp ℂ 2 (volume : Measure SpaceTime)) :=
    SchwartzMap.toLpCLM (𝕜 := ℝ) (F := ℂ) (E := SpaceTime)
      (p := (2 : ℝ≥0∞)) (μ := (volume : Measure SpaceTime))
  have htoLp :
      h.toLp 2 (volume : Measure SpaceTime) =
        g.toLp 2 (volume : Measure SpaceTime)
          + ((2 : ℝ) • SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) quadWeight g).toLp 2
              (volume : Measure SpaceTime)
          + (SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ)
                (fun ξ : SpaceTime ↦ quadWeight ξ * quadWeight ξ) g).toLp 2
              (volume : Measure SpaceTime) := by
    have hEq := congrArg (fun u : TestFunctionℂ => T u) hdecomp
    have :
        T h =
          T g
            + T ((2 : ℝ) • SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) quadWeight g)
            + T (SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ)
                  (fun ξ : SpaceTime ↦ quadWeight ξ * quadWeight ξ) g) := by
      calc
        T h = T (g + (2 : ℝ) • SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) quadWeight g +
              SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ)
                (fun ξ : SpaceTime ↦ quadWeight ξ * quadWeight ξ) g) := hEq
        _ = T (g + (2 : ℝ) • SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) quadWeight g)
              + T (SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ)
                    (fun ξ : SpaceTime ↦ quadWeight ξ * quadWeight ξ) g) := by
              simpa [add_assoc] using
                (T.map_add (g + (2 : ℝ) • SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) quadWeight g)
                  (SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ)
                    (fun ξ : SpaceTime ↦ quadWeight ξ * quadWeight ξ) g))
        _ = (T g + T ((2 : ℝ) • SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) quadWeight g))
              + T (SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ)
                    (fun ξ : SpaceTime ↦ quadWeight ξ * quadWeight ξ) g) := by
              simpa using congrArg (fun z => z + T (SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ)
                (fun ξ : SpaceTime ↦ quadWeight ξ * quadWeight ξ) g))
                (T.map_add g ((2 : ℝ) • SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) quadWeight g))
        _ = _ := by simp [add_assoc]
    simpa [T, SchwartzMap.toLpCLM_apply] using this

  have htri :
      ‖h.toLp 2 (volume : Measure SpaceTime)‖ ≤
        ‖g.toLp 2 (volume : Measure SpaceTime)‖
          + ‖((2 : ℝ) • SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) quadWeight g).toLp 2
              (volume : Measure SpaceTime)‖
          + ‖(SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ)
                (fun ξ : SpaceTime ↦ quadWeight ξ * quadWeight ξ) g).toLp 2
              (volume : Measure SpaceTime)‖ := by
    have habc :
        ‖(g.toLp 2 (volume : Measure SpaceTime)
            + ((2 : ℝ) • SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) quadWeight g).toLp 2
                (volume : Measure SpaceTime))
          + (SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ)
                (fun ξ : SpaceTime ↦ quadWeight ξ * quadWeight ξ) g).toLp 2
              (volume : Measure SpaceTime)‖
          ≤
          ‖g.toLp 2 (volume : Measure SpaceTime)
              + ((2 : ℝ) • SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) quadWeight g).toLp 2
                  (volume : Measure SpaceTime)‖
            + ‖(SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ)
                  (fun ξ : SpaceTime ↦ quadWeight ξ * quadWeight ξ) g).toLp 2
                (volume : Measure SpaceTime)‖ :=
      norm_add_le _ _
    have hab :
        ‖g.toLp 2 (volume : Measure SpaceTime)
            + ((2 : ℝ) • SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) quadWeight g).toLp 2
                (volume : Measure SpaceTime)‖
          ≤
          ‖g.toLp 2 (volume : Measure SpaceTime)‖
            + ‖((2 : ℝ) • SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) quadWeight g).toLp 2
                (volume : Measure SpaceTime)‖ :=
      norm_add_le _ _
    have hsum :
        ‖(g.toLp 2 (volume : Measure SpaceTime)
            + ((2 : ℝ) • SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) quadWeight g).toLp 2
                (volume : Measure SpaceTime))
          + (SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ)
                (fun ξ : SpaceTime ↦ quadWeight ξ * quadWeight ξ) g).toLp 2
              (volume : Measure SpaceTime)‖
          ≤
          ‖g.toLp 2 (volume : Measure SpaceTime)‖
            + ‖((2 : ℝ) • SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) quadWeight g).toLp 2
                (volume : Measure SpaceTime)‖
            + ‖(SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ)
                  (fun ξ : SpaceTime ↦ quadWeight ξ * quadWeight ξ) g).toLp 2
                (volume : Measure SpaceTime)‖ := by
      refine le_trans habc ?_
      have :
          ‖g.toLp 2 (volume : Measure SpaceTime)
                + ((2 : ℝ) • SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) quadWeight g).toLp 2
                    (volume : Measure SpaceTime)‖
              + ‖(SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ)
                    (fun ξ : SpaceTime ↦ quadWeight ξ * quadWeight ξ) g).toLp 2
                  (volume : Measure SpaceTime)‖
            ≤
            (‖g.toLp 2 (volume : Measure SpaceTime)‖
                + ‖((2 : ℝ) • SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) quadWeight g).toLp 2
                    (volume : Measure SpaceTime)‖)
              + ‖(SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ)
                    (fun ξ : SpaceTime ↦ quadWeight ξ * quadWeight ξ) g).toLp 2
                  (volume : Measure SpaceTime)‖ := by
        -- add the third term to `hab`
        simpa [add_assoc] using
          (add_le_add hab le_rfl)
      simpa [add_assoc] using this
    simpa [htoLp, add_assoc] using hsum

  have hterm2 := norm_toLp_two_smul_fourierMultiplierCLM_quadWeight_eq (g := g)
  have hterm3 := norm_toLp_fourierMultiplierCLM_quadWeight_sq_eq (g := g)

  have htri' := htri
  rw [hterm2, hterm3] at htri'
  -- close the goal by rewriting `h` back into the original LHS
  simpa [hh, h, one_mul, add_assoc] using htri'

set_option maxHeartbeats 800000 in
private lemma norm_toLp_sobolevWeight_smul_fourier_ofReal_le_coeffSeminormSeq
    (ξ : ℝ) (hξ : ξ ≠ 0) (f : TestFunction) :
    ‖(SchwartzMap.smulLeftCLM (F := ℂ) (fun ξ : SpaceTime ↦ (sobolevWeight ξ : ℂ))
          (𝓕 (OSforGFF.ofRealSchwartz f))).toLp 2 (volume : Measure SpaceTime)‖ ≤
      sobolevConst ξ * coeffSeminormSeq ξ hξ 4 f := by
  -- constants used in the `Δ`-graph norm bound
  let d : ℕ → ℝ := coeffDerivConst ξ
  let CΔ : ℝ := (Fintype.card (Fin STDimension) : ℝ) * (d 0) * (d 1)
  let CΔΔ : ℝ := (Fintype.card (Fin STDimension) : ℝ) ^ 2 * (d 0) * (d 1) * (d 2) * (d 3)
  let Csob : ℝ := sobolevConst ξ

  -- abbreviations
  let g : TestFunctionℂ := OSforGFF.ofRealSchwartz f
  let hW : TestFunctionℂ :=
    SchwartzMap.smulLeftCLM (F := ℂ) (fun ξ : SpaceTime ↦ (sobolevWeight ξ : ℂ)) (𝓕 g)

  -- Reduce to the physical-space Fourier multiplier via Plancherel.
  let w : SpaceTime → ℝ := sobolevWeight
  let h : TestFunctionℂ := SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) (F := ℂ) w g
  have hFourier : 𝓕 h = hW := by
    have hfour :
        𝓕 h = (SchwartzMap.smulLeftCLM (F := ℂ) w) (𝓕 g) := by
      dsimp [h]
      exact (SchwartzMap.fourier_fourierMultiplierCLM (𝕜 := ℝ) (F := (ℂ)) (g := w) (f := g))
    have hw' :
        (SchwartzMap.smulLeftCLM (F := ℂ) w) (𝓕 g) = hW := by
      have hwg : Function.HasTemperateGrowth w := by
        dsimp [w]
        simpa [sobolevWeight] using
          (by
            fun_prop : Function.HasTemperateGrowth (fun ξ : SpaceTime ↦ (1 + ‖ξ‖ ^ 2) ^ 2))
      simpa [hW, w, sobolevWeight] using
        (SchwartzMap.smulLeftCLM_ofReal (𝕜' := ℂ) (F := (ℂ)) (g := w) (hg := hwg)
          (f := (𝓕 g))).symm
    exact hfour.trans hw'
  have hPlanch :
      ‖hW.toLp 2 (volume : Measure SpaceTime)‖ = ‖h.toLp 2 (volume : Measure SpaceTime)‖ := by
    have := (SchwartzMap.norm_fourier_toL2_eq (f := h))
    simpa [hFourier] using this
  -- It suffices to bound the `L²` norm of `h`.
  rw [hPlanch]

  have hL2_le_coeff4 :
      ‖f.toLp 2 (volume : Measure SpaceTime)‖ ≤ coeffSeminormSeq ξ hξ 4 f :=
    norm_toLp_le_coeffSeminormSeq (ξ := ξ) (hξ := hξ) (k := 4) (f := f)
  have hL2Δ_le :
      ‖(Δ f).toLp 2 (volume : Measure SpaceTime)‖ ≤ CΔ * coeffSeminormSeq ξ hξ 4 f := by
    simpa [CΔ, d] using
      (norm_toLp_laplacian_le_coeffSeminormSeq_four (ξ := ξ) (hξ := hξ) (f := f))
  have hL2ΔΔ_le :
      ‖(Δ (Δ f)).toLp 2 (volume : Measure SpaceTime)‖ ≤ CΔΔ * coeffSeminormSeq ξ hξ 4 f := by
    simpa [CΔΔ, d] using
      (norm_toLp_laplacian_laplacian_le_coeffSeminormSeq_four (ξ := ξ) (hξ := hξ) (f := f))

  have hbound_h :
      ‖h.toLp 2 (volume : Measure SpaceTime)‖ ≤
        (1 : ℝ) * ‖g.toLp 2 (volume : Measure SpaceTime)‖
          + ((2 : ℝ) / ((2 * Real.pi) ^ 2)) * ‖(Δ g).toLp 2 (volume : Measure SpaceTime)‖
          + (1 / ((2 * Real.pi) ^ 4)) * ‖(Δ (Δ g)).toLp 2 (volume : Measure SpaceTime)‖ := by
    have h' := (norm_toLp_fourierMultiplierCLM_sobolevWeight_le (g := g))
    simpa [h, w] using h'

  have hgL2 : ‖g.toLp 2 (volume : Measure SpaceTime)‖ ≤ coeffSeminormSeq ξ hξ 4 f := by
    simpa [g] using (le_trans (by
      simpa [g] using (norm_toLp_ofRealSchwartz_eq (f := f)).le) hL2_le_coeff4)
  have hΔg :
      ‖(Δ g).toLp 2 (volume : Measure SpaceTime)‖ ≤ CΔ * coeffSeminormSeq ξ hξ 4 f := by
    have : Δ g = OSforGFF.ofRealSchwartz (Δ f) := by
      simpa [g] using (laplacian_ofReal_eq (f := f))
    have hnorm :
        ‖(Δ g).toLp 2 (volume : Measure SpaceTime)‖ = ‖(Δ f).toLp 2 (volume : Measure SpaceTime)‖ := by
      simpa [this] using (norm_toLp_ofRealSchwartz_eq (f := Δ f))
    simpa [hnorm] using hL2Δ_le
  have hΔΔg :
      ‖(Δ (Δ g)).toLp 2 (volume : Measure SpaceTime)‖ ≤ CΔΔ * coeffSeminormSeq ξ hξ 4 f := by
    have hΔg' : Δ g = OSforGFF.ofRealSchwartz (Δ f) := by
      simpa [g] using (laplacian_ofReal_eq (f := f))
    have : Δ (Δ g) = OSforGFF.ofRealSchwartz (Δ (Δ f)) := by
      simpa [hΔg'] using (laplacian_ofReal_eq (f := Δ f))
    have hnorm :
        ‖(Δ (Δ g)).toLp 2 (volume : Measure SpaceTime)‖ =
          ‖(Δ (Δ f)).toLp 2 (volume : Measure SpaceTime)‖ := by
      simpa [this] using (norm_toLp_ofRealSchwartz_eq (f := Δ (Δ f)))
    simpa [hnorm] using hL2ΔΔ_le

  have : ‖h.toLp 2 (volume : Measure SpaceTime)‖ ≤ Csob * coeffSeminormSeq ξ hξ 4 f := by
    have hA :
        (1 : ℝ) * ‖g.toLp 2 (volume : Measure SpaceTime)‖ ≤
          (1 : ℝ) * coeffSeminormSeq ξ hξ 4 f := by
      simpa [one_mul] using hgL2
    have hB :
        ((2 : ℝ) / ((2 * Real.pi) ^ 2)) * ‖(Δ g).toLp 2 (volume : Measure SpaceTime)‖ ≤
          ((2 : ℝ) / ((2 * Real.pi) ^ 2)) * (CΔ * coeffSeminormSeq ξ hξ 4 f) := by
      exact mul_le_mul_of_nonneg_left hΔg (by positivity)
    have hC :
        ((2 * Real.pi) ^ 4)⁻¹ * ‖(Δ (Δ g)).toLp 2 (volume : Measure SpaceTime)‖ ≤
          ((2 * Real.pi) ^ 4)⁻¹ * (CΔΔ * coeffSeminormSeq ξ hξ 4 f) := by
      exact mul_le_mul_of_nonneg_left hΔΔg (by positivity)
    have hsum :
        (1 : ℝ) * ‖g.toLp 2 (volume : Measure SpaceTime)‖
            + ((2 : ℝ) / ((2 * Real.pi) ^ 2)) * ‖(Δ g).toLp 2 (volume : Measure SpaceTime)‖
            + ((2 * Real.pi) ^ 4)⁻¹ * ‖(Δ (Δ g)).toLp 2 (volume : Measure SpaceTime)‖
          ≤
          (1 : ℝ) * coeffSeminormSeq ξ hξ 4 f
            + ((2 : ℝ) / ((2 * Real.pi) ^ 2)) * (CΔ * coeffSeminormSeq ξ hξ 4 f)
            + ((2 * Real.pi) ^ 4)⁻¹ * (CΔΔ * coeffSeminormSeq ξ hξ 4 f) :=
      add_le_add (add_le_add hA hB) hC
    have h2 :
        ‖h.toLp 2 (volume : Measure SpaceTime)‖ ≤
          (1 : ℝ) * coeffSeminormSeq ξ hξ 4 f
            + ((2 : ℝ) / ((2 * Real.pi) ^ 2)) * (CΔ * coeffSeminormSeq ξ hξ 4 f)
            + ((2 * Real.pi) ^ 4)⁻¹ * (CΔΔ * coeffSeminormSeq ξ hξ 4 f) :=
      le_trans (by simpa [one_div] using hbound_h) hsum
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
    have h2' :
        ‖h.toLp 2 (volume : Measure SpaceTime)‖ ≤
          c
            + ((2 : ℝ) / ((2 * Real.pi) ^ 2)) * (CΔ * c)
            + ((2 * Real.pi) ^ 4)⁻¹ * (CΔΔ * c) := by
      simpa [c, mul_assoc] using h2
    have : ‖h.toLp 2 (volume : Measure SpaceTime)‖ ≤
        ((1 : ℝ)
            + ((2 : ℝ) / ((2 * Real.pi) ^ 2)) * CΔ
            + ((2 * Real.pi) ^ 4)⁻¹ * CΔΔ) * c := by
      simpa [hEq] using h2'
    -- match the definition of `Csob = sobolevConst ξ`
    dsimp [Csob, sobolevConst] at this
    simpa [c] using this
  simpa [Csob] using this


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

  -- Sobolev constant for the Fourier-weight `((1 + ‖·‖^2)^2)`.
  let Csob : ℝ := sobolevConst ξ
  have hCsob0 : 0 ≤ Csob := by
    simpa [Csob] using sobolevConst_nonneg ξ

  refine ⟨⟨Csob * A, mul_nonneg hCsob0 hA0⟩, ?_⟩
  intro f
  -- Reduce to a pointwise bound.
  have hbound :
      ∀ x : SpaceTime, ‖x‖ ^ (0 : ℕ) * ‖iteratedFDeriv ℝ (0 : ℕ) f x‖ ≤
        (A * Csob) * coeffSeminormSeq ξ hξ 4 f := by
    -- Work with the complexification `g` and the weighted Fourier transform `hW`.
    let g : TestFunctionℂ := OSforGFF.ofRealSchwartz f
    let hW : TestFunctionℂ :=
      SchwartzMap.smulLeftCLM (F := ℂ) (fun ξ : SpaceTime ↦ (sobolevWeight ξ : ℂ)) (𝓕 g)
    have hW_le : ‖hW.toLp 2 (volume : Measure SpaceTime)‖ ≤ Csob * coeffSeminormSeq ξ hξ 4 f := by
      have h' :=
        norm_toLp_sobolevWeight_smul_fourier_ofReal_le_coeffSeminormSeq
          (ξ := ξ) (hξ := hξ) (f := f)
      simpa [g, hW, Csob] using h'

    intro x
    simp only [pow_zero, one_mul, norm_iteratedFDeriv_zero]
    have hx0 : ‖f x‖ = ‖g x‖ := by
      simp [g, OSforGFF.ofRealSchwartz_apply]
    have hx4 : ‖g x‖ ≤ A * ‖hW.toLp 2 (volume : Measure SpaceTime)‖ := by
      have hx :=
        norm_le_fourierWeightL2_mul_norm_toLp_fourierWeightInv_smul_fourier (g := g) (x := x)
      -- unfold `A` and `hW` into the packaged statement
      simpa [A, wInv, hW, fourierWeight, fourierWeightInv, sobolevWeight] using hx

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
  have hsem' : SchwartzMap.seminorm ℝ 0 0 f ≤ (Csob * A) * coeffSeminormSeq ξ hξ 4 f := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using hsem
  -- finish by rewriting the RHS as evaluation of the scaled seminorm
  simpa [Seminorm.smul_apply, NNReal.smul_def, mul_assoc, mul_comm, mul_left_comm] using hsem'

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

private lemma schwartz_seminorm00_le_mul_coeffSeminormSeq
    (ξ : ℝ) (hξ : ξ ≠ 0) (C00 : ℝ≥0)
    (hC00 : ∀ f : TestFunction,
      SchwartzMap.seminorm ℝ 0 0 f ≤ ((C00 : ℝ≥0) • coeffSeminormSeq ξ hξ 4) f)
    (f : TestFunction) :
    SchwartzMap.seminorm ℝ 0 0 f ≤ (C00 : ℝ) * coeffSeminormSeq ξ hξ 4 f := by
  simpa [Seminorm.smul_apply, NNReal.smul_def, mul_assoc] using hC00 f

set_option maxHeartbeats 800000 in
private lemma schwartz_seminorm00_mulCoordCLM_iter_iteratedLineDerivOp_unitVec_le
    (ξ : ℝ) (hξ : ξ ≠ 0) (C00 : ℝ≥0)
    (hC00 : ∀ f : TestFunction,
      SchwartzMap.seminorm ℝ 0 0 f ≤ ((C00 : ℝ≥0) • coeffSeminormSeq ξ hξ 4) f)
    (k n : ℕ) (i : Fin STDimension) (r : Fin n → Fin STDimension) (f : TestFunction) :
    SchwartzMap.seminorm ℝ 0 0
        (((mulCoordCLM i)^[k + 1]) (∂^{fun j : Fin n ↦ unitVec (r j)} f))
      ≤ (C00 : ℝ) *
          (∏ j ∈ Finset.range (k + 1),
              (‖(ξ / 2 : ℝ)‖ * Real.sqrt 2 * ((2 : ℝ) ^ (4 + j) + 1))) *
            (∏ j ∈ Finset.range n,
                (‖(1 / (2 * ξ) : ℝ)‖ * Real.sqrt 2 * ((2 : ℝ) ^ (4 + (k + 1) + j) + 1))) *
              coeffSeminormSeq ξ hξ (4 + (k + 1) + n) f := by
  have hC00' (g : TestFunction) :
      SchwartzMap.seminorm ℝ 0 0 g ≤ (C00 : ℝ) * coeffSeminormSeq ξ hξ 4 g := by
    simpa using
      schwartz_seminorm00_le_mul_coeffSeminormSeq (ξ := ξ) (hξ := hξ) (C00 := C00) (hC00 := hC00) g
  -- apply `hC00` at the transformed function
  have h00 :
      SchwartzMap.seminorm ℝ 0 0
          (((mulCoordCLM i)^[k + 1]) (∂^{fun j : Fin n ↦ unitVec (r j)} f))
        ≤ (C00 : ℝ) * coeffSeminormSeq ξ hξ 4
            (((mulCoordCLM i)^[k + 1]) (∂^{fun j : Fin n ↦ unitVec (r j)} f)) := by
    simpa using hC00' (((mulCoordCLM i)^[k + 1]) (∂^{fun j : Fin n ↦ unitVec (r j)} f))
  -- bound multiplication iterates in `coeffSeminormSeq`
  have hmul :
      coeffSeminormSeq ξ hξ 4
          (((mulCoordCLM i)^[k + 1]) (∂^{fun j : Fin n ↦ unitVec (r j)} f))
        ≤ (∏ j ∈ Finset.range (k + 1),
              (‖(ξ / 2 : ℝ)‖ * Real.sqrt 2 * ((2 : ℝ) ^ (4 + j) + 1))) *
            coeffSeminormSeq ξ hξ (4 + (k + 1)) (∂^{fun j : Fin n ↦ unitVec (r j)} f) := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (coeffSeminormSeq_mulCoordCLM_iter_le (ξ := ξ) (hξ := hξ) (i := i)
        (k₀ := 4) (k := k + 1) (f := (∂^{fun j : Fin n ↦ unitVec (r j)} f)))
  -- bound iterated derivatives in `coeffSeminormSeq`
  have hder :
      coeffSeminormSeq ξ hξ (4 + (k + 1)) (∂^{fun j : Fin n ↦ unitVec (r j)} f) ≤
        (∏ j ∈ Finset.range n,
            (‖(1 / (2 * ξ) : ℝ)‖ * Real.sqrt 2 * ((2 : ℝ) ^ (4 + (k + 1) + j) + 1))) *
          coeffSeminormSeq ξ hξ (4 + (k + 1) + n) f := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (coeffSeminormSeq_iteratedLineDerivOp_unitVec_le (ξ := ξ) (hξ := hξ)
        (r := r) (k₀ := 4 + (k + 1)) (f := f))
  -- chain all bounds
  calc
    SchwartzMap.seminorm ℝ 0 0
        (((mulCoordCLM i)^[k + 1]) (∂^{fun j : Fin n ↦ unitVec (r j)} f))
        ≤ (C00 : ℝ) * coeffSeminormSeq ξ hξ 4
              (((mulCoordCLM i)^[k + 1]) (∂^{fun j : Fin n ↦ unitVec (r j)} f)) := h00
    _ ≤ (C00 : ℝ) *
          ((∏ j ∈ Finset.range (k + 1),
                (‖(ξ / 2 : ℝ)‖ * Real.sqrt 2 * ((2 : ℝ) ^ (4 + j) + 1))) *
              coeffSeminormSeq ξ hξ (4 + (k + 1)) (∂^{fun j : Fin n ↦ unitVec (r j)} f)) := by
          exact mul_le_mul_of_nonneg_left hmul (by positivity)
    _ ≤ (C00 : ℝ) *
          ((∏ j ∈ Finset.range (k + 1),
                (‖(ξ / 2 : ℝ)‖ * Real.sqrt 2 * ((2 : ℝ) ^ (4 + j) + 1))) *
            ((∏ j ∈ Finset.range n,
                  (‖(1 / (2 * ξ) : ℝ)‖ * Real.sqrt 2 * ((2 : ℝ) ^ (4 + (k + 1) + j) + 1))) *
                coeffSeminormSeq ξ hξ (4 + (k + 1) + n) f)) := by
          have hnonneg :
              0 ≤ (C00 : ℝ) *
                (∏ j ∈ Finset.range (k + 1),
                    (‖(ξ / 2 : ℝ)‖ * Real.sqrt 2 * ((2 : ℝ) ^ (4 + j) + 1))) := by
            positivity
          have hmul' := mul_le_mul_of_nonneg_left hder hnonneg
          simpa [mul_assoc] using hmul'
    _ = (C00 : ℝ) *
          (∏ j ∈ Finset.range (k + 1),
              (‖(ξ / 2 : ℝ)‖ * Real.sqrt 2 * ((2 : ℝ) ^ (4 + j) + 1))) *
            (∏ j ∈ Finset.range n,
                (‖(1 / (2 * ξ) : ℝ)‖ * Real.sqrt 2 * ((2 : ℝ) ^ (4 + (k + 1) + j) + 1))) *
              coeffSeminormSeq ξ hξ (4 + (k + 1) + n) f := by ring

set_option maxHeartbeats 800000 in
private lemma schwartz_seminorm_zero_le_coeffSeminormSeq_of_seminorm0
    (ξ : ℝ) (hξ : ξ ≠ 0) (C00 : ℝ≥0)
    (hC00 : ∀ f : TestFunction,
      SchwartzMap.seminorm ℝ 0 0 f ≤ ((C00 : ℝ≥0) • coeffSeminormSeq ξ hξ 4) f)
    (n : ℕ) :
    ∃ C : ℝ≥0, ∀ f : TestFunction,
      SchwartzMap.seminorm ℝ 0 n f ≤ ((C : ℝ≥0) • coeffSeminormSeq ξ hξ (4 + n)) f := by
  -- dimension constant
  let d : ℝ := (Fintype.card (Fin STDimension) : ℝ)
  -- size of the `r : Fin n → Fin STDimension` index set
  let cardR : ℝ := (Fintype.card (Fin n → Fin STDimension) : ℝ)
  have hC00' (f : TestFunction) :
      SchwartzMap.seminorm ℝ 0 0 f ≤ (C00 : ℝ) * coeffSeminormSeq ξ hξ 4 f := by
    simpa using
      schwartz_seminorm00_le_mul_coeffSeminormSeq (ξ := ξ) (hξ := hξ) (C00 := C00) (hC00 := hC00) f
  let Cder : ℝ :=
    ∏ j ∈ Finset.range n,
      (‖(1 / (2 * ξ) : ℝ)‖ * Real.sqrt 2 * ((2 : ℝ) ^ (4 + j) + 1))
  let C : ℝ := (d ^ n) * cardR * (C00 : ℝ) * Cder
  refine ⟨⟨C, by
    dsimp [C]; positivity⟩, ?_⟩
  intro f
  let M : ℝ :=
    (d ^ n) *
      (∑ r : (Fin n → Fin STDimension),
        SchwartzMap.seminorm ℝ 0 0 (∂^{fun j : Fin n ↦ unitVec (r j)} f))
  have hsem : SchwartzMap.seminorm ℝ 0 n f ≤ M := by
    simpa [M, d] using (schwartz_seminorm0_le_card_pow_mul_sum_seminorm0 (n := n) (f := f))
  have hM : M ≤ C * coeffSeminormSeq ξ hξ (4 + n) f := by
    have hterm :
        ∀ r : (Fin n → Fin STDimension),
          SchwartzMap.seminorm ℝ 0 0 (∂^{fun j : Fin n ↦ unitVec (r j)} f)
            ≤ (C00 : ℝ) * Cder * coeffSeminormSeq ξ hξ (4 + n) f := by
      intro r
      have h00 :
          SchwartzMap.seminorm ℝ 0 0 (∂^{fun j : Fin n ↦ unitVec (r j)} f) ≤
            (C00 : ℝ) * coeffSeminormSeq ξ hξ 4 (∂^{fun j : Fin n ↦ unitVec (r j)} f) := by
        simpa using hC00' (∂^{fun j : Fin n ↦ unitVec (r j)} f)
      have hder :
          coeffSeminormSeq ξ hξ 4 (∂^{fun j : Fin n ↦ unitVec (r j)} f) ≤
            Cder * coeffSeminormSeq ξ hξ (4 + n) f := by
        simpa [Cder, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          (coeffSeminormSeq_iteratedLineDerivOp_unitVec_le (ξ := ξ) (hξ := hξ)
            (r := r) (k₀ := 4) (f := f))
      calc
        SchwartzMap.seminorm ℝ 0 0 (∂^{fun j : Fin n ↦ unitVec (r j)} f)
            ≤ (C00 : ℝ) * coeffSeminormSeq ξ hξ 4 (∂^{fun j : Fin n ↦ unitVec (r j)} f) := h00
        _ ≤ (C00 : ℝ) * (Cder * coeffSeminormSeq ξ hξ (4 + n) f) := by
              exact mul_le_mul_of_nonneg_left hder (by positivity)
        _ = (C00 : ℝ) * Cder * coeffSeminormSeq ξ hξ (4 + n) f := by ring
    have hsum :
        (∑ r : (Fin n → Fin STDimension),
            SchwartzMap.seminorm ℝ 0 0 (∂^{fun j : Fin n ↦ unitVec (r j)} f))
          ≤ cardR * ((C00 : ℝ) * Cder * coeffSeminormSeq ξ hξ (4 + n) f) := by
      have :
          (∑ r : (Fin n → Fin STDimension),
              SchwartzMap.seminorm ℝ 0 0 (∂^{fun j : Fin n ↦ unitVec (r j)} f))
            ≤ (Fintype.card (Fin n → Fin STDimension) : ℝ) *
                ((C00 : ℝ) * Cder * coeffSeminormSeq ξ hξ (4 + n) f) := by
        refine sum_le_card_mul_of_pointwise_le (f := fun r : (Fin n → Fin STDimension) =>
          SchwartzMap.seminorm ℝ 0 0 (∂^{fun j : Fin n ↦ unitVec (r j)} f))
          (C := (C00 : ℝ) * Cder * coeffSeminormSeq ξ hξ (4 + n) f) ?_
        intro r
        simpa [mul_assoc] using (hterm r)
      simpa [cardR] using this
    have hsum' :
        d ^ n *
            (∑ r : (Fin n → Fin STDimension),
              SchwartzMap.seminorm ℝ 0 0 (∂^{fun j : Fin n ↦ unitVec (r j)} f))
          ≤
          d ^ n * (cardR * ((C00 : ℝ) * Cder * coeffSeminormSeq ξ hξ (4 + n) f)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    simpa [M, C, mul_assoc, mul_left_comm, mul_comm] using hsum'
  have : SchwartzMap.seminorm ℝ 0 n f ≤ C * coeffSeminormSeq ξ hξ (4 + n) f :=
    le_trans hsem hM
  change SchwartzMap.seminorm ℝ 0 n f ≤ C * coeffSeminormSeq ξ hξ (4 + n) f
  exact this

set_option maxHeartbeats 800000 in
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
  have hC00' (f : TestFunction) :
      SchwartzMap.seminorm ℝ 0 0 f ≤ (C00 : ℝ) * coeffSeminormSeq ξ hξ 4 f := by
    simpa using
      schwartz_seminorm00_le_mul_coeffSeminormSeq (ξ := ξ) (hξ := hξ) (C00 := C00) (hC00 := hC00) f
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
    have hterm (i : Fin STDimension) (r : Fin n → Fin STDimension) :
        SchwartzMap.seminorm ℝ 0 0 (((mulCoordCLM i)^[k + 1]) (∂^{fun j : Fin n ↦ unitVec (r j)} f))
          ≤ (C00 : ℝ) * Cmul * Cder * coeffSeminormSeq ξ hξ (4 + (k + 1) + n) f := by
      dsimp [Cmul, Cder]
      exact
        schwartz_seminorm00_mulCoordCLM_iter_iteratedLineDerivOp_unitVec_le
          (ξ := ξ) (hξ := hξ) (C00 := C00) (hC00 := hC00) (k := k) (n := n)
          (i := i) (r := r) (f := f)
    have hsum :
        (∑ i : Fin STDimension, ∑ r : (Fin n → Fin STDimension),
            SchwartzMap.seminorm ℝ 0 0
              (((mulCoordCLM i)^[k + 1]) (∂^{fun j : Fin n ↦ unitVec (r j)} f)))
          ≤ (d * cardR) *
              ((C00 : ℝ) * Cmul * Cder * coeffSeminormSeq ξ hξ (4 + (k + 1) + n) f) := by
      -- two-step `Fintype.card` estimate: first in `r`, then in `i`
      have hsum_r :
          ∀ i : Fin STDimension,
            (∑ r : (Fin n → Fin STDimension),
                SchwartzMap.seminorm ℝ 0 0
                  (((mulCoordCLM i)^[k + 1]) (∂^{fun j : Fin n ↦ unitVec (r j)} f)))
              ≤ cardR * ((C00 : ℝ) * Cmul * Cder * coeffSeminormSeq ξ hξ (4 + (k + 1) + n) f) := by
        intro i
        have :
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
        exact this
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
      have hsum_i' := hsum_i
      rw [← mul_assoc] at hsum_i'
      dsimp [d]
      exact hsum_i'
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

set_option maxHeartbeats 800000 in
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
