/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/

import OSforGFF.Basic
import OSforGFF.PositiveTimeTestFunction_real
import OSforGFF.DiscreteSymmetry
import OSforGFF.OS_Axioms
import OSforGFF.GFFMconstruct
import OSforGFF.HadamardExp
import OSforGFF.CovarianceR
import OSforGFF.OS3_CovarianceRP
import OSforGFF.GFFIsGaussian

/-!
## Real Reflection Positivity for the Gaussian Free Field

This file proves the real-valued version of the OS3 reflection positivity
for the Gaussian free field by establishing the key matrix inequality
`gaussianFreeField_OS3_matrix_real`.

The main result is `gaussianFreeField_OS3_real` which shows
`OS3_ReflectionPositivity (gaussianFreeField_free m)` for every positive mass `m`.
-/

open MeasureTheory Complex Matrix
open scoped Real InnerProductSpace BigOperators

noncomputable section

namespace QFT

/-- Reflection positivity for a single positive-time test function in the real setting. -/
private lemma freeCovarianceFormR_reflection_nonneg
    (m : ℝ) [Fact (0 < m)] (f : PositiveTimeTestFunction) :
    0 ≤ freeCovarianceFormR m (QFT.compTimeReflectionReal f.val) f.val := by
  classical
  have hf_supp : ∀ x : SpaceTime, x 0 ≤ 0 → f.val x = 0 := fun x hx => by
    apply f.zero_on_nonpositive
    unfold getTimeComponent
    exact hx
  have h := freeCovariance_reflection_positive_real (m := m) (f := f.val) hf_supp
  simpa [freeCovarianceFormR] using h

/-- Entrywise exponential preserves PSD on real symmetric PSD matrices (finite index).
    Bridge lemma to be discharged using HadamardExp (Hadamard series) machinery. -/
private lemma entrywiseExp_posSemidef_of_posSemidef
  {n : ℕ} (R : Matrix (Fin n) (Fin n) ℝ)
  (hR : R.PosSemidef) : Matrix.PosSemidef (fun i j => Real.exp (R i j)) := by
  classical
  -- PSD for the Hadamard-series exponential
  have hS : (OSforGFF.entrywiseExp_hadamardSeries (ι := Fin n) R).PosSemidef :=
    OSforGFF.posSemidef_entrywiseExp_hadamardSeries_of_posSemidef (ι := Fin n) R hR
  -- Convert to PSD for the entrywise exponential
  have hExp : (OSforGFF.entrywiseExp (ι := Fin n) R).PosSemidef := by
    simpa [OSforGFF.entrywiseExp_eq_hadamardSeries (ι := Fin n) R] using hS
  -- Unfold the definition of entrywiseExp
  simpa [OSforGFF.entrywiseExp] using hExp

-- We recall the standard Gram-matrix positivity result from Mathlib. -/
attribute [local simp] inner_sub_right inner_sub_left


/-- Reflection matrix built from the real covariance is positive semidefinite.
    This is the real analogue of covariance reflection positivity. -/
lemma freeCovarianceFormR_reflection_matrix_posSemidef
    (m : ℝ) [Fact (0 < m)]
    {n : ℕ} (f : Fin n → PositiveTimeTestFunction) :
    Matrix.PosSemidef (fun i j : Fin n =>
      freeCovarianceFormR m (QFT.compTimeReflectionReal (f i).val) (f j).val) := by
  -- The matrix R_{ij} = C(θf_i, f_j) is symmetric by freeCovarianceFormR_reflection_cross
  -- We'll prove positive semidefiniteness directly by showing the quadratic form is nonnegative
  let M : Matrix (Fin n) (Fin n) ℝ := fun i j =>
    freeCovarianceFormR m (QFT.compTimeReflectionReal (f i).val) (f j).val

  -- First prove the matrix is Hermitian (symmetric since entries are real)
  have h_herm : M.IsHermitian := by
    ext i j
    simp only [M, conjTranspose_apply]
    -- For real entries, star is the identity, so we need to show symmetry
    simp only [star_id_of_comm]
    -- Use the symmetry from freeCovarianceFormR_reflection_cross
    exact (freeCovarianceFormR_reflection_cross (m := m) (f := (f i).val) (g := (f j).val)).symm

  -- Use the constructor for regular functions
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg h_herm

  -- Second prove the quadratic form is nonnegative for all c : Fin n → ℝ
  intro c
  -- The goal is: 0 ≤ star c ⬝ᵥ M *ᵥ c
  classical

  -- For real coefficients, star c = c
  have h_star : star c = c := by ext k; simp

  -- Convert the matrix-vector form to double sum
  have h_expand : star c ⬝ᵥ M *ᵥ c =
      ∑ i, ∑ j, c i * freeCovarianceFormR m (QFT.compTimeReflectionReal (f i).val) (f j).val * c j := by
    simp only [dotProduct, Matrix.mulVec, M]
    congr 1
    ext k
    simp only [h_star]
    rw [Finset.mul_sum]
    ring_nf

  -- Step 1: Use bilinearity to collect the sums
  have h_step1 : ∑ i, ∑ j, c i * freeCovarianceFormR m (QFT.compTimeReflectionReal (f i).val) (f j).val * c j =
      freeCovarianceFormR m (∑ i, c i • QFT.compTimeReflectionReal (f i).val) (∑ j, c j • (f j).val) := by
      -- Use induction on finite sums combined with the bilinearity axioms
      -- We'll work with the multiplication form and convert to smul at the end

      -- Apply linearity in first argument: ∑ᵢ cᵢ • θfᵢ
      have h_left : ∑ i, c i * freeCovarianceFormR m (QFT.compTimeReflectionReal (f i).val) (∑ j, c j • (f j).val) =
        freeCovarianceFormR m (∑ i, c i • QFT.compTimeReflectionReal (f i).val) (∑ j, c j • (f j).val) := by
        -- This uses freeCovarianceFormR_add_left and freeCovarianceFormR_smul_left repeatedly
        induction' (Finset.univ : Finset (Fin n)) using Finset.induction with k s hk ih
        · simp only [Finset.sum_empty]
          -- freeCovarianceFormR m 0 0 = 0 (follows from linearity)
          rw [← freeCovarianceFormR_zero_left (m := m)]
        · rw [Finset.sum_insert hk, Finset.sum_insert hk]
          -- Apply bilinearity systematically
          -- Goal: show left side equals right side
          -- Use freeCovarianceFormR_smul_left and inductive hypothesis

          -- First apply smul_left to the k-th term
          have h_smul_k :
            c k * freeCovarianceFormR m (QFT.compTimeReflectionReal (f k).val) (c k • (f k).val + ∑ x ∈ s, c x • (f x).val) =
            freeCovarianceFormR m (c k • QFT.compTimeReflectionReal (f k).val) (c k • (f k).val + ∑ x ∈ s, c x • (f x).val) := by
            exact (freeCovarianceFormR_smul_left m _ _ _).symm

          -- For the sum part, we need to extend each term's right argument and use linearity
          have h_sum_extend :
            ∑ x ∈ s, c x * freeCovarianceFormR m (QFT.compTimeReflectionReal (f x).val) (c k • (f k).val + ∑ x ∈ s, c x • (f x).val) =
            freeCovarianceFormR m (∑ i ∈ s, c i • QFT.compTimeReflectionReal (f i).val) (c k • (f k).val + ∑ x ∈ s, c x • (f x).val) := by
            exact freeCovarianceFormR_left_linear_any_right m f c s (c k • (f k).val + ∑ x ∈ s, c x • (f x).val)

          -- Now combine using freeCovarianceFormR_add_left
          calc
          c k * freeCovarianceFormR m (QFT.compTimeReflectionReal (f k).val) (c k • (f k).val + ∑ x ∈ s, c x • (f x).val) +
          ∑ x ∈ s, c x * freeCovarianceFormR m (QFT.compTimeReflectionReal (f x).val) (c k • (f k).val + ∑ x ∈ s, c x • (f x).val)
          = freeCovarianceFormR m (c k • QFT.compTimeReflectionReal (f k).val) (c k • (f k).val + ∑ x ∈ s, c x • (f x).val) +
            freeCovarianceFormR m (∑ i ∈ s, c i • QFT.compTimeReflectionReal (f i).val) (c k • (f k).val + ∑ x ∈ s, c x • (f x).val) := by
            rw [h_smul_k, h_sum_extend]
          _ = freeCovarianceFormR m (c k • QFT.compTimeReflectionReal (f k).val + ∑ i ∈ s, c i • QFT.compTimeReflectionReal (f i).val) (c k • (f k).val + ∑ x ∈ s, c x • (f x).val) := by
            exact (freeCovarianceFormR_add_left m _ _ _).symm
          _ = freeCovarianceFormR m (∑ i ∈ insert k s, c i • QFT.compTimeReflectionReal (f i).val) (c k • (f k).val + ∑ x ∈ s, c x • (f x).val) := by
            simp only [Finset.sum_insert hk]      -- Then expand the right sum using linearity in second argument
      have h_right : ∀ i, ∑ j, freeCovarianceFormR m (QFT.compTimeReflectionReal (f i).val) (f j).val * c j =
        freeCovarianceFormR m (QFT.compTimeReflectionReal (f i).val) (∑ j, c j • (f j).val) := by
        intro i
        -- Use induction on the right argument with our right linearity lemmas
        induction' (Finset.univ : Finset (Fin n)) using Finset.induction with j t hj ih_right
        · simp only [Finset.sum_empty]
          -- freeCovarianceFormR m u 0 = 0 (follows from linearity)
          rw [← freeCovarianceFormR_zero_right (m := m)]
        · rw [Finset.sum_insert hj, Finset.sum_insert hj]
          -- Apply right linearity: freeCovarianceFormR_add_right and freeCovarianceFormR_smul_right
          -- First convert multiplications to scalar multiplications
          -- freeCovarianceFormR m u (f j) * c j = freeCovarianceFormR m u (c j • f j)
          have h_smul_first : freeCovarianceFormR m (QFT.compTimeReflectionReal (f i).val) (f j).val * c j =
            freeCovarianceFormR m (QFT.compTimeReflectionReal (f i).val) (c j • (f j).val) := by
            rw [mul_comm]
            rw [freeCovarianceFormR_smul_right]
          rw [h_smul_first, ih_right]
          -- Now apply freeCovarianceFormR_add_right
          rw [← freeCovarianceFormR_add_right]

      -- Combine the results by showing both sides equal the bilinear form
      -- Left side: ∑ i, ∑ j, c i * freeCovarianceFormR m (θf_i) (f_j) * c j
      -- We need: ∑ i, c i * freeCovarianceFormR m (θf_i) (∑ j, c j • f_j)
      have h_rewrite : ∑ i, ∑ j, c i * freeCovarianceFormR m (QFT.compTimeReflectionReal (f i).val) (f j).val * c j =
        ∑ i, c i * freeCovarianceFormR m (QFT.compTimeReflectionReal (f i).val) (∑ j, c j • (f j).val) := by
        congr 1
        ext i
        -- The goal after ext is to show:
        -- ∑ j, c i * freeCovarianceFormR m (θf_i) (f_j) * c j = c i * freeCovarianceFormR m (θf_i) (∑ j, c j • f_j)
        -- This follows by factoring out c i and applying h_right i
        -- Goal: ∑ j, c i * freeCovarianceFormR m (θf_i) (f_j) * c j = c i * freeCovarianceFormR m (θf_i) (∑ j, c j • f_j)

        -- We need to rewrite: ∑ j, c i * freeCovarianceFormR m (θf_i) (f_j) * c j
        -- as: c i * ∑ j, freeCovarianceFormR m (θf_i) (f_j) * c j
        -- Then apply h_right i

        -- The key insight: we can rewrite each term using mul_assoc and then factor out c i
        conv_lhs =>
          rw [show ∑ j, c i * freeCovarianceFormR m (QFT.compTimeReflectionReal (f i).val) (f j).val * c j =
                  ∑ j, c i * (freeCovarianceFormR m (QFT.compTimeReflectionReal (f i).val) (f j).val * c j) by
                simp only [mul_assoc]]

        -- Now factor out c i
        rw [← Finset.mul_sum]

        -- Apply h_right i to both sides (after factoring out c i, we need the congr_arg version)
        rw [h_right i]
      rw [h_rewrite, h_left]

  -- Step 2: Use linearity of time reflection
  have h_step2 : ∑ i, c i • QFT.compTimeReflectionReal (f i).val =
    QFT.compTimeReflectionReal (∑ i, c i • (f i).val) := by
    exact (compTimeReflectionReal_linear_combination (fun i => (f i).val) c).symm

  -- Step 3: The sum of positive-time functions is positive-time
  obtain ⟨g, hg⟩ := PositiveTimeTestFunction.sum_smul_mem f c

  -- Step 4: Combine and apply reflection positivity
  rw [h_expand, h_step1, h_step2]
  -- Now we have: freeCovarianceFormR m (compTimeReflectionReal (∑ i, c i • (f i).val)) (∑ j, c j • (f j).val)
  -- Since g.val = ∑ i, c i • (f i).val, we get: freeCovarianceFormR m (compTimeReflectionReal g.val) g.val
  rw [← hg]
  exact freeCovarianceFormR_reflection_nonneg m g

/-- Quadratic expansion identity for reflected arguments. -/
lemma freeCovarianceFormR_reflection_expansion
    (m : ℝ) [Fact (0 < m)] (f g : TestFunction) :
    freeCovarianceFormR m
        (f - QFT.compTimeReflectionReal g)
        (f - QFT.compTimeReflectionReal g)
      = freeCovarianceFormR m f f
        + freeCovarianceFormR m g g
        - 2 * freeCovarianceFormR m (QFT.compTimeReflectionReal f) g := by
  classical
  set θf := QFT.compTimeReflectionReal f
  set θg := QFT.compTimeReflectionReal g
  set Cf : ℝ := freeCovarianceFormR m f f
  set Cg : ℝ := freeCovarianceFormR m g g
  set Cfg : ℝ := freeCovarianceFormR m θf g
  have h_neg_left : ∀ u v : TestFunction,
      freeCovarianceFormR m (-u) v = -freeCovarianceFormR m u v := by
    intro u v
    simpa using
      (freeCovarianceFormR_smul_left (m := m) (c := (-1 : ℝ)) (f := u) (g := v))
  have h_neg_right : ∀ u v : TestFunction,
      freeCovarianceFormR m u (-v) = -freeCovarianceFormR m u v := by
    intro u v
    calc
      freeCovarianceFormR m u (-v)
          = freeCovarianceFormR m (-v) u := by
              exact freeCovarianceFormR_symm m u (-v)
      _ = -freeCovarianceFormR m v u := h_neg_left v u
      _ = -freeCovarianceFormR m u v := by
            simp [freeCovarianceFormR_symm]
  have h_cross : freeCovarianceFormR m θg f = Cfg := by
    simpa [θf, θg, Cfg]
      using
        (freeCovarianceFormR_reflection_cross (m := m) (f := f) (g := g)).symm
  have h_invariant : freeCovarianceFormR m θg θg = Cg := by
    simpa [θg, Cg]
      using freeCovarianceFormR_reflection_invariant (m := m) (f := g) (g := g)
  have h_term₁ :
      freeCovarianceFormR m f (f - θg) = Cf - Cfg := by
    have h_add :=
      freeCovarianceFormR_add_left (m := m)
        (f₁ := f) (f₂ := -θg) (g := f)
    have h_add' :
        freeCovarianceFormR m (f - θg) f
          = freeCovarianceFormR m f f
              + freeCovarianceFormR m (-θg) f := by
      simpa [sub_eq_add_neg, θg] using h_add
    calc
      freeCovarianceFormR m f (f - θg)
          = freeCovarianceFormR m (f - θg) f := by
              exact freeCovarianceFormR_symm m f (f - θg)
      _ = freeCovarianceFormR m f f
            + freeCovarianceFormR m (-θg) f := h_add'
      _ = Cf + (-freeCovarianceFormR m θg f) := by
            simp [θg, Cf, h_neg_left]
      _ = Cf - Cfg := by
            simp [sub_eq_add_neg, h_cross]
  have h_term₂ :
      freeCovarianceFormR m (-θg) (f - θg) = -Cfg + Cg := by
    have h_add :=
      freeCovarianceFormR_add_left (m := m)
        (f₁ := f) (f₂ := -θg) (g := -θg)
    have h_add' :
        freeCovarianceFormR m (f - θg) (-θg)
          = freeCovarianceFormR m f (-θg)
              + freeCovarianceFormR m (-θg) (-θg) := by
      simpa [sub_eq_add_neg, θg] using h_add
    have h_negneg :
        freeCovarianceFormR m (-θg) (-θg)
          = freeCovarianceFormR m θg θg := by
      have h₁ := h_neg_left θg (-θg)
      have h₂ := h_neg_right θg θg
      have h₁' : freeCovarianceFormR m (-θg) (-θg) = -freeCovarianceFormR m θg (-θg) := by
        simpa [θg] using h₁
      have h₂' : freeCovarianceFormR m θg (-θg) = -freeCovarianceFormR m θg θg := by
        simpa [θg] using h₂
      calc
        freeCovarianceFormR m (-θg) (-θg)
            = -freeCovarianceFormR m θg (-θg) := h₁'
        _ = -(-freeCovarianceFormR m θg θg) := by
              exact neg_inj.mpr h₂'
        _ = freeCovarianceFormR m θg θg := by simp
    calc
      freeCovarianceFormR m (-θg) (f - θg)
          = freeCovarianceFormR m (f - θg) (-θg) := by
              exact freeCovarianceFormR_symm m (-θg) (f - θg)
      _ = freeCovarianceFormR m f (-θg)
            + freeCovarianceFormR m (-θg) (-θg) := h_add'
      _ = -freeCovarianceFormR m f θg
            + freeCovarianceFormR m (-θg) (-θg) := by
              simp [θg, h_neg_right]
      _ = -freeCovarianceFormR m f θg
            + freeCovarianceFormR m θg θg := by
              simp [h_negneg]
      _ = -Cfg + Cg := by
          have h_sym : freeCovarianceFormR m f θg = freeCovarianceFormR m θg f := by
            simpa using freeCovarianceFormR_symm m f θg
          simp [h_sym, h_cross, h_invariant]
  have h_total :=
      freeCovarianceFormR_add_left (m := m)
        (f₁ := f) (f₂ := -θg) (g := f - θg)
  have h_total' :
      freeCovarianceFormR m (f - θg) (f - θg)
        = freeCovarianceFormR m f (f - θg)
            + freeCovarianceFormR m (-θg) (f - θg) := by
    simpa [sub_eq_add_neg, θg] using h_total
  calc
    freeCovarianceFormR m (f - θg) (f - θg)
        = freeCovarianceFormR m f (f - θg)
            + freeCovarianceFormR m (-θg) (f - θg) := h_total'
    _ = (Cf - Cfg) + (-Cfg + Cg) := by
          simp [h_term₁, h_term₂]
    _ = Cf + Cg - 2 * Cfg := by ring

/-- Evaluate the real generating functional of the free field on a real test function. -/
lemma gaussianFreeField_real_generating_re
    (m : ℝ) [Fact (0 < m)] (h : TestFunction) :
    (GJGeneratingFunctional (gaussianFreeField_free m) h).re
      = Real.exp (-(1 / 2 : ℝ) * freeCovarianceFormR m h h) := by
  classical
  set r : ℝ := -(1 / 2 : ℝ) * freeCovarianceFormR m h h
  have h_char := congrArg Complex.re (gff_real_characteristic (m := m) h)
  have h_arg :
      (-(1 / 2 : ℂ) * (freeCovarianceFormR m h h : ℝ))
        = Complex.ofReal r := by
    simp [r, Complex.ofReal_mul]
  have h_exp_rewrite :
      (Complex.exp (-(1 / 2 : ℂ) * (freeCovarianceFormR m h h : ℝ))).re
        = Real.exp r := by
    simpa [h_arg, r] using (Complex.exp_ofReal_re r)
  have h_char' := h_char
  rw [h_exp_rewrite] at h_char'
  simpa [r] using h_char'

/-- Factorisation of OS3 matrix entries in the purely real setting. -/
lemma gaussianFreeField_real_entry_factor
    (m : ℝ) [Fact (0 < m)]
    {f g : PositiveTimeTestFunction} :
    (GJGeneratingFunctional (gaussianFreeField_free m)
        (f.val - QFT.compTimeReflectionReal g.val)).re
      = (GJGeneratingFunctional (gaussianFreeField_free m) (f.val)).re
        * (GJGeneratingFunctional (gaussianFreeField_free m) (g.val)).re
        * Real.exp
            (freeCovarianceFormR m
              (QFT.compTimeReflectionReal (f.val)) (g.val)) := by
  classical
  -- shorthand for the covariance terms appearing in the exponent
  set Cf : ℝ := freeCovarianceFormR m (f.val) (f.val)
  set Cg : ℝ := freeCovarianceFormR m (g.val) (g.val)
  set Cfg : ℝ :=
    freeCovarianceFormR m (QFT.compTimeReflectionReal (f.val)) (g.val)
  -- Evaluate the generating functionals via the real characteristic formula
  have hf := gaussianFreeField_real_generating_re (m := m) (h := f.val)
  have hg := gaussianFreeField_real_generating_re (m := m) (h := g.val)
  have hfg :=
    gaussianFreeField_real_generating_re (m := m)
      (h := f.val - QFT.compTimeReflectionReal g.val)
  -- Use the reflection expansion to rewrite the covariance of f - Θg
  have h_expansion := freeCovarianceFormR_reflection_expansion (m := m)
    (f := f.val) (g := g.val)
  -- Translate the equalities coming from the generating functionals into exponentials
  have hf' :
      (GJGeneratingFunctional (gaussianFreeField_free m) (f.val)).re
        = Real.exp (-(1 / 2 : ℝ) * Cf) := by simpa [Cf] using hf
  have hg' :
      (GJGeneratingFunctional (gaussianFreeField_free m) (g.val)).re
        = Real.exp (-(1 / 2 : ℝ) * Cg) := by simpa [Cg] using hg
  have hfg' :
      (GJGeneratingFunctional (gaussianFreeField_free m)
          (f.val - QFT.compTimeReflectionReal g.val)).re
        =
        Real.exp (-(1 / 2 : ℝ)
          * freeCovarianceFormR m
              (f.val - QFT.compTimeReflectionReal g.val)
              (f.val - QFT.compTimeReflectionReal g.val)) := by
    simpa using hfg
  -- Rewrite the exponent using the quadratic expansion lemma
  have h_covariance_rewrite :
      freeCovarianceFormR m
          (f.val - QFT.compTimeReflectionReal g.val)
          (f.val - QFT.compTimeReflectionReal g.val)
        = Cf + Cg - 2 * Cfg := by
    simpa [Cf, Cg, Cfg] using h_expansion
  -- Combine all exponentials and simplify
  set a : ℝ := -(1 / 2 : ℝ) * Cf
  set b : ℝ := -(1 / 2 : ℝ) * Cg
  set A : ℝ := a + b
  have hA : A = -(1 / 2 : ℝ) * Cf + -(1 / 2 : ℝ) * Cg := by
    simp [A, a, b]
  have h_factor :
      -(1 / 2 : ℝ) * (Cf + Cg - 2 * Cfg) = A + Cfg := by
    have h_ring : -(1 / 2 : ℝ) * (Cf + Cg - 2 * Cfg)
        = -(1 / 2 : ℝ) * Cf + -(1 / 2 : ℝ) * Cg + Cfg := by
          ring
    simpa [A, a, b, add_comm, add_left_comm, add_assoc, hA] using h_ring
  calc
    (GJGeneratingFunctional (gaussianFreeField_free m)
        (f.val - QFT.compTimeReflectionReal g.val)).re
        = Real.exp (-(1 / 2 : ℝ) * (Cf + Cg - 2 * Cfg)) := by
              simpa [h_covariance_rewrite] using hfg'
  _ =
    Real.exp (-(1 / 2 : ℝ) * Cf)
    * Real.exp (-(1 / 2 : ℝ) * Cg)
    * Real.exp (Cfg) := by
        -- Exponential of sums factorises; use `Real.exp_add` twice
        calc
        Real.exp (-(1 / 2 : ℝ) * (Cf + Cg - 2 * Cfg))
          = Real.exp (A + Cfg) := by
              exact Real.exp_eq_exp.mpr h_factor
        _ = Real.exp A * Real.exp Cfg := by
              simp [Real.exp_add]
        _ =
          (Real.exp a * Real.exp b)
            * Real.exp Cfg := by
              simp [A, a, b, Real.exp_add]
    _ =
        (GJGeneratingFunctional (gaussianFreeField_free m) (f.val)).re
        * (GJGeneratingFunctional (gaussianFreeField_free m) (g.val)).re
        * Real.exp Cfg := by
        simp [hf', hg', Cfg, a, b, one_div, mul_assoc]

section GaussianRealReflectionPositivity

variable (m : ℝ) [Fact (0 < m)]

/-- Matrix formulation of the real OS3 inequality for the Gaussian free field. -/
lemma gaussianFreeField_OS3_matrix_real
    {n : ℕ} (f : Fin n → PositiveTimeTestFunction) (c : Fin n → ℝ) :
    0 ≤ (∑ i, ∑ j, c i * c j *
        (GJGeneratingFunctional (gaussianFreeField_free m)
          ((f i).val - QFT.compTimeReflectionReal (f j).val)).re) := by
  classical
  -- Build the auxiliary data appearing in the factorisation argument.
  let Z : Fin n → ℝ := fun i =>
    (GJGeneratingFunctional (gaussianFreeField_free m) (f i).val).re
  let R : Matrix (Fin n) (Fin n) ℝ := fun i j =>
    freeCovarianceFormR m
      (QFT.compTimeReflectionReal (f i).val) (f j).val
  let E : Matrix (Fin n) (Fin n) ℝ := fun i j => Real.exp (R i j)
  let y : Fin n → ℝ := fun i => c i * Z i
  -- Use the real entry factorisation and reflection positivity for the covariance.
  -- Step 1: Apply the factorisation to each matrix entry
  have h_factor : ∀ i j,
      (GJGeneratingFunctional (gaussianFreeField_free m)
        ((f i).val - QFT.compTimeReflectionReal (f j).val)).re
      = Z i * Z j * E i j := by
    intro i j
    have h_entry := gaussianFreeField_real_entry_factor (m := m) (f := f i) (g := f j)
    simp [Z, E, R] at h_entry ⊢
    exact h_entry

  -- Step 2: Rewrite the sum using the factorisation
  have h_sum₁ :
      (∑ i, ∑ j, c i * c j *
        (GJGeneratingFunctional (gaussianFreeField_free m)
          ((f i).val - QFT.compTimeReflectionReal (f j).val)).re)
      = ∑ i, ∑ j, c i * c j * (Z i * Z j * E i j) := by
    simp_rw [h_factor]

  -- Step 3: express the quadratic form using the rescaled vector y
  have h_sum₂ :
      (∑ i, ∑ j, c i * c j * (Z i * Z j * E i j))
        = ∑ i, ∑ j, y i * y j * E i j := by
    simp [y, Z, E, R, mul_comm, mul_left_comm, mul_assoc]

  -- Step 4: Apply PSD property of E
  have h_R_psd : R.PosSemidef := by
    simpa [R] using freeCovarianceFormR_reflection_matrix_posSemidef (m := m) f

  have h_E_psd : E.PosSemidef := by
    simpa [E] using entrywiseExp_posSemidef_of_posSemidef R h_R_psd

  -- Step 5: Use PSD property - the quadratic form yᵀEy is nonnegative
  have h_quad_sum :
      (∑ i, ∑ j, y i * y j * E i j)
        = y ⬝ᵥ (E.mulVec y) := by
    classical
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_comm, mul_assoc]

  have hy_nonneg : 0 ≤ y ⬝ᵥ (E.mulVec y) := h_E_psd.dotProduct_mulVec_nonneg y

  have h_goal :
      0 ≤ (∑ i, ∑ j, c i * c j *
        (GJGeneratingFunctional (gaussianFreeField_free m)
          ((f i).val - QFT.compTimeReflectionReal (f j).val)).re) := by
    have h₁ : 0 ≤ ∑ i, ∑ j, y i * y j * E i j := by
      simpa [h_quad_sum] using hy_nonneg
    have h₂ : 0 ≤ ∑ i, ∑ j, c i * c j * (Z i * Z j * E i j) := by
      simpa [h_sum₂] using h₁
    simpa [h_sum₁] using h₂

  exact h_goal

/-- Main theorem: the Gaussian free field satisfies the real reflection
  positivity axiom. -/
theorem gaussianFreeField_OS3_real :
    OS3_ReflectionPositivity (gaussianFreeField_free m) := by
  intro n f c
  simpa using gaussianFreeField_OS3_matrix_real (m := m) f c

end GaussianRealReflectionPositivity

end QFT

end
