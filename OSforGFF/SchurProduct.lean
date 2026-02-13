/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/
/-
Schur product theorem (Hadamard product preserves positive semidefiniteness).

We prove/record that if A and B are positive semidefinite Hermitian matrices, then their
entrywise (Hadamard) product D with entries D i j = A i j * B i j is also positive semidefinite.

This is used in the OS3 reflection positivity argument to deduce positivity of exp(R) from
positivity of R via power series and Schur products.
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Hadamard
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Analysis.SpecialFunctions.Exp
import OSforGFF.FrobeniusPositivity

set_option linter.unusedSectionVars false

open Complex
open scoped BigOperators

namespace OSforGFF

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Notation alias for the Hadamard (entrywise) product from Mathlib. -/
notation:100 A "∘ₕ" B => Matrix.hadamard A B

/-- Auxiliary: diagonal embedding of a vector `x : ι → ℝ` into `ι×ι` used for the restriction
argument: only the diagonal entries are nonzero and equal to `x`. -/
@[simp] def diagEmbed (x : ι → ℝ) : ι × ι → ℝ := fun p => if p.2 = p.1 then x p.1 else 0

@[simp] lemma diagEmbed_diag (x : ι → ℝ) (i : ι) : diagEmbed (ι:=ι) x (i, i) = x i := by
  simp [diagEmbed]

lemma diagEmbed_ne_zero_of_ne_zero {x : ι → ℝ} (hx : x ≠ 0) : diagEmbed (ι:=ι) x ≠ 0 := by
  classical
  -- If diagEmbed x = 0 then all diagonal entries vanish, hence x = 0, contradiction.
  intro h
  apply hx
  funext i
  have := congrArg (fun f => f (i, i)) h
  simpa [diagEmbed] using this

/-- Kronecker-like product kernel on the product index: (i,j),(k,l) ↦ A i k * B j l. -/
@[simp] def kronLike (A B : Matrix ι ι ℝ) : Matrix (ι × ι) (ι × ι) ℝ :=
  fun p q => A p.1 q.1 * B p.2 q.2

/-- Column slice of a vector indexed by ι×ι: take j and view i ↦ y (i,j). -/
@[simp] def colSlice (y : ι × ι → ℝ) (j : ι) : ι → ℝ := fun i => y (i, j)

/-- Finite sum over pairs equals iterated double sum over coordinates (binderless sums). -/
lemma sum_pairs_eq_double (g : ι × ι → ℝ) :
  (∑ p, g p) = ∑ i, ∑ j, g (i, j) :=
  Fintype.sum_prod_type g

/-- Compute (kronLike A B).mulVec y at a pair (i,j) as a double sum (binderless sums). -/
lemma kronLike_mulVec
  (A B : Matrix ι ι ℝ) (y : ι × ι → ℝ) (i j : ι) :
  ((kronLike (ι:=ι) A B).mulVec y) (i, j)
  = ∑ k, ∑ l, (A i k * B j l) * y (k, l) := by
  classical
  -- Start from definition
  have : (∑ q, (A i q.1 * B j q.2) * y q)
      = ∑ k, ∑ l, (A i k * B j l) * y (k, l) := by
    simpa using sum_pairs_eq_double (g := fun q => (A i q.1 * B j q.2) * y q)
  simpa [Matrix.mulVec, kronLike] using this

/-- Helper: swap sums and factor the `B` term in the Kronecker quadratic expansion. -/
lemma swap_sums_factor_B
  (A B : Matrix ι ι ℝ) (y : ι × ι → ℝ) :
  (∑ i, ∑ j, y (i, j) * (∑ k, ∑ l, (A i k * B j l) * y (k, l)))
  = ∑ j, ∑ l, (∑ i, y (i, j) * (∑ k, A i k * y (k, l))) * B j l := by
  classical
  -- Expand to a quadruple sum
  have h1 :
      (∑ i, ∑ j, y (i, j) * (∑ k, ∑ l, (A i k * B j l) * y (k, l)))
      = ∑ i, ∑ j, ∑ k, ∑ l, y (i, j) * ((A i k * B j l) * y (k, l)) := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    simp [Finset.mul_sum]
  -- Swap the first two sums (i and j)
  have h2 :
      (∑ i, ∑ j, ∑ k, ∑ l, y (i, j) * ((A i k * B j l) * y (k, l)))
      = ∑ j, ∑ i, ∑ k, ∑ l, y (i, j) * ((A i k * B j l) * y (k, l)) := by
    rw [Finset.sum_comm]
  -- For each fixed j, swap k and l, then bring (j,l) outside
  have h2a :
      (∑ j, ∑ i, ∑ k, ∑ l, y (i, j) * ((A i k * B j l) * y (k, l)))
      = ∑ j, ∑ i, ∑ l, ∑ k, y (i, j) * ((A i k * B j l) * y (k, l)) := by
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.sum_comm]
  have h2b :
      (∑ j, ∑ i, ∑ l, ∑ k, y (i, j) * ((A i k * B j l) * y (k, l)))
      = ∑ j, ∑ l, ∑ i, ∑ k, y (i, j) * ((A i k * B j l) * y (k, l)) := by
    apply Finset.sum_congr rfl; intro j _
    rw [Finset.sum_comm]
  -- For fixed (j,l), factor B j l and regroup the inner i,k-sums
  have h3 : ∀ j l,
      (∑ i, ∑ k, y (i, j) * ((A i k * B j l) * y (k, l)))
      = (∑ i, y (i, j) * (∑ k, A i k * y (k, l))) * B j l := by
    intro j l
    calc
      (∑ i, ∑ k, y (i, j) * ((A i k * B j l) * y (k, l)))
          = ∑ i, ∑ k, (y (i, j) * (A i k * y (k, l))) * B j l := by
            apply Finset.sum_congr rfl; intro i _
            apply Finset.sum_congr rfl; intro k _
            ring_nf
      _ = ∑ i, ((∑ k, y (i, j) * (A i k * y (k, l))) * B j l) := by
            apply Finset.sum_congr rfl; intro i _
            simp [Finset.sum_mul]
      _ = (∑ i, (∑ k, y (i, j) * (A i k * y (k, l)))) * B j l := by
            simp [Finset.sum_mul]
      _ = (∑ i, y (i, j) * (∑ k, A i k * y (k, l))) * B j l := by
            apply congrArg (fun t => t * B j l)
            apply Finset.sum_congr rfl; intro i _
            simp [Finset.mul_sum]
  -- Assemble the pieces
  have h4 :
      (∑ j, ∑ l, ∑ i, ∑ k, y (i, j) * ((A i k * B j l) * y (k, l)))
      = ∑ j, ∑ l, (∑ i, y (i, j) * (∑ k, A i k * y (k, l))) * B j l := by
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro l _
    simpa using h3 j l
  exact h1.trans (h2.trans (h2a.trans (h2b.trans h4)))

/-- Helper: identify the inner expression with `colSlice` and `A.mulVec`. -/
lemma inner_sum_colSlice_mulVec
  (A : Matrix ι ι ℝ) (y : ι × ι → ℝ) (j l : ι) :
  (∑ i, y (i, j) * (∑ k, A i k * y (k, l)))
  = (∑ i, (colSlice (ι:=ι) y j) i * (A.mulVec (colSlice (ι:=ι) y l)) i) := by
  classical
  simp [colSlice, Matrix.mulVec, dotProduct, Finset.mul_sum]

/-- Quadratic form via sums: binderless version. -/
lemma kronLike_quadratic_sum
  (A B : Matrix ι ι ℝ) (y : ι × ι → ℝ) :
  (∑ p, y p * ((kronLike (ι:=ι) A B).mulVec y) p)
  = ∑ j, ∑ l, (∑ i, (colSlice (ι:=ι) y j) i * (A.mulVec (colSlice (ι:=ι) y l)) i) * B j l := by
  classical
  -- Turn the outer sum over pairs into a double sum and expand mulVec
  have hsum_pairs :
      (∑ p, y p * ((kronLike (ι:=ι) A B).mulVec y) p)
      = ∑ i, ∑ j, y (i, j) * ((kronLike (ι:=ι) A B).mulVec y) (i, j) := by
    simpa using sum_pairs_eq_double (g := fun p => y p * ((kronLike (ι:=ι) A B).mulVec y) p)
  have hmul :
      (∑ i, ∑ j, y (i, j) * ((kronLike (ι:=ι) A B).mulVec y) (i, j))
      = ∑ i, ∑ j, y (i, j) * (∑ k, ∑ l, (A i k * B j l) * y (k, l)) := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    simp [kronLike_mulVec]
  -- Rearrange sums and factor B
  have hdist := swap_sums_factor_B (ι:=ι) A B y
  -- Identify the inner expression with colSlice and A.mulVec
  have hid : ∀ j l,
      (∑ i, y (i, j) * (∑ k, A i k * y (k, l)))
      = (∑ i, (colSlice (ι:=ι) y j) i * (A.mulVec (colSlice (ι:=ι) y l)) i) := by
    intro j l
    simpa using inner_sum_colSlice_mulVec (ι:=ι) A y j l
  -- Chain equalities
  calc
    (∑ p, y p * ((kronLike (ι:=ι) A B).mulVec y) p)
        = ∑ i, ∑ j, y (i, j) * ((kronLike (ι:=ι) A B).mulVec y) (i, j) := hsum_pairs
    _ = ∑ i, ∑ j, y (i, j) * (∑ k, ∑ l, (A i k * B j l) * y (k, l)) := hmul
    _ = ∑ j, ∑ l, (∑ i, y (i, j) * (∑ k, A i k * y (k, l))) * B j l := hdist
    _ = ∑ j, ∑ l, (∑ i, (colSlice (ι:=ι) y j) i * (A.mulVec (colSlice (ι:=ι) y l)) i) * B j l := by
      apply Finset.sum_congr rfl; intro j _
      apply Finset.sum_congr rfl; intro l _
      simp [hid]

/-- Frobenius positivity for a nonzero PSD matrix against a PD matrix.
If `G` is positive semidefinite and nonzero, and `B` is positive definite,
then the Frobenius inner product `∑ j, ∑ l, G j l * B j l` is strictly positive. -/
lemma frobenius_pos_of_psd_posdef
  (G B : Matrix ι ι ℝ) (hG_psd : G.PosSemidef) (hG_ne_zero : G ≠ 0) (hB : B.PosDef) :
  0 < ∑ j, ∑ l, G j l * B j l := by
  -- Delegate to the standalone proof to avoid duplication
  exact _root_.frobenius_pos_of_psd_posdef G B hG_psd hG_ne_zero hB

/-- Gram-type PSD: if `A` is positive definite, then the matrix
`G j l = ∑ i, (colSlice y j) i * (A * colSlice y l)_i` is positive semidefinite. -/
lemma gram_psd_from_A_posdef
  (A : Matrix ι ι ℝ) (hA : A.PosDef) (y : ι × ι → ℝ) :
  Matrix.PosSemidef (fun j l : ι => ∑ i, (colSlice (ι:=ι) y j) i * (A.mulVec (colSlice (ι:=ι) y l)) i) := by
  classical
  -- Use the characterization via dotProduct_mulVec
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · -- IsHermitian part: symmetry of the Gram matrix
    rw [Matrix.IsHermitian]
    ext j l
    -- Over ℝ, conjTranspose is transpose and star = id
    simp [Matrix.conjTranspose, star]
    -- We show: ∑ i, y (i, l) * (∑ k, A i k * y (k, j)) = ∑ i, y (i, j) * (∑ k, A i k * y (k, l))
    -- Use symmetry of A and swap the i,k-sums
    have hA_sym : ∀ i k, A i k = A k i := by
      intro i k
      -- from Hermitian entries (over ℝ: A i k = A k i)
      have := (Matrix.IsHermitian.apply hA.isHermitian i k).symm
      simpa [star] using this
    calc
      (∑ i, y (i, l) * (∑ k, A i k * y (k, j)))
          = ∑ i, ∑ k, y (i, l) * (A i k * y (k, j)) := by
            simp [Finset.mul_sum, mul_left_comm]
      _ = ∑ k, ∑ i, y (i, l) * (A i k * y (k, j)) := by
            rw [Finset.sum_comm]
      _ = ∑ k, ∑ i, y (i, l) * (A k i * y (k, j)) := by
            apply Finset.sum_congr rfl; intro k _
            apply Finset.sum_congr rfl; intro i _
            have hk : A i k = A k i := hA_sym i k
            simp [hk]
      _ = ∑ k, ∑ i, y (k, j) * (A k i * y (i, l)) := by
            apply Finset.sum_congr rfl; intro k _
            apply Finset.sum_congr rfl; intro i _
            ring_nf
      _ = ∑ i, ∑ k, y (i, j) * (A i k * y (k, l)) := by
            rw [Finset.sum_comm]
      _ = ∑ i, y (i, j) * (∑ k, A i k * y (k, l)) := by
            simp [Finset.mul_sum, mul_left_comm]
  · -- Nonnegative quadratic form
    intro z
    -- The quadratic form is ∑_j z_j * ∑_l G_{jl} * z_l where G_{jl} = ∑_i colSlice(y,j)_i * (A * colSlice(y,l))_i
    -- This can be written as ⟨w, A w⟩ where w = ∑_j z_j * colSlice(y, j)
    let w : ι → ℝ := fun i => ∑ j, z j * (colSlice (ι:=ι) y j) i

    suffices h : star z ⬝ᵥ Matrix.mulVec (fun j l : ι => ∑ i, (colSlice (ι:=ι) y j) i * (A.mulVec (colSlice (ι:=ι) y l)) i) z
                = star w ⬝ᵥ A.mulVec w by
      rw [h]
      -- Since A is positive semidefinite, star w ⬝ᵥ A.mulVec w ≥ 0
      have hA_psd : A.PosSemidef := hA.posSemidef
      exact hA_psd.dotProduct_mulVec_nonneg w

    -- Prove the equality by expanding both sides to the same expression
    -- Key helper: rewrite the inner sum on the right into (A.mulVec w) i
    have hinner : ∀ i : ι, (∑ l, z l * (A.mulVec (colSlice (ι:=ι) y l)) i) = (A.mulVec w) i := by
      intro i; classical
      calc
        ∑ l, z l * (A.mulVec (colSlice (ι:=ι) y l)) i
            = ∑ l, z l * (∑ k, A i k * (colSlice (ι:=ι) y l) k) := by
                simp only [Matrix.mulVec, colSlice, dotProduct]
        _ = ∑ l, ∑ k, z l * (A i k * (colSlice (ι:=ι) y l) k) := by
                simp [Finset.mul_sum]
        _ = ∑ k, ∑ l, z l * (A i k * (colSlice (ι:=ι) y l) k) := by
                rw [Finset.sum_comm]
        _ = ∑ k, (∑ l, (z l * (colSlice (ι:=ι) y l) k) * A i k) := by
                apply Finset.sum_congr rfl; intro k _
                apply Finset.sum_congr rfl; intro l _
                ring
        _ = ∑ k, (∑ l, z l * (colSlice (ι:=ι) y l) k) * A i k := by
                apply Finset.sum_congr rfl; intro k _
                simp [Finset.sum_mul]
        _ = ∑ k, A i k * (∑ l, z l * (colSlice (ι:=ι) y l) k) := by
                apply Finset.sum_congr rfl; intro k _
                ring
        _ = (A.mulVec w) i := by
                simp only [Matrix.mulVec, w, colSlice, dotProduct]

    -- Left-hand side expands to Σ_i w i * (Σ_l z l * (A.mulVec (colSlice y l)) i)
    have hL :
        star z ⬝ᵥ Matrix.mulVec (fun j l : ι => ∑ i, (colSlice (ι:=ι) y j) i * (A.mulVec (colSlice (ι:=ι) y l)) i) z
        = ∑ i, w i * (∑ l, z l * (A.mulVec (colSlice (ι:=ι) y l)) i) := by
      classical
      -- Start from the LHS and expand to a triple sum
      have h0 :
        star z ⬝ᵥ Matrix.mulVec (fun j l : ι => ∑ i, (colSlice (ι:=ι) y j) i * (A.mulVec (colSlice (ι:=ι) y l)) i) z
        = ∑ j, z j * ∑ l, (∑ i, (colSlice (ι:=ι) y j) i * (A.mulVec (colSlice (ι:=ι) y l)) i) * z l := by
        simp [dotProduct, star, Matrix.mulVec]
      -- Turn into a quadruple sum and regroup by i
      have h1 :
         ∑ j, z j * ∑ l, (∑ i, (colSlice (ι:=ι) y j) i * (A.mulVec (colSlice (ι:=ι) y l)) i) * z l
         = ∑ i, ∑ j, ∑ l, z j * ((colSlice (ι:=ι) y j) i * (A.mulVec (colSlice (ι:=ι) y l)) i) * z l := by
         classical
         -- expand to a double sum over j,l
         have hjl :
           (∑ j, z j * ∑ l, (∑ i, (colSlice (ι:=ι) y j) i * (A.mulVec (colSlice (ι:=ι) y l)) i) * z l)
           = ∑ j, ∑ l, z j * ((∑ i, (colSlice (ι:=ι) y j) i * (A.mulVec (colSlice (ι:=ι) y l)) i) * z l) := by
           simp [Finset.mul_sum]
         -- push the inner sum over i out using sum-mul identities, then bring z j inside
         have hdist :
           ∑ j, ∑ l, z j * ((∑ i, (colSlice (ι:=ι) y j) i * (A.mulVec (colSlice (ι:=ι) y l)) i) * z l)
           = ∑ j, ∑ l, ∑ i, z j * (((colSlice (ι:=ι) y j) i * (A.mulVec (colSlice (ι:=ι) y l)) i) * z l) := by
           apply Finset.sum_congr rfl; intro j _
           apply Finset.sum_congr rfl; intro l _
           -- for fixed j,l:
           -- z j * ((∑ i, f i) * z l) = ∑ i, z j * (f i * z l)
           simp [Finset.sum_mul, Finset.mul_sum]
         -- swap l and i for each fixed j
         have hswap_li :
           (∑ j, ∑ l, ∑ i, z j * (((colSlice (ι:=ι) y j) i * (A.mulVec (colSlice (ι:=ι) y l)) i) * z l))
           = ∑ j, ∑ i, ∑ l, z j * (((colSlice (ι:=ι) y j) i * (A.mulVec (colSlice (ι:=ι) y l)) i) * z l) := by
           apply Finset.sum_congr rfl; intro j _
           rw [Finset.sum_comm]
         -- swap outer j and i
         have hswap_ji :
           (∑ j, ∑ i, ∑ l, z j * (((colSlice (ι:=ι) y j) i * (A.mulVec (colSlice (ι:=ι) y l)) i) * z l))
           = ∑ i, ∑ j, ∑ l, z j * (((colSlice (ι:=ι) y j) i * (A.mulVec (colSlice (ι:=ι) y l)) i) * z l) := by
           rw [Finset.sum_comm]
         -- reassociate to match the target parenthesization
         have hassoc :
           (∑ i, ∑ j, ∑ l, z j * (((colSlice (ι:=ι) y j) i * (A.mulVec (colSlice (ι:=ι) y l)) i) * z l))
           = ∑ i, ∑ j, ∑ l, z j * (( (colSlice (ι:=ι) y j) i * (A.mulVec (colSlice (ι:=ι) y l)) i)) * z l := by
           apply Finset.sum_congr rfl; intro i _
           apply Finset.sum_congr rfl; intro j _
           apply Finset.sum_congr rfl; intro l _
           -- z j * ((a*b) * z l) = z j * (a*b) * z l
           ac_rfl
         exact hjl.trans (hdist.trans (hswap_li.trans (hswap_ji.trans hassoc)))
      -- Factor the inner double sum as a product of sums at fixed i using `sum_mul_sum`
      have h2 :
        (∑ i, ∑ j, ∑ l, z j * ((colSlice (ι:=ι) y j) i * (A.mulVec (colSlice (ι:=ι) y l)) i) * z l)
        = ∑ i, (∑ j, z j * (colSlice (ι:=ι) y j) i) * (∑ l, z l * (A.mulVec (colSlice (ι:=ι) y l)) i) := by
        classical
        apply Finset.sum_congr rfl; intro i _
        -- align the summand to F j * G l form
        have halign :
          (∑ j, ∑ l, z j * (( (colSlice (ι:=ι) y j) i * (A.mulVec (colSlice (ι:=ι) y l)) i)) * z l)
          = ∑ j, ∑ l, (z j * (colSlice (ι:=ι) y j) i) * (((A.mulVec (colSlice (ι:=ι) y l)) i) * z l) := by
          apply Finset.sum_congr rfl; intro j _
          apply Finset.sum_congr rfl; intro l _
          -- z j * (a*b) * z l = (z j * a) * (b * z l)
          ac_rfl
        have hprod :
          ∑ j, ∑ l, (z j * (colSlice (ι:=ι) y j) i) * (((A.mulVec (colSlice (ι:=ι) y l)) i) * z l)
          = (∑ j, z j * (colSlice (ι:=ι) y j) i) * (∑ l, ((A.mulVec (colSlice (ι:=ι) y l)) i) * z l) := by
          simp [Finset.sum_mul_sum]
            -- using (Finset.sum_mul_sum ...)
        have hcomm_l :
          (∑ l, ((A.mulVec (colSlice (ι:=ι) y l)) i) * z l)
          = ∑ l, z l * (A.mulVec (colSlice (ι:=ι) y l)) i := by
          apply Finset.sum_congr rfl; intro l _
          simp [mul_comm]
        -- combine
        have := halign.trans hprod
        simpa [hcomm_l] using this
      -- Put the pieces together and rewrite `w`, using h0 for the LHS expansion
      -- Recall w i = ∑ j, z j * (colSlice y j)
      -- Also expand the left-hand side dotProduct form via h0
      simpa [w] using h0.trans (h1.trans h2)

    -- Right-hand side is ∑ i, w i * (A.mulVec w) i
    have hR : star w ⬝ᵥ A.mulVec w = ∑ i, w i * (A.mulVec w) i := by
      simp [dotProduct, star, Matrix.mulVec]

    -- Combine the two by rewriting the inner sum using hinner
    have : ∑ i, w i * (∑ l, z l * (A.mulVec (colSlice (ι:=ι) y l)) i)
           = ∑ i, w i * (A.mulVec w) i := by
      classical
      apply Finset.sum_congr rfl; intro i _
      simp [hinner i]

    -- Conclude the desired equality
    exact by
      -- transform LHS using hL, then rewrite inner sum via hinner, then fold back to RHS using hR
      simpa [this, hR] using hL

/-- If A and B are positive definite, then the Kronecker-like product is positive definite. -/
lemma kronLike_posDef
  (A B : Matrix ι ι ℝ) (hA : A.PosDef) (hB : B.PosDef) :
  (kronLike (ι:=ι) A B).PosDef := by
  -- To show positive definiteness, we use the characterization via dotProduct_mulVec
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  constructor
  · -- First show it's Hermitian (symmetric for real matrices)
    rw [Matrix.IsHermitian]
    ext p q
    simp [kronLike, Matrix.conjTranspose]
    -- For real matrices, conjugate is just the identity
    -- Use the symmetry of A and B (follows from PosDef)
    have hA_sym : A p.1 q.1 = A q.1 p.1 := by
      rw [← Matrix.IsHermitian.apply hA.isHermitian]
      simp
    have hB_sym : B p.2 q.2 = B q.2 p.2 := by
      rw [← Matrix.IsHermitian.apply hB.isHermitian]
      simp
    rw [hA_sym, hB_sym]
  · -- Now show positivity of the quadratic form
    intro y hy
    -- Use the spectral theorem approach, but simplified
    -- Key insight: use kronLike_quadratic_sum to express quadratic form in terms of A-quadratic forms

    -- Since we have kronLike_quadratic_sum available (even if it has sorry), use it conceptually
    have hquad_form : y ⬝ᵥ (kronLike (ι:=ι) A B).mulVec y =
        ∑ j, ∑ l, (∑ i, (colSlice (ι:=ι) y j) i * (A.mulVec (colSlice (ι:=ι) y l)) i) * B j l := by
      classical
      simpa [dotProduct] using
        (kronLike_quadratic_sum (ι:=ι) A B y)

    -- Over reals, star y = y
    have star_y_eq : star y = y := by
      ext p
      simp [star]

    rw [star_y_eq, hquad_form]

    -- Define the Gram matrix G_{jl} = ∑_i colSlice(y,j)_i * (A * colSlice(y,l))_i
    let G : Matrix ι ι ℝ := fun j l => ∑ i, (colSlice (ι:=ι) y j) i * (A.mulVec (colSlice (ι:=ι) y l)) i

    -- The quadratic form becomes ∑_{j,l} G_{jl} * B_{jl}
    change 0 < ∑ j, ∑ l, G j l * B j l

    -- Key insight: This is the Frobenius inner product ⟨G, B⟩ = trace(G^T * B) = trace(G * B) (since G real)
    -- Since B is positive definite, its eigenvalues are positive
    -- Since G arises from A (positive definite) acting on colSlice vectors, G is positive semidefinite
    -- The Frobenius product of two positive semidefinite matrices with one being positive definite is positive
    -- if the first matrix is nonzero

    -- Show G ≠ 0
    have hG_ne_zero : G ≠ 0 := by
      -- If G = 0, then for all j,l: ∑_i colSlice(y,j)_i * (A * colSlice(y,l))_i = 0
      -- Taking j = l and summing over j: ∑_j ∑_i colSlice(y,j)_i * (A * colSlice(y,j))_i = 0
      -- But this equals ∑_j ⟨colSlice(y,j), A * colSlice(y,j)⟩ = 0
      -- Since A is positive definite, this implies all colSlice(y,j) = 0, hence y = 0, contradiction
      intro hG_zero
      apply hy
      ext ⟨i, j⟩
      -- Since G = 0, we have G j j = 0, i.e., ∑_k colSlice(y,j)_k * (A * colSlice(y,j))_k = 0
      have hGjj : G j j = 0 := by
        rw [hG_zero]; rfl
      simp [G] at hGjj
      -- Since A is positive definite and ∑_k colSlice(y,j)_k * (A * colSlice(y,j))_k = 0,
      -- we must have colSlice(y,j) = 0, hence y(i,j) = 0
      -- hGjj says: ∑_x y(x,j) * (A * colSlice(y,j))_x = 0
      -- This is the dotProduct ⟨colSlice(y,j), A * colSlice(y,j)⟩ = 0
      have hcolSlice_zero : colSlice (ι:=ι) y j = 0 := by
        -- Since A is positive definite, if ⟨v, A * v⟩ = 0 then v = 0
        by_contra h_ne_zero
        -- Apply positive definiteness of A to colSlice(y,j) ≠ 0
        have hpos := hA.dotProduct_mulVec_pos h_ne_zero
        -- We have ⟨colSlice(y,j), A * colSlice(y,j)⟩ = 0 from hGjj
        -- The positive definiteness condition is star x ⬝ᵥ A.mulVec x > 0
        -- For real vectors, star x = x, and dotProduct x (A.mulVec x) = x ⬝ᵥ A.mulVec x
        have heq_zero : (colSlice (ι:=ι) y j) ⬝ᵥ (A.mulVec (colSlice (ι:=ι) y j)) = 0 := by
          simp [dotProduct, colSlice] at hGjj ⊢
          exact hGjj
        -- Over reals, star (colSlice y j) = colSlice y j, so we need star colSlice y j ⬝ᵥ A.mulVec colSlice y j = 0
        have star_col : star (colSlice (ι:=ι) y j) = colSlice (ι:=ι) y j := by
          ext k
          simp [star]
        -- Rewrite the positive condition using star_col
        rw [star_col] at hpos
        -- Now we have hpos: 0 < colSlice y j ⬝ᵥ A.mulVec (colSlice y j) and heq_zero: ... = 0
        rw [heq_zero] at hpos
        -- Contradiction: 0 < 0
        exact lt_irrefl 0 hpos
      -- Now since colSlice(y,j) = 0, we have y(i,j) = 0
      have hcol_at_i : (colSlice (ι:=ι) y j) i = 0 := by
        rw [hcolSlice_zero]; rfl
      simp [colSlice] at hcol_at_i
      exact hcol_at_i

    -- Use the fact that for positive semidefinite G and positive definite B,
    -- if G ≠ 0, then ∑_{j,l} G_{jl} * B_{jl} > 0
    -- This follows from spectral theory: both can be diagonalized, and the result
    -- is a sum of products of nonnegative and positive eigenvalues with at least one positive term
    -- Use the general Frobenius-positivity lemma
    have hG_psd : G.PosSemidef := by
      -- G is a Gram matrix built from A and the slices of y
      simpa [G] using gram_psd_from_A_posdef (ι:=ι) A hA y
    exact frobenius_pos_of_psd_posdef G B hG_psd hG_ne_zero hB

/-- Schur product theorem (real case, finite index):
If A B are positive definite matrices over ℝ, then the Hadamard product is positive definite. -/
@[simp] theorem schur_product_posDef
  (A B : Matrix ι ι ℝ)
  (hA : A.PosDef) (hB : B.PosDef) :
  (A ∘ₕ B).PosDef := by
  classical
  -- Use the characterization via dotProduct_mulVec
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  constructor
  · -- Hermitian: follows from Hermitian of A and B
    have hAh : A.IsHermitian := hA.isHermitian
    have hBh : B.IsHermitian := hB.isHermitian
    -- Show (A ∘ₕ B) is Hermitian
    rw [Matrix.IsHermitian]
    ext i j
    simp [Matrix.conjTranspose]
    -- use hermitian entries symmetry (over ℝ, star is id)
    have hAij : A i j = A j i := by
      simpa using (Matrix.IsHermitian.apply hAh i j).symm
    have hBij : B i j = B j i := by
      simpa using (Matrix.IsHermitian.apply hBh i j).symm
    -- rearrange
    simp [hAij, hBij]
  · -- Positivity: diagonal restriction of kronLike
    intro x hx
    -- Define diagonal embedding y from x
    let y : ι × ι → ℝ := diagEmbed (ι:=ι) x
    have hy : y ≠ 0 := diagEmbed_ne_zero_of_ne_zero (ι:=ι) hx
    -- kronLike is positive definite hence positive on y
    have hk := (kronLike_posDef (ι:=ι) A B hA hB).dotProduct_mulVec_pos hy
    -- The quadratic forms coincide on diagonal-embedded vectors
    have hquad_eq : y ⬝ᵥ (kronLike (ι:=ι) A B).mulVec y = x ⬝ᵥ (A ∘ₕ B).mulVec x := by
      classical
      -- expand LHS to sums over pairs and use kronLike_mulVec
      calc
        y ⬝ᵥ (kronLike (ι:=ι) A B).mulVec y
            = ∑ p, y p * ((kronLike (ι:=ι) A B).mulVec y) p := by
              simp [dotProduct]
        _ = ∑ i, ∑ j, y (i, j) * ((kronLike (ι:=ι) A B).mulVec y) (i, j) := by
              exact sum_pairs_eq_double fun p => y p * (kronLike A B).mulVec y p
        _ = ∑ i, ∑ j, y (i, j) * (∑ k, ∑ l, (A i k * B j l) * y (k, l)) := by
              apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
              simp [kronLike_mulVec]
        _ = ∑ i, ∑ k, x i * ((A i k * B i k) * x k) := by
              -- Kill off-diagonal terms using diagEmbed definition
              simp [y, diagEmbed, Finset.mul_sum, eq_comm]
        _ = x ⬝ᵥ (A ∘ₕ B).mulVec x := by
              -- expand RHS: Hadamard mulVec then dot
              simp [dotProduct, Matrix.mulVec, Matrix.hadamard, Finset.mul_sum, mul_comm, mul_left_comm]
    -- transport positivity
    simpa [hquad_eq] using hk

end OSforGFF
