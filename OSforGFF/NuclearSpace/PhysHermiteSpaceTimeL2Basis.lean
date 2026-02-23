import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Function.L2Space

import OSforGFF.NuclearSpace.PhysHermiteL2Basis

/-!
# Product harmonic-oscillator eigenfunctions on `Fin n → ℝ`

This file provides a small, reusable API for the `n`-fold product of the 1D harmonic-oscillator
eigenfunctions `eigenfunctionReal ξ n`, together with the basic `L²` facts needed later (measurability
and `MemLp`).

The actual spacetime (`SpaceTime = ℝ⁴`) Hilbert basis / Parseval step is developed in a subsequent
file.
-/

open scoped BigOperators ENNReal RealInnerProductSpace

namespace PhysLean

noncomputable section

open MeasureTheory

namespace SpaceTimeHermite

variable {n : ℕ}

/-- The `n`-fold product eigenfunction indexed by a multi-index `k : Fin n → ℕ`. -/
noncomputable def eigenfunctionProd (ξ : ℝ) (k : Fin n → ℕ) (x : Fin n → ℝ) : ℝ :=
  ∏ i : Fin n, eigenfunctionReal ξ (k i) (x i)

@[simp] lemma eigenfunctionProd_apply (ξ : ℝ) (k : Fin n → ℕ) (x : Fin n → ℝ) :
    eigenfunctionProd (n := n) ξ k x = ∏ i : Fin n, eigenfunctionReal ξ (k i) (x i) := rfl

lemma integrable_eigenfunctionProd_sq (ξ : ℝ) (hξ : ξ ≠ 0) (k : Fin n → ℕ) :
    Integrable (fun x : (Fin n → ℝ) => (eigenfunctionProd (n := n) ξ k x) ^ 2)
      (volume : Measure (Fin n → ℝ)) := by
  classical
  -- expand the square as a product of squares and use the `fintype_prod` lemma
  have hfactor (i : Fin n) :
      Integrable (fun t : ℝ => (eigenfunctionReal ξ (k i) t) ^ 2) (volume : Measure ℝ) := by
    simpa [pow_two] using
      (HarmonicOscillator.integrable_eigenfunctionReal_sq (ξ := ξ) (hξ := hξ) (n := k i))
  -- apply the `Integrable.fintype_prod` lemma on the finite product space
  simpa [eigenfunctionProd, pow_two, Finset.prod_mul_distrib] using
    (MeasureTheory.Integrable.fintype_prod (ι := Fin n) (μ := fun _ : Fin n => (volume : Measure ℝ))
      (f := fun i : Fin n => fun t : ℝ => (eigenfunctionReal ξ (k i) t) ^ 2) hfactor)

lemma aestronglyMeasurable_eigenfunctionProd (ξ : ℝ) (hξ : ξ ≠ 0) (k : Fin n → ℕ) :
    AEStronglyMeasurable (eigenfunctionProd (n := n) ξ k) (volume : Measure (Fin n → ℝ)) := by
  classical
  -- each factor is continuous, hence (ae-)strongly measurable; finite products preserve this.
  have hfactor (i : Fin n) :
      AEStronglyMeasurable (fun x : (Fin n → ℝ) => eigenfunctionReal ξ (k i) (x i))
        (volume : Measure (Fin n → ℝ)) := by
    have hcont : Continuous (eigenfunctionReal ξ (k i)) :=
      HarmonicOscillator.continuous_eigenfunctionReal (ξ := ξ) (hξ := hξ) (n := k i)
    -- evaluation at coordinate `i` is measurable, so we can compose.
    exact (hcont.aestronglyMeasurable.comp_measurable (measurable_pi_apply i))
  -- now take the product over `Fin n`
  simpa [eigenfunctionProd] using
    (Finset.aestronglyMeasurable_fun_prod (s := (Finset.univ : Finset (Fin n)))
      (f := fun i : Fin n => fun x : (Fin n → ℝ) => eigenfunctionReal ξ (k i) (x i))
      (by
        intro i hi
        simpa using hfactor i))

lemma memLp_eigenfunctionProd (ξ : ℝ) (hξ : ξ ≠ 0) (k : Fin n → ℕ) :
    MemLp (eigenfunctionProd (n := n) ξ k) 2 (volume : Measure (Fin n → ℝ)) := by
  -- `MemLp` at `p=2` is equivalent to integrability of the square.
  have hmeas :
      AEStronglyMeasurable (eigenfunctionProd (n := n) ξ k) (volume : Measure (Fin n → ℝ)) :=
    aestronglyMeasurable_eigenfunctionProd (n := n) (ξ := ξ) (hξ := hξ) k
  refine (MeasureTheory.memLp_two_iff_integrable_sq hmeas).2 ?_
  simpa using integrable_eigenfunctionProd_sq (n := n) (ξ := ξ) (hξ := hξ) k

end SpaceTimeHermite

end

end PhysLean
