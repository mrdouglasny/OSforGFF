import Mathlib.MeasureTheory.Measure.CharacteristicFunction
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import OSforGFF.FiniteDimGaussian

/-!
# Finite-dimensional characteristic-function API (Bochner pipeline scaffolding)

This file provides the finite-dimensional **characteristic function** API needed for a
Bochner–Minlos strategy:

- functoriality of `charFun` under continuous linear maps (pushforward ↔ precomposition with adjoint),
- uniqueness of a finite measure from its characteristic function (`Measure.ext_of_charFun`),
  specialized to Euclidean spaces.

The **general existence** direction of Bochner's theorem (continuous positive-definite normalized
`φ : E → ℂ` gives a unique probability measure with `charFun μ = φ`) is not currently available in
mathlib.

However, for the **Gaussian** characteristic functions arising from a positive semidefinite
covariance matrix, existence is available in `OSforGFF/FiniteDimGaussian.lean`, and we
provide it here as part of the Bochner–Minlos pipeline infrastructure.
-/

open scoped RealInnerProductSpace

open MeasureTheory Complex

namespace OSforGFF

noncomputable section

section Functoriality

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [MeasurableSpace F] [BorelSpace F]

/-- Functoriality of characteristic functions under continuous linear maps:

`charFun (μ.map L) t = charFun μ (L.adjoint t)`.

Pushforward ↔ precomposition rule used to prove projectivity via characteristic
functions. -/
theorem charFun_map_clm (μ : Measure E) (L : E →L[ℝ] F) (t : F) :
    charFun (μ.map L) t = charFun μ (L.adjoint t) := by
  simp only [MeasureTheory.charFun]
  have hL : AEMeasurable (fun x : E => L x) μ :=
    (L.continuous.measurable.aemeasurable)
  rw [integral_map hL (by fun_prop)]
  congr 1
  ext x
  have h : ⟪L x, t⟫ = ⟪x, L.adjoint t⟫ := by
    simpa using (L.adjoint_inner_right x t).symm
  simp [h]

end Functoriality

section Uniqueness

variable {n : ℕ}

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

instance : MeasurableSpace (E n) := borel _
instance : BorelSpace (E n) := ⟨rfl⟩
instance : CompleteSpace (E n) := by infer_instance
instance : SecondCountableTopology (E n) := by infer_instance

/-- Uniqueness: a finite measure on `EuclideanSpace` is determined by its characteristic function. -/
theorem Measure.ext_of_charFun_euclidean
    {μ ν : Measure (E n)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : charFun μ = charFun ν) : μ = ν :=
  Measure.ext_of_charFun h

end Uniqueness

section Gaussian

open scoped MatrixOrder
open scoped RealInnerProductSpace InnerProductSpace

open OSforGFF.FiniteDimGaussian

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Gaussian existence+uniqueness from a positive semidefinite covariance matrix, packaged in the
`ProbabilityMeasure` form.

This is the finite-dimensional “Bochner theorem” for the Gaussian characteristic functions used
throughout the project. -/
theorem existsUnique_gaussianOfPosSemidef_charFun
    (Sigma : Matrix n n ℝ) (hSigma : Sigma.PosSemidef) :
    ∃! μ : ProbabilityMeasure (EuclideanSpace ℝ n),
      ∀ t : EuclideanSpace ℝ n,
        MeasureTheory.charFun μ.toMeasure t =
          Complex.exp (-(1 / 2 : ℂ) *
            ⟪t, (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) Sigma) t⟫_ℝ) := by
  refine ⟨⟨gaussianOfPosSemidef (n := n) Sigma hSigma, inferInstance⟩, ?_, ?_⟩
  · intro t
    simpa using (charFun_gaussianOfPosSemidef (n := n) Sigma hSigma t)
  · intro ν hν
    have hcf : MeasureTheory.charFun (gaussianOfPosSemidef (n := n) Sigma hSigma) =
        MeasureTheory.charFun ν.toMeasure := by
      funext t
      simpa [hν t] using (charFun_gaussianOfPosSemidef (n := n) Sigma hSigma t)
    have : (gaussianOfPosSemidef (n := n) Sigma hSigma) = ν.toMeasure :=
      Measure.ext_of_charFun hcf
    ext s hs
    simp [this]

end Gaussian

end

end OSforGFF
