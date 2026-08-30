/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Copyright (c) 2026 Sergey A. Cherkis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergey A. Cherkis, Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/

import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

import OSforGFF.Spacetime.Basic
import OSforGFF.OS.Axioms
import OSforGFF.Measure.Construct
import OSforGFF.Measure.IsGaussian
import OSforGFF.Spacetime.Euclidean
import OSforGFF.Spacetime.DiscreteSymmetry
import OSforGFF.General.FunctionalAnalysis
import OSforGFF.Measure.Minlos
import OSforGFF.Measure.MinlosAnalytic
import OSforGFF.Schwinger.Defs

/-!
# Euclidean invariance of Gaussian measures

A Gaussian measure inherits OS2 (Euclidean invariance) from its covariance:
`gaussian_satisfies_OS2` shows that when the complex 2-point function is invariant under
the Euclidean group (`CovarianceEuclideanInvariantℂ`), the Gaussian generating functional
`Z[f] = exp(−½⟨f, Cf⟩)` satisfies `Z[gf] = Z[f]` for every Euclidean motion `g`.
-/

open MeasureTheory Complex
open TopologicalSpace SchwartzMap

noncomputable section

variable {d : ℕ} [Fact (2 ≤ d)]

open scoped BigOperators
open Finset

/-! ## OS2: Euclidean Invariance for Translation-Invariant Gaussian Measures

Euclidean invariance follows if the covariance operator commutes with Euclidean transformations.
For translation-invariant measures, this is equivalent to the covariance depending only on
differences of spacetime points.
-/

/-- Assumption: The complex covariance is invariant under Euclidean transformations -/
def CovarianceEuclideanInvariantℂ (dμ_config : ProbabilityMeasure (FieldConfiguration d)) : Prop :=
  ∀ (g : QFT.E d) (f h : SchwartzTestFunctionℂ d),
    SchwingerFunctionℂ₂ dμ_config (QFT.euclidean_action g f) (QFT.euclidean_action g h) =
    SchwingerFunctionℂ₂ dμ_config f h

omit [Fact (2 ≤ d)] in
theorem gaussian_satisfies_OS2
  (dμ_config : ProbabilityMeasure (FieldConfiguration d))
  (h_gaussian : isGaussianGJ dμ_config)
  (h_euclidean_invariant : CovarianceEuclideanInvariantℂ dμ_config)
  : OS2_EuclideanInvariance dμ_config := by
  -- For Gaussian measures: Z[f] = exp(-½⟨f, Cf⟩)
  -- If C commutes with Euclidean transformations g, then:
  -- Z[gf] = exp(-½⟨gf, C(gf)⟩) = exp(-½⟨f, Cf⟩) = Z[f]
  intro g f

  -- Extract Gaussian form for both Z[f] and Z[gf]
  have h_form := h_gaussian.2

  -- Apply Gaussian form to both sides
  rw [h_form f, h_form (QFT.euclidean_action g f)]

  -- Show the exponents are equal: ⟨gf, C(gf)⟩ = ⟨f, Cf⟩
  -- This follows directly from Euclidean invariance of the complex covariance
  congr 2
  -- Use Euclidean invariance directly (symmetric form)
  exact (h_euclidean_invariant g f f).symm

