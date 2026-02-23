/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/

import Mathlib.Tactic  -- gives `ext` and `simp` power
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.Group.Support
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Calculus.BumpFunction.Convolution

import Mathlib.Topology.Algebra.Module.LinearMapPiProd

import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Density

import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Real

import Mathlib.Topology.Basic
import Mathlib.Order.Filter.Basic

import OSforGFF.Basic
import OSforGFF.Schwinger
import OSforGFF.FunctionalAnalysis
import OSforGFF.Euclidean
import OSforGFF.DiscreteSymmetry
import OSforGFF.PositiveTimeTestFunction_real
import OSforGFF.ComplexTestFunction
import OSforGFF.TimeTranslation
import OSforGFF.SchwingerTwoPointFunction

/-!
## Osterwalder-Schrader Axioms

The four OS axioms characterizing Euclidean field theories that admit analytic
continuation to relativistic QFTs:

- **OS-0**: `OS0_Analyticity` - Complex analyticity of generating functionals
- **OS-1**: `OS1_Regularity` - Exponential bounds and temperedness
- **OS-2**: `OS2_EuclideanInvariance` - Euclidean group invariance
- **OS-3**: `OS3_ReflectionPositivity` - Reflection positivity (multiple formulations)
- **OS-4**: `OS4_Ergodicity` - Ergodicity and clustering properties

Following Glimm-Jaffe formulation using probability measures on field configurations.
Glimm and Jaffe, Quantum Physics, pp. 89-90
-/

open MeasureTheory NNReal ENNReal
open TopologicalSpace Measure QFT
open DFunLike (coe)

noncomputable section
open scoped MeasureTheory Complex BigOperators SchwartzMap

/-- OS0 (Holomorphicity / Analyticity): the generating functional is complex differentiable
in finite-dimensional complex directions.

In Glimm–Jaffe this is stated as analyticity.  In finite dimensions, complex Fréchet
differentiability (“holomorphicity”) implies analyticity; Mathlib has the needed
holomorphic⇒analytic infrastructure for one complex variable, and we use this holomorphic
formulation as the robust core axiom. -/
def OS0_Analyticity (dμ_config : ProbabilityMeasure FieldConfiguration) : Prop :=
  ∀ (n : ℕ) (J : Fin n → TestFunctionℂ),
    Differentiable ℂ (fun z : Fin n → ℂ =>
      GJGeneratingFunctionalℂ dμ_config (∑ i, z i • J i))

/-- Two-point function local integrability condition for p = 2 -/
def TwoPointIntegrable (dμ_config : ProbabilityMeasure FieldConfiguration) : Prop :=
  LocallyIntegrable (fun x => SchwingerTwoPointFunction dμ_config x) volume

/-- OS1 (Regularity): The complex generating functional satisfies exponential bounds. -/
def OS1_Regularity (dμ_config : ProbabilityMeasure FieldConfiguration) : Prop :=
  ∃ (p : ℝ) (c : ℝ), 1 ≤ p ∧ p ≤ 2 ∧ c > 0 ∧
    (∀ (f : TestFunctionℂ),
      ‖GJGeneratingFunctionalℂ dμ_config f‖ ≤
        Real.exp (c * (∫ x, ‖f x‖ ∂volume + ∫ x, ‖f x‖^p ∂volume))) ∧
    (p = 2 → TwoPointIntegrable dμ_config)

/-- OS2 (Euclidean Invariance): The measure is invariant under Euclidean transformations. -/
def OS2_EuclideanInvariance (dμ_config : ProbabilityMeasure FieldConfiguration) : Prop :=
  ∀ (g : QFT.E) (f : TestFunctionℂ),
    GJGeneratingFunctionalℂ dμ_config f =
    GJGeneratingFunctionalℂ dμ_config (QFT.euclidean_action g f)

/-- Real formulation of OS3 reflection positivity using the real-valued positive time
    subspace and the real generating functional. This version avoids explicit complex
    coefficients and conjugation, aligning more closely with the new real-valued
    `PositiveTimeTestFunction` infrastructure. -/
def OS3_ReflectionPositivity (dμ_config : ProbabilityMeasure FieldConfiguration) : Prop :=
  ∀ (n : ℕ) (f : Fin n → PositiveTimeTestFunction) (c : Fin n → ℝ),
    let reflection_matrix := fun i j : Fin n =>
      GJGeneratingFunctional dμ_config
        ((f i).val - compTimeReflectionReal ((f j).val))
    0 ≤ ∑ i, ∑ j, c i * c j * (reflection_matrix i j).re

/-- OS4 (Clustering): Clustering via correlation decay.

    This is an alternative formulation that directly expresses the clustering property:
    correlations between well-separated regions decay to zero. This is equivalent
    to ergodicity for translation-invariant measures.

    The key identity is: Z[f + T_a g] → Z[f] · Z[g] as |a| → ∞
    which says that distant test functions become statistically independent.

    Translation is implemented via SchwartzMap.translate.

    NOTE: This is stated for real test functions, which is the standard OS formulation.
    For real test functions, the generating functional satisfies |Z[f]| ≤ 1 due to
    positive definiteness of the covariance. The complex extension follows from
    analyticity (OS0) and regularity (OS1).
-/
def OS4_Clustering (dμ_config : ProbabilityMeasure FieldConfiguration) : Prop :=
  ∀ (f g : TestFunction) (ε : ℝ), ε > 0 → ∃ (R : ℝ), R > 0 ∧ ∀ (a : SpaceTime),
    ‖a‖ > R →
    ‖GJGeneratingFunctional dμ_config (f + g.translate a) -
     GJGeneratingFunctional dμ_config f * GJGeneratingFunctional dμ_config g‖ < ε

/-- OS4 (Ergodicity): For generating functions A(φ) = Σⱼ zⱼ e^{⟨φ,fⱼ⟩}, the time average
    converges to the expectation in L²(μ).

    lim_{T→∞} (1/T) ∫₀ᵀ A(T_s φ) ds → 𝔼_μ[A(φ)]

    This is the standard ergodicity formulation from Glimm-Jaffe.
-/
def OS4_Ergodicity (dμ_config : ProbabilityMeasure FieldConfiguration) : Prop :=
  ∀ (n : ℕ) (z : Fin n → ℂ) (f : Fin n → TestFunctionℂ),
    let μ := dμ_config.toMeasure
    let A : FieldConfiguration → ℂ := fun ω =>
      ∑ j, z j * Complex.exp (distributionPairingℂ_real ω (f j))
    Filter.Tendsto
      (fun T : ℝ =>
        ∫ ω, ‖(1 / T) * ∫ s in Set.Icc (0 : ℝ) T,
          A (TimeTranslation.timeTranslationDistribution s ω)
          - ∫ ω', A ω' ∂μ‖^2 ∂μ)
      Filter.atTop
      (nhds 0)

/-- OS4 (Polynomial Clustering): For any f, g ∈ S(ℝ × ℝ³) and any exponent α > 0,
    there exists c such that:

    |𝔼_μ[e^{⟨φ,f⟩ + ⟨T_s φ, g⟩}] - 𝔼_μ[e^{⟨φ,f⟩}] 𝔼_μ[e^{⟨φ,g⟩}]| ≤ c (1 + s)^{-α}

    This is a generalization of the clustering property that allows for any
    polynomial decay rate. For the GFF in 4D spacetime (d=3 spatial dimensions),
    the natural rate is α = 2d = 6 from the mass gap.
-/
def OS4_PolynomialClustering (dμ_config : ProbabilityMeasure FieldConfiguration)
    (α : ℝ) (_hα : α > 0) : Prop :=
  ∀ (f g : TestFunctionℂ), ∃ (c : ℝ), c ≥ 0 ∧
    let μ := dμ_config.toMeasure
    ∀ s : ℝ, s ≥ 0 →
      ‖∫ ω, Complex.exp (distributionPairingℂ_real ω f +
            distributionPairingℂ_real (TimeTranslation.timeTranslationDistribution s ω) g) ∂μ
        - (∫ ω, Complex.exp (distributionPairingℂ_real ω f) ∂μ) *
          (∫ ω, Complex.exp (distributionPairingℂ_real ω g) ∂μ)‖
      ≤ c * (1 + s)^(-α)

/-! ## Bundled Axiom Conjunction -/

/-- A probability measure on field configurations satisfies all Osterwalder-Schrader axioms.
    This bundles OS0 through OS4 (clustering and ergodicity) into a single predicate. -/
structure SatisfiesAllOS (dμ_config : ProbabilityMeasure FieldConfiguration) : Prop where
  os0 : OS0_Analyticity dμ_config
  os1 : OS1_Regularity dμ_config
  os2 : OS2_EuclideanInvariance dμ_config
  os3 : OS3_ReflectionPositivity dμ_config
  os4_clustering : OS4_Clustering dμ_config
  os4_ergodicity : OS4_Ergodicity dμ_config
