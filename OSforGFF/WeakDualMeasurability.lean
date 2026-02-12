import Mathlib.Topology.Algebra.Module.WeakDual
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Measurability lemmas for `WeakDual`

Masurability facts about the weak-* dual
`WeakDual ℝ E = (E →L[ℝ] ℝ)` equipped with the Borel σ-algebra of its weak-* topology.

These are useful when transporting measures between `WeakDual ℝ E` and function spaces via the
evaluation maps.
-/

open MeasureTheory
open scoped BigOperators

namespace OSforGFF

noncomputable section

namespace WeakDual

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

@[measurability]
theorem measurable_eval (f : E) [MeasurableSpace (WeakDual ℝ E)] [BorelSpace (WeakDual ℝ E)] :
    Measurable fun ω : WeakDual ℝ E => ω f := by
  simpa using (WeakDual.eval_continuous (𝕜 := ℝ) (E := E) f).measurable

@[measurability]
theorem aemeasurable_eval (f : E) [MeasurableSpace (WeakDual ℝ E)] [BorelSpace (WeakDual ℝ E)]
    (μ : Measure (WeakDual ℝ E)) :
    AEMeasurable (fun ω : WeakDual ℝ E => ω f) μ := by
  exact (measurable_eval (E := E) f).aemeasurable

@[measurability]
theorem measurable_coeFun [MeasurableSpace (WeakDual ℝ E)] [BorelSpace (WeakDual ℝ E)] :
    Measurable fun ω : WeakDual ℝ E => (fun f : E => ω f) := by
  -- Measurability into a Π-type is coordinatewise.
  refine measurable_pi_lambda _ (fun f => ?_)
  simpa using measurable_eval (E := E) f

@[measurability]
theorem aemeasurable_coeFun [MeasurableSpace (WeakDual ℝ E)] [BorelSpace (WeakDual ℝ E)]
    (μ : Measure (WeakDual ℝ E)) :
    AEMeasurable (fun ω : WeakDual ℝ E => (fun f : E => ω f)) μ := by
  exact (measurable_coeFun (E := E)).aemeasurable

end WeakDual

end
end OSforGFF
