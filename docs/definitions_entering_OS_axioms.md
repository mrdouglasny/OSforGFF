# Definitions Entering the OS Axiom Statements

The library is **dimension-generic**: every definition below is parameterized by the spacetime
dimension `d : ℕ` (a `variable {d}` in scope), so `SpaceTime`, `SchwartzTestFunction`, `E`, `O`,
`FieldConfiguration` in the snippets mean `SpaceTime d`, `SchwartzTestFunction d`, `E d`, `O d`,
`FieldConfiguration d`. The master theorem is:

```lean
-- dimension-generic form (any d ≥ 2, given a GFFPropagator d m instance):
theorem gaussianFreeField_satisfies_all_OS_axioms_generic
    {d : ℕ} [Fact (2 ≤ d)] (m : ℝ) [Fact (0 < m)] [GFFPropagator d m] :
    SatisfiesAllOS (gaussianFreeField_free (d := d) m)

-- four-dimensional instance:
theorem gaussianFreeField_satisfies_all_OS_axioms_dim4 (m : ℝ) [Fact (0 < m)] :
    SatisfiesAllOS (μ_GFF 4 m)
```

A correct proof guarantees the *theorem statement* is true — but only relative to the
definitions it references. If a definition encodes the wrong mathematical concept, the
theorem proves the wrong thing regardless of the proof. This document lists every
definition entering the statements of OS0–OS4 and assesses correctness. (Because every OS-axiom
`Prop` is parameterized only by the measure, and the dimension lives entirely in the types, the
assessments below hold uniformly in `d`.)

---

## 1. `GJGeneratingFunctional` — sign of i

**Definition** ([Spacetime/Basic.lean](../OSforGFF/Spacetime/Basic.lean)):
```lean
def GJGeneratingFunctional (dμ_config : ProbabilityMeasure FieldConfiguration)
  (J : SchwartzTestFunction) : ℂ :=
  ∫ ω, Complex.exp (Complex.I * (distributionPairing ω J : ℂ)) ∂dμ_config.toMeasure
```

**Used in**: OS3, OS4_Clustering.

**Assessment**: This is `Z[J] = ∫ exp(i⟨ω,J⟩) dμ(ω)`, matching the standard Glimm–Jaffe
convention (Quantum Physics, p. 89). The sign `+i` is correct — the opposite sign `−i`
would give the complex conjugate `Z̄[J]`, which would break OS3 (the reflection positivity
matrix would be conjugate-transposed). **Correct.**

---

## 2. `GJGeneratingFunctionalℂ` and `distributionPairingℂ_real` — complex extension

**Definitions** ([Spacetime/Basic.lean](../OSforGFF/Spacetime/Basic.lean)):
```lean
def distributionPairingℂ_real (ω : FieldConfiguration) (f : SchwartzTestFunctionℂ) : ℂ :=
  let ⟨f_re, f_im⟩ := complex_testfunction_decompose f
  (ω f_re : ℂ) + Complex.I * (ω f_im : ℂ)

def GJGeneratingFunctionalℂ (dμ_config : ProbabilityMeasure FieldConfiguration)
  (J : SchwartzTestFunctionℂ) : ℂ :=
  ∫ ω, Complex.exp (Complex.I * (distributionPairingℂ_real ω J)) ∂dμ_config.toMeasure
```

**Used in**: OS0, OS1, OS2, OS4_Ergodicity.

**Assessment**: `distributionPairingℂ_real` extends the real pairing ⟨ω, f⟩ to complex
test functions via `⟨ω, f⟩_ℂ = ⟨ω, Re(f)⟩ + i⟨ω, Im(f)⟩`. This is ℂ-linear in f
(verify: scaling f by z = a+ib sends Re(zf) = a·Re(f) − b·Im(f) and
Im(zf) = a·Im(f) + b·Re(f), giving z·⟨ω,f⟩_ℂ). It is ℝ-linear in ω (inherited from
WeakDual). This is the unique ℂ-linear extension of the real pairing, which is the
standard construction. **Correct.**

---

## 3. `distributionPairing` — evaluation

**Definition** ([Spacetime/Basic.lean](../OSforGFF/Spacetime/Basic.lean)):
```lean
def distributionPairing (ω : FieldConfiguration) (f : SchwartzTestFunction) : ℝ := ω f
```

**Assessment**: Just the WeakDual evaluation map. No convention choices. **Trivially correct.**

---

## 4. `OS3_ReflectionPositivity` — complex coefficients and test functions

**Definition** ([OS/Axioms.lean](../OSforGFF/OS/Axioms.lean)):
```lean
def OS3_ReflectionPositivity (dμ_config : ProbabilityMeasure FieldConfiguration) : Prop :=
  ∀ (n : ℕ) (f : Fin n → PositiveTimeTestFunctionℂ) (c : Fin n → ℂ),
    0 ≤ (∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
      GJGeneratingFunctionalℂ dμ_config
        ((f i).val - QFT.compTimeReflection ((f j).val))).re
```

**Used in**: SatisfiesAllOS.

**Assessment**: Three points to check.

**(a) Matrix entry `Z_ℂ[fᵢ − Θfⱼ]`**: The standard GJ formulation (p. 90) uses the matrix
M_{ij} = Z[fᵢ − θfⱼ] where fᵢ are supported in {t > 0}. This matches, now using the
complex generating functional `GJGeneratingFunctionalℂ` and complex time reflection
`compTimeReflection`.

**(b) Complex coefficients and test functions**: This formulation now uses complex-valued
test functions (`PositiveTimeTestFunctionℂ = Submodule ℂ SchwartzTestFunctionℂ`) with complex
coefficients (`c : Fin n → ℂ`) and explicit conjugation (`starRingEnd ℂ`). This is the
standard Osterwalder–Schrader formulation (1975, axiom E2) restricted to the 1-particle
sector of the generating functional.

The `OSreconstruction` project (xiyin137/OSreconstruction) uses the full Borchers algebra:
```lean
E2_reflection_positive : ∀ (F : BorchersSequence d),
    (∀ n, ∀ x : NPointDomain d n, (F.funcs n).toFun x ≠ 0 → x ∈ PositiveTimeRegion d n) →
    (OSInnerProduct d S F F).re ≥ 0
```

| Aspect | OSforGFF (this project) | OSreconstruction (standard) |
|--------|------------------------|-----------------------------|
| Test functions | Complex-valued, 1-particle | Complex-valued, n-particle (Borchers) |
| Coefficients | Complex `c : Fin n → ℂ` | Implicit in complex test functions |
| Involution | `compTimeReflection` (Θf) | `osConj` = time-reflect + conjugate |
| Inner product | `Re(∑ c̄ᵢcⱼ Z_ℂ[fᵢ − Θfⱼ])` | `Re(∑ S_{m+n}(f̄_m^θ ⊗ f_n))` |

The real-coefficient version is retained as `OS3_ReflectionPositivity_real` for
compatibility and as a stepping stone in the GFF proof.

**(c) `compTimeReflection`**: This is the complex version `(Θf)(x) = f(Θx) = f(−t, x̄)`
acting on complex-valued test functions. It is an ℝ-linear (not ℂ-linear) map on
`SchwartzTestFunctionℂ`. For the OS star operation f★ = conj(Θf), complex conjugation is
handled separately via `starRingEnd ℂ` in the coefficients.  **Correct.**

---

## 5. `QFT.timeReflection` — negates time coordinate

**Definition** ([Spacetime/DiscreteSymmetry.lean](../OSforGFF/Spacetime/DiscreteSymmetry.lean)):
```lean
abbrev timeReflection (x : SpaceTime) : SpaceTime :=
  (WithLp.equiv 2 _).symm (Function.update x.ofLp 0 (-x.ofLp 0))
```

**Assessment**: `Function.update x 0 (−x₀)` replaces coordinate 0 with its negation,
leaving the spatial coordinates 1,…,d−1 unchanged. This gives (t, x̄) ↦ (−t, x̄). The time coordinate
is index 0 throughout the project (`getTimeComponent x = x ⟨0, _⟩` in Basic.lean,
`timeIndex = ⟨0, _⟩` in TimeTranslation.lean). **Correct and consistent.**

---

## 6. `QFT.euclidean_action` — pullback by inverse

**Definition** ([Spacetime/Euclidean.lean](../OSforGFF/Spacetime/Euclidean.lean)):
```lean
noncomputable def euclidean_action (g : E) (f : SchwartzTestFunctionℂ) : SchwartzTestFunctionℂ :=
  SchwartzMap.compCLM ... f    -- composes f with euclidean_pullback g = act g⁻¹
```

The inverse of `g = ⟨R, t⟩` is `g⁻¹ = ⟨R⁻¹, −R⁻¹t⟩` (Euclidean.lean).

**Verification**: act(g⁻¹, act(g, x)) = R⁻¹(Rx + t) + (−R⁻¹t) = x + R⁻¹t − R⁻¹t = x. ✓

The group action `(g·f)(x) = f(g⁻¹x)` is the standard left-action by pullback,
ensuring `(gh)·f = g·(h·f)`. This is standard in the OS literature. **Correct.**

---

## 7. `QFT.E` — Euclidean group structure

**Definition** ([Spacetime/Euclidean.lean](../OSforGFF/Spacetime/Euclidean.lean)):
```lean
structure E (d : ℕ) where
  R : O d         -- O d = LinearIsometry ℝ (SpaceTime d) (SpaceTime d)
  t : SpaceTime d

instance : Mul (E d) where
  mul g h := ⟨g.R.comp h.R, g.R h.t + g.t⟩
```

**Assessment**: Multiplication is (R₁, t₁)·(R₂, t₂) = (R₁R₂, R₁t₂ + t₁), the
standard semidirect product ℝ^d ⋊ O(d). The group axioms (associativity, identity,
inverse) are all proved in Lean. **Correct.**

---

## 8. `OS4_Clustering` — translation direction

**Definition** ([OS/Axioms.lean](../OSforGFF/OS/Axioms.lean)):
```lean
def OS4_Clustering (dμ_config : ProbabilityMeasure FieldConfiguration) : Prop :=
  ∀ (f g : SchwartzTestFunction) (ε : ℝ), ε > 0 → ∃ (R : ℝ), R > 0 ∧ ∀ (a : SpaceTime),
    ‖a‖ > R →
    ‖GJGeneratingFunctional dμ_config (f + g.translate a) -
     GJGeneratingFunctional dμ_config f * GJGeneratingFunctional dμ_config g‖ < ε
```

**Assessment**: The clustering condition quantifies over all `a : SpaceTime` with
`‖a‖ > R`, i.e., separation in *any* spacetime direction, not just time. This is
potentially stronger than the time-only version in some references. However, given
OS2 (Euclidean invariance), the measure is invariant under rotations mixing time and
space, so clustering in any single direction implies clustering in all directions at the
same rate. The two formulations are therefore **equivalent given OS2**, and using all
directions is cleaner. **Correct.**

`SchwartzMap.translate` is defined as `f.translate a x = f (x − a)` (General/FunctionalAnalysis.lean),
which is standard: translating the function by +a means evaluating at x − a. **Correct.**

---

## 9. `OS4_Ergodicity` — observable class and convergence

**Definition** ([OS/Axioms.lean](../OSforGFF/OS/Axioms.lean)):
```lean
def OS4_Ergodicity (dμ_config : ProbabilityMeasure FieldConfiguration) : Prop :=
  ∀ (n : ℕ) (z : Fin n → ℂ) (f : Fin n → SchwartzTestFunctionℂ),
    let μ := dμ_config.toMeasure
    let A : FieldConfiguration → ℂ := fun ω =>
      ∑ j, z j * Complex.exp (distributionPairingℂ_real ω (f j))
    Filter.Tendsto
      (fun T : ℝ =>
        ∫ ω, ‖(1 / T) * ∫ s in Set.Icc (0 : ℝ) T,
          A (TimeTranslation.timeTranslationDistribution s ω)
          - ∫ ω', A ω' ∂μ‖^2 ∂μ)
      Filter.atTop (nhds 0)
```

**Assessment**: The observable A(ω) = ∑ zⱼ exp(⟨ω, fⱼ⟩_ℂ) is a finite linear combination
of exponential functionals — these span a dense subset of L²(μ) (via Stone–Weierstrass–type
arguments), so ergodicity for this class implies ergodicity in general.

The convergence is ∫ ‖time-average − space-average‖² dμ → 0, i.e., L²(μ) convergence
of the Cesàro mean to the ensemble mean. The normalization `1/T` with `Icc 0 T`
(averaging over [0,T]) is standard. This matches GJ's formulation. **Correct.**

`timeTranslationDistribution s ω = ω ∘ T_{−s}` (Spacetime/TimeTranslation.lean), giving
⟨T_s ω, f⟩ = ⟨ω, T_{−s}f⟩ = ⟨ω, f(· − se₀)⟩, which shifts by time s via duality.
The sign convention (positive s = forward time) is correct.
**Correct.**

---

## 10. `PositiveTimeTestFunction` — support condition

**Definition** ([Spacetime/PositiveTimeTestFunction.lean](../OSforGFF/Spacetime/PositiveTimeTestFunction.lean)):
```lean
def PositiveTimeTestFunctions.submodule : Submodule ℝ SchwartzTestFunction where
  carrier := { f : SchwartzTestFunction | tsupport f ⊆ positiveTimeSet }
```

where `positiveTimeSet = {x | getTimeComponent x > 0}` is open.

**Assessment**: `tsupport f = closure(support f)` ⊆ {t > 0} (open) means f and all its
derivatives vanish in a neighborhood of {t = 0}. This is the correct and standard
requirement: test functions must be supported strictly away from the time-zero hyperplane.
Using `tsupport` rather than `support` is the proper Lean/Mathlib convention for
Schwartz functions, and the two are equivalent here since {t > 0} is open (closure of
support inside an open set implies support inside that set). **Correct.**

---

## 11. `OS0_Analyticity`

**Definition** ([OS/Axioms.lean](../OSforGFF/OS/Axioms.lean)):
```lean
def OS0_Analyticity (dμ_config : ProbabilityMeasure FieldConfiguration) : Prop :=
  ∀ (n : ℕ) (J : Fin n → SchwartzTestFunctionℂ),
    AnalyticOn ℂ (fun z : Fin n → ℂ =>
      GJGeneratingFunctionalℂ dμ_config (∑ i, z i • J i)) Set.univ
```

**Assessment**: For any finite collection J₁,...,Jₙ of complex test functions, the map
z ↦ Z[∑ zᵢJᵢ] is analytic on all of ℂⁿ (entire). This is the standard OS0 axiom:
the generating functional is analytic when restricted to finite-dimensional complex
subspaces of the test function space. **Correct.**

---

## 12. `OS1_Regularity`

**Definition** ([OS/Axioms.lean](../OSforGFF/OS/Axioms.lean)):
```lean
def OS1_Regularity (dμ_config : ProbabilityMeasure FieldConfiguration) : Prop :=
  ∃ (p : ℝ) (c : ℝ), 1 ≤ p ∧ p ≤ 2 ∧ c > 0 ∧
    (∀ (f : SchwartzTestFunctionℂ),
      ‖GJGeneratingFunctionalℂ dμ_config f‖ ≤
        Real.exp (c * (∫ x, ‖f x‖ ∂volume + ∫ x, ‖f x‖^p ∂volume))) ∧
    (p = 2 → TwoPointIntegrable dμ_config)
```

**Assessment**: The bound ‖Z[f]‖ ≤ exp(c·(‖f‖_L¹ + ‖f‖_Lp^p)) for some 1 ≤ p ≤ 2
encodes temperedness: Z extends continuously to Lp. The subsidiary condition
(p = 2 ⟹ local integrability of S₂) matches the GJ statement. **Correct.**

---

## 13. `OS2_EuclideanInvariance`

**Definition** ([OS/Axioms.lean](../OSforGFF/OS/Axioms.lean)):
```lean
def OS2_EuclideanInvariance (dμ_config : ProbabilityMeasure FieldConfiguration) : Prop :=
  ∀ (g : QFT.E) (f : SchwartzTestFunctionℂ),
    GJGeneratingFunctionalℂ dμ_config f =
    GJGeneratingFunctionalℂ dμ_config (QFT.euclidean_action g f)
```

**Assessment**: Z[f] = Z[g·f] for all g ∈ E(d) and all complex test functions f. This is
the standard formulation of Euclidean invariance for the generating functional. **Correct.**

---

## Summary

| # | Definition | Verdict |
|---|-----------|---------|
| 1 | `GJGeneratingFunctional` (sign of i) | ✓ Correct, matches GJ |
| 2 | `distributionPairingℂ_real` (ℂ-linearity) | ✓ Correct, unique ℂ-linear extension |
| 3 | `distributionPairing` (evaluation) | ✓ Trivially correct |
| 4 | `OS3_ReflectionPositivity` (complex coeff + test fns) | ✓ Correct. Now uses complex test functions (`PositiveTimeTestFunctionℂ`), complex coefficients with conjugation (`starRingEnd`), and the complex generating functional (`GJGeneratingFunctionalℂ`). Compatible with OS reconstruction. Real version retained as `OS3_ReflectionPositivity_real`. |
| 5 | `timeReflection` (negates coord 0) | ✓ Correct and consistent |
| 6 | `euclidean_action` (pullback by g⁻¹) | ✓ Correct, standard left-action |
| 7 | `QFT.E` (semidirect product) | ✓ Correct group structure, proved in Lean |
| 8 | `OS4_Clustering` (all directions) | ✓ Equivalent to time-only given OS2 |
| 9 | `OS4_Ergodicity` (observable class) | ✓ Correct, dense observable class |
| 10 | `PositiveTimeTestFunction` (tsupport) | ✓ Correct, standard support condition |
| 11 | `OS0_Analyticity` (entire on ℂⁿ) | ✓ Standard OS0 |
| 12 | `OS1_Regularity` (Lp bound) | ✓ Standard OS1 with subsidiary condition |
| 13 | `OS2_EuclideanInvariance` (Z[f] = Z[g·f]) | ✓ Standard OS2 |

**Note on OS3**: Item 4 now uses the standard complex formulation with complex-valued
test functions and complex coefficients, compatible with OS reconstruction. The real
version is retained as `OS3_ReflectionPositivity_real`. The proof that the GFF satisfies
the complex OS3 currently uses the analytic continuation of the real characteristic
function formula (see `gff_complexOS3_matrix` in `OS3_ReflectionPositivity.lean`).
