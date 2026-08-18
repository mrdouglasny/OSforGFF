# The registry Challenge: design and dictionary

`Challenge.lean` restates the library's headline result — *the free Gaussian Free Field
exists and satisfies the Osterwalder–Schrader axioms in every dimension `d ≥ 2`* — in a form
auditable **without trusting or reading this library**: its transitive imports are Mathlib
only. `Solution.lean` proves it from the library. This document explains the design choices
and tabulates the dictionary between the Challenge's self-contained definitions and the
library's originals.

## The statement

```lean
theorem Challenge.gaussianFreeField_satisfies_OS_axioms
    (d : ℕ) [Fact (2 ≤ d)] (m : ℝ) (hm : 0 < m) :
    ∃ μ : ProbabilityMeasure (FieldConfiguration d),
      (∀ f : TestFunction d,
        GJGeneratingFunctional μ f =
          Complex.exp (-(1 / 2 : ℂ) * ((covarianceForm d m f f : ℝ) : ℂ))) ∧
      OS0_Analyticity μ ∧ OS1_Regularity μ ∧ OS2_EuclideanInvariance μ ∧
      OS3_ReflectionPositivity μ ∧ OS4_Clustering μ ∧ OS4_Ergodicity μ
```

**Why existential + characterization.** The library states its theorem about a *named*
measure, `gaussianFreeField_free`, whose construction goes through the Minlos theorem
(external `bochner` library) and therefore cannot appear in a Mathlib-only file. The
Challenge instead asserts the existence of a measure **together with the property that
determines it uniquely**: its generating functional is the Gaussian
`Z[f] = exp(−½⟨f, C f⟩)`. This clause is essential — a bare "there exists a measure
satisfying OS0–OS4" would be discharged by the Dirac measure at `0` (for which `Z ≡ 1`).
With it, the statement is exactly "the free field with covariance `(−Δ + m²)⁻¹` exists and
satisfies the OS axioms": a Gaussian probability measure on `S'(ℝ^d)` is determined by its
characteristic functional.

**Why the proper-time covariance.** The free covariance is presented by its Schwinger
(heat-kernel) integral

```
C(x, y) = ∫₀^∞ e^{−t m²} (4πt)^{−d/2} e^{−‖x−y‖²/(4t)} dt ,
```

an elementary closed formula requiring no operator theory, valid uniformly in the dimension.
It matches the library's canonical propagator `GFFPropagator.ofProperTime`
(`OSforGFF/Covariance/Propagator.lean`), for which the identification is definitional — so
the Solution's characterization clause is exactly the library lemma
`gff_real_characteristic`.

**Hypotheses.** `2 ≤ d` is carried as a `Fact` instance because the positive-time apparatus
of OS3 (the time coordinate `x₀`) consumes it through instances; `0 < m` is a plain
hypothesis. Neither weakens the statement: both are the standard hypotheses of the theory
(`d ≥ 2` for a time/space split, `m > 0` for a mass gap).

## Verification workflow

- `lake build Challenge Solution` — builds both root modules; `Challenge` reports exactly
  one `sorry` (the hole), `Solution` is clean.
- `diff Challenge.lean Solution.lean` — the files agree except for the import line, the
  module docstring, and the proof.
- `comparator.json` — drives the Comparator: identical statement, only
  `propext`/`Classical.choice`/`Quot.sound`, kernel replay.
- `scripts/check-guardrails.sh` — additionally gates the pair at source level (no axioms or
  escape hatches; exactly one `sorry`, in `Challenge.lean`).

## Dictionary

Every Challenge definition is a copy of a library definition (the embedded *proofs* may
differ — by proof irrelevance only the data must agree). The table gives the corresponding
library declaration and file.

### Spacetime, test functions, field configurations

| Challenge (`Challenge.*`) | Library | File |
|---|---|---|
| `SpaceTime` | `SpaceTime` | `OSforGFF/Spacetime/Basic.lean` |
| `TestFunction`, `TestFunctionℂ` | `TestFunction`, `TestFunctionℂ` | `OSforGFF/Spacetime/Basic.lean` |
| `FieldConfiguration` | `FieldConfiguration` | `OSforGFF/Spacetime/Basic.lean` |
| `measurableSpaceWeakDual` (cylinder σ-algebra) | `instance : MeasurableSpace (WeakDual ℝ E)` | `bochner`: `Minlos/NuclearSpace.lean` |
| `NeZero` instance, `getTimeComponent` | same | `OSforGFF/Spacetime/Basic.lean` |

The cylinder σ-algebra `⨆ f, (borel ℝ).comap (ω ↦ ω f)` is the one definition whose
original lives in an external dependency; it is copied verbatim so that the Challenge's
`ProbabilityMeasure (FieldConfiguration d)` is definitionally the library's.

### Pairings and generating functionals

| Challenge | Library | File |
|---|---|---|
| `distributionPairing` | `distributionPairing` | `OSforGFF/Spacetime/Basic.lean` |
| `GJGeneratingFunctional`, `GJGeneratingFunctionalℂ` | same | `OSforGFF/Spacetime/Basic.lean` |
| `schwartz_comp_clm`, `complex_testfunction_decompose`, `distributionPairingℂ_real` | same | `OSforGFF/Spacetime/Basic.lean` |

### The free covariance

| Challenge | Library | File |
|---|---|---|
| `heatKernelProfile` | `heatKernelProfile` | `OSforGFF/Covariance/Propagator.lean` |
| `properTimeCovariance` | `properTimeCovariance` | `OSforGFF/Covariance/Propagator.lean` |
| `freeCovariance d m x y` | `freeCovariance d m x y` with `Cprofile := GFFPropagator.ofProperTime` | `OSforGFF/Covariance/Propagator.lean` |
| `covarianceForm` | `QFT.freeCovarianceFormR` | `OSforGFF/Covariance/RealForm.lean` |

### Schwinger functions and the two-point function (OS1)

| Challenge | Library | File |
|---|---|---|
| `SchwingerFunction`, `SchwingerFunction₂` | same | `OSforGFF/Schwinger/Defs.lean` |
| `translateSchwartz` | `translateSchwartz` (= `SchwartzMap.translate`) | `OSforGFF/Schwinger/TwoPoint.lean`, `OSforGFF/General/FunctionalAnalysis.lean` |
| `bumpToSchwartz`, `SmearedTwoPointFunction`, `standardBumpSequence`, `SchwingerTwoPointFunction` | same | `OSforGFF/Schwinger/TwoPoint.lean` |

### Euclidean group (OS2)

| Challenge | Library | File |
|---|---|---|
| `Rotation` | `QFT.O4` | `OSforGFF/Spacetime/Euclidean.lean` |
| `E`, `act` | `QFT.E`, `QFT.act` | `OSforGFF/Spacetime/Euclidean.lean` |
| `Rotation.inv`, `Inv (E d)` instance | `LinearIsometry.inv`, `Inv (E d)` instance | `OSforGFF/Spacetime/Euclidean.lean` |
| `euclidean_pullback` + growth lemmas | `QFT.euclidean_pullback` + growth lemmas | `OSforGFF/Spacetime/Euclidean.lean` |
| `euclidean_action` | `QFT.euclidean_action` | `OSforGFF/Spacetime/Euclidean.lean` |

`Challenge.E d` is a distinct structure type from `QFT.E d`; the Solution bridges them by
the component mapping `g ↦ ⟨g.R, g.t⟩` (the rotation type `Rotation d = QFT.O4 d` is the
same Mathlib `LinearIsometry`, so only the wrapper differs).

### Time reflection, star operation, positive time (OS3)

| Challenge | Library | File |
|---|---|---|
| `timeReflection`, `timeReflectionLinear`, `timeReflectionCLM`, `timeReflectionLE` | `QFT.timeReflection` etc. | `OSforGFF/Spacetime/DiscreteSymmetry.lean` |
| `compTimeReflection` | `QFT.compTimeReflection` | `OSforGFF/Spacetime/DiscreteSymmetry.lean` |
| `starTestFunction`, `Star (TestFunctionℂ d)` instance | same | `OSforGFF/Spacetime/PositiveTimeTestFunction.lean` |
| `HasPositiveTime`, `positiveTimeSet`, `PositiveTimeTestFunctionsℂ.submodule`, `PositiveTimeTestFunctionℂ` | same | `OSforGFF/Spacetime/PositiveTimeTestFunction.lean` |

One deliberate formulation difference: the Challenge builds `compTimeReflection` as
`SchwartzMap.compCLMOfAntilipschitz` applied to the *raw* map `timeReflection` (which is an
isometry), where the library uses `SchwartzMap.compCLM` applied to the coercion
`⇑timeReflectionCLM`. The two are definitionally equal (`compCLMOfAntilipschitz` reduces to
`compCLM`, and `timeReflection = ⇑timeReflectionCLM` holds by `rfl`); the Solution's proof
crosses this boundary silently.

### Time translations (OS4 ergodicity)

| Challenge | Library | File |
|---|---|---|
| `timeShift` + isometry/growth lemmas | `TimeTranslation.timeShift` etc. | `OSforGFF/Spacetime/TimeTranslation.lean` |
| `timeTranslationSchwartzCLM` | `TimeTranslation.timeTranslationSchwartzCLM` | `OSforGFF/Spacetime/TimeTranslation.lean` |
| `timeTranslationDistribution` | `TimeTranslation.timeTranslationDistribution` | `OSforGFF/Spacetime/TimeTranslation.lean` |

### The OS axioms

| Challenge | Library | File |
|---|---|---|
| `OS0_Analyticity` | `OS0_Analyticity` | `OSforGFF/OS/Axioms.lean` |
| `TwoPointIntegrable`, `OS1_Regularity` | same | `OSforGFF/OS/Axioms.lean` |
| `OS2_EuclideanInvariance` | `OS2_EuclideanInvariance` | `OSforGFF/OS/Axioms.lean` |
| `OS3_ReflectionPositivity` | `OS3_ReflectionPositivity` | `OSforGFF/OS/Axioms.lean` |
| `OS4_Clustering` | `OS4_Clustering` | `OSforGFF/OS/Axioms.lean` |
| `OS4_Ergodicity` | `OS4_Ergodicity` | `OSforGFF/OS/Axioms.lean` |

### The theorem

| Challenge | Proved from | File |
|---|---|---|
| `gaussianFreeField_satisfies_OS_axioms` | `OSforGFF.gaussianFreeField_satisfies_all_OS_axioms_generic` under `GFFPropagator.ofProperTime`, with `gff_real_characteristic` for the characterization clause | `OSforGFF/OS/Master.lean`, `OSforGFF/Measure/Construct.lean` |

The witness is the library's Minlos-constructed measure `gaussianFreeField_free`
(`OSforGFF/Measure/Construct.lean`); the five OS conjuncts are the fields of the master
theorem, with only two adaptors: the Euclidean component mapping (OS2) and the
positive-time subtype mapping (OS3).

## Known divergences from the sources

As in the library (see `formalization.yaml`, `fidelity`): the axioms are stated in the
Glimm–Jaffe probability-measure formulation rather than for Schwinger functions; OS3 is the
complex star formulation (Osterwalder–Schrader 1975, axiom E2); OS4 is split into
clustering and ergodicity. The Challenge restates these verbatim, adding only the
existential packaging described above.
