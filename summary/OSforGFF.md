# `OSforGFF.lean` — Informal Summary

> **Source**: [`OSforGFF.lean`](../OSforGFF.lean)
> **Generated**: 2026-07-05 (regenerated from current source)

## Overview

Root import aggregator for the `OSforGFF` library. It contains no declarations of its own;
it simply `import`s every on-graph module of the library in dependency order, so that building
this file (the package's `@[default_target]` `lean_lib`) builds the whole development. The six
off-graph `Legacy/` modules (`BesselK1Analytics`, `Dim4Bessel`, and the four `Unused*` files)
are deliberately **not** imported here — they preserve superseded proven mathematics and are
verified in isolation with `lake env lean`. `OS/NonTrivial.lean` is likewise off-graph but
live (non-degeneracy results), compiled by `scripts/check-guardrails.sh`.

## Status

**Main result**: N/A — import-only root module (no definitions or theorems).

**Length**: 76 lines, 0 definition(s) + 0 theorem(s)/lemma(s).

---

## Imported modules (source order)

**General mathematics** — pure Mathlib extensions, no project imports:
[`FunctionalAnalysis`](../OSforGFF/General/FunctionalAnalysis.lean),
[`SchurProduct`](../OSforGFF/General/SchurProduct.lean),
[`HadamardExp`](../OSforGFF/General/HadamardExp.lean),
[`PositiveDefinite`](../OSforGFF/General/PositiveDefinite.lean),
[`GaussianRBF`](../OSforGFF/General/GaussianRBF.lean),
[`FourierTransforms`](../OSforGFF/General/FourierTransforms.lean),
[`LaplaceIntegral`](../OSforGFF/General/LaplaceIntegral.lean),
[`BesselFunction`](../OSforGFF/General/BesselFunction.lean),
[`BesselK0`](../OSforGFF/General/BesselK0.lean),
[`BesselK`](../OSforGFF/General/BesselK.lean),
[`QuantitativeDecay`](../OSforGFF/General/QuantitativeDecay.lean),
[`SchwartzTranslationDecay`](../OSforGFF/General/SchwartzTranslationDecay.lean),
[`L2TimeIntegral`](../OSforGFF/General/L2TimeIntegral.lean).

**Spacetime** — test functions & symmetries:
[`Basic`](../OSforGFF/Spacetime/Basic.lean),
[`Euclidean`](../OSforGFF/Spacetime/Euclidean.lean),
[`DiscreteSymmetry`](../OSforGFF/Spacetime/DiscreteSymmetry.lean),
[`Decomposition`](../OSforGFF/Spacetime/Decomposition.lean),
[`ComplexTestFunction`](../OSforGFF/Spacetime/ComplexTestFunction.lean),
[`PositiveTimeTestFunction`](../OSforGFF/Spacetime/PositiveTimeTestFunction.lean),
[`TimeTranslation`](../OSforGFF/Spacetime/TimeTranslation.lean),
[`ProdIntegrable`](../OSforGFF/Spacetime/ProdIntegrable.lean),
[`Tonelli`](../OSforGFF/Spacetime/Tonelli.lean).

**Schwinger** — generating functionals:
[`Defs`](../OSforGFF/Schwinger/Defs.lean),
[`TwoPoint`](../OSforGFF/Schwinger/TwoPoint.lean),
[`GaussianMoments`](../OSforGFF/Schwinger/GaussianMoments.lean).

**Covariance & instances** — free propagator and its per-dimension `GFFPropagator` instances:
[`Covariance/Propagator`](../OSforGFF/Covariance/Propagator.lean),
[`Covariance/ParsevalGeneric`](../OSforGFF/Covariance/ParsevalGeneric.lean),
[`Instances/Dim4`](../OSforGFF/Instances/Dim4.lean),
[`Instances/Dim3`](../OSforGFF/Instances/Dim3.lean),
[`Instances/Dim2`](../OSforGFF/Instances/Dim2.lean),
[`Instances/Dim5`](../OSforGFF/Instances/Dim5.lean),
[`Covariance/RealForm`](../OSforGFF/Covariance/RealForm.lean).

**Measure** — Minlos construction of the GFF:
[`NuclearSpace`](../OSforGFF/Measure/NuclearSpace.lean),
[`Minlos`](../OSforGFF/Measure/Minlos.lean),
[`MinlosAnalytic`](../OSforGFF/Measure/MinlosAnalytic.lean),
[`Construct`](../OSforGFF/Measure/Construct.lean),
[`IsGaussian`](../OSforGFF/Measure/IsGaussian.lean),
[`GaussianFreeField`](../OSforGFF/Measure/GaussianFreeField.lean).

**OS axioms** — definitions and proofs:
[`Axioms`](../OSforGFF/OS/Axioms.lean),
[`OS0_Analyticity`](../OSforGFF/OS/OS0_Analyticity.lean),
[`OS1_Regularity`](../OSforGFF/OS/OS1_Regularity.lean),
[`OS2_Invariance`](../OSforGFF/OS/OS2_Invariance.lean),
[`OS3_MixedRepInfra`](../OSforGFF/OS/OS3_MixedRepInfra.lean),
[`OS3_MixedRep`](../OSforGFF/OS/OS3_MixedRep.lean),
[`OS3_CovarianceRP`](../OSforGFF/OS/OS3_CovarianceRP.lean),
[`OS3_ReflectionPositivity`](../OSforGFF/OS/OS3_ReflectionPositivity.lean),
[`OS4_MGF`](../OSforGFF/OS/OS4_MGF.lean),
[`OS4_Clustering`](../OSforGFF/OS/OS4_Clustering.lean),
[`OS4_Ergodicity`](../OSforGFF/OS/OS4_Ergodicity.lean).

**Master theorem**: [`OS/Master`](../OSforGFF/OS/Master.lean).

**Build-enforced guardrails** (axiom-footprint + statement-type): [`Guardrails`](../OSforGFF/Guardrails.lean).

---

*This file declares no definitions or theorems; it is the library root that transitively imports all on-graph modules (0 with sorry).*
