# `Master.lean` — Informal Summary

> **Source**: [`OSforGFF/OS/Master.lean`](../../OSforGFF/OS/Master.lean)
> **Generated**: 2026-07-05 (regenerated from current source)

## Overview

This is the headline file: it assembles the six Osterwalder–Schrader components
(OS0 analyticity, OS1 regularity, OS2 Euclidean invariance, OS3 reflection positivity,
OS4 clustering, OS4 ergodicity) into a single
[`SatisfiesAllOS`](../../OSforGFF/OS/Axioms.lean#L195) verdict for the free Gaussian Free
Field measure. The central result is the **dimension-generic** master theorem
`gaussianFreeField_satisfies_all_OS_axioms_generic`, valid for any spacetime dimension with
`{d : ℕ} [Fact (2 ≤ d)]` equipped with a `[GFFPropagator d m]` instance and
mass `m > 0`. From it the file derives an **all-dimensions corollary**
`gaussianFreeField_satisfies_all_OS_axioms_of_dim` (every `d ≥ 2`, supplying the canonical
[`GFFPropagator.ofProperTime`](../../OSforGFF/Covariance/Propagator.lean) instance so no per-`d`
closed form is required), and **four concrete instances** at the literal dimensions `d = 4, 3, 2, 5`,
each stated as `SatisfiesAllOS (μ_GFF n m)` for the single unified measure
[`μ_GFF d`](../../OSforGFF/Measure/Construct.lean). The file declares no
definitions and no axioms; each theorem is a thin assembly of results proven in the `OS/` submodules.

## Status

**Main result**: Fully proven (0 sorries; `grep` for `sorry`/`admit` finds none).

**Length**: 119 lines, 0 definitions + 6 theorems/lemmas

---

### [`gaussianFreeField_satisfies_all_OS_axioms_generic`](../../OSforGFF/OS/Master.lean#L61) — Theorem

**Lean signature**
```lean
theorem gaussianFreeField_satisfies_all_OS_axioms_generic
    {d : ℕ} [Fact (2 ≤ d)] (m : ℝ) [Fact (0 < m)] [GFFPropagator d m] :
    SatisfiesAllOS (gaussianFreeField_free (d := d) m)
```

**Statement**: The dimension-generic master theorem. For any spacetime dimension $d \ge 2$,
mass $m > 0$, and a `GFFPropagator d m` instance (the closed-form radial
covariance identified with the proper-time integral), the free GFF measure
`gaussianFreeField_free (d := d) m` satisfies **all** Osterwalder–Schrader axioms:
$$\mathrm{SatisfiesAllOS}\bigl(\mathrm{gaussianFreeField\_free}\ (d := d)\ m\bigr).$$

**Informal**: Builds the `SatisfiesAllOS` structure field-by-field
(`os0, os1, os2, os3, os4_clustering, os4_ergodicity`).

**Proof uses**: OS0 [`QFT.gaussianFreeField_satisfies_OS0`](../../OSforGFF/OS/OS0_Analyticity.lean)
(holomorphic integral / differentiation under the integral);
OS1 [`gaussianFreeField_satisfies_OS1`](../../OSforGFF/OS/OS1_Regularity.lean)
(Fourier/momentum-space methods);
OS2 [`gaussian_satisfies_OS2`](../../OSforGFF/Measure/GaussianFreeField.lean) with
[`isGaussianGJ_gaussianFreeField_free`](../../OSforGFF/Measure/IsGaussian.lean) and
[`QFT.CovarianceEuclideanInvariantℂ_μ_GFF`](../../OSforGFF/OS/OS2_Invariance.lean);
OS3 [`QFT.gaussianFreeField_OS3`](../../OSforGFF/OS/OS3_ReflectionPositivity.lean)
(Schur–Hadamard, complex star formulation);
OS4 clustering [`QFT.gaussianFreeField_satisfies_OS4`](../../OSforGFF/OS/OS4_Clustering.lean)
(Gaussian factorization and covariance decay);
OS4 ergodicity [`OS4_Ergodicity.OS4_PolynomialClustering_implies_OS4_Ergodicity`](../../OSforGFF/OS/OS4_Ergodicity.lean)
fed by [`QFT.gaussianFreeField_satisfies_OS4_PolynomialClustering`](../../OSforGFF/OS/OS4_Clustering.lean)
at $\alpha = 6$.

---

### [`gaussianFreeField_satisfies_all_OS_axioms_of_dim`](../../OSforGFF/OS/Master.lean#L80) — Theorem

**Lean signature**
```lean
theorem gaussianFreeField_satisfies_all_OS_axioms_of_dim (d : ℕ) [Fact (2 ≤ d)]
    (m : ℝ) [Fact (0 < m)] :
    letI := GFFPropagator.ofProperTime d m
    SatisfiesAllOS (gaussianFreeField_free (d := d) m)
```

**Statement**: All-dimensions corollary. For **every** $d \ge 2$ and mass $m > 0$, the free
GFF built from the canonical proper-time propagator satisfies all Osterwalder–Schrader axioms:
$$\text{with } \mathrm{GFFPropagator.ofProperTime}\ d\ m,\quad
\mathrm{SatisfiesAllOS}\bigl(\mathrm{gaussianFreeField\_free}\ (d := d)\ m\bigr).$$

**Informal**: Drops the `[GFFPropagator d m]` hypothesis of the generic theorem by supplying the
canonical instance [`GFFPropagator.ofProperTime`](../../OSforGFF/Covariance/Propagator.lean) via
`letI`, so no per-`d` closed form is needed (the concrete instances additionally exhibit the
covariance in closed form).

**Proof uses**: [`GFFPropagator.ofProperTime`](../../OSforGFF/Covariance/Propagator.lean),
[`gaussianFreeField_satisfies_all_OS_axioms_generic`](../../OSforGFF/OS/Master.lean#L61).

---

### [`gaussianFreeField_satisfies_all_OS_axioms_dim4`](../../OSforGFF/OS/Master.lean#L106) — Theorem

**Lean signature**
```lean
theorem gaussianFreeField_satisfies_all_OS_axioms_dim4 (m : ℝ) [Fact (0 < m)] :
    SatisfiesAllOS (μ_GFF 4 m)
```

**Statement**: Four-dimensional instance. An unconditional theorem — no assumptions beyond
$m > 0$ — that the free GFF in dimension `4` satisfies all OS axioms:
$$\mathrm{SatisfiesAllOS}(\mu_{\mathrm{GFF}}\ 4\ m).$$

**Informal**: The `d = 4` specialization, obtained by applying the generic master theorem at the
literal dimension `4`; the instances `[Fact (2 ≤ 4)]` and `GFFPropagator 4 m`
are synthesized by typeclass search.

**Proof uses**: [`gaussianFreeField_satisfies_all_OS_axioms_generic`](../../OSforGFF/OS/Master.lean#L61),
[`μ_GFF`](../../OSforGFF/Measure/Construct.lean).

---

### [`gaussianFreeField_satisfies_all_OS_axioms_dim3`](../../OSforGFF/OS/Master.lean#L97) — Theorem

**Lean signature**
```lean
theorem gaussianFreeField_satisfies_all_OS_axioms_dim3 (m : ℝ) [Fact (0 < m)] :
    SatisfiesAllOS (μ_GFF 3 m)
```

**Statement**: Three-dimensional instance. The free GFF with the Yukawa covariance
$e^{-mr}/(4\pi r)$ satisfies all OS axioms:
$$\mathrm{SatisfiesAllOS}(\mu_{\mathrm{GFF}}\ 3\ m).$$

**Informal**: The `d = 3` specialization of the generic master theorem.

**Proof uses**: [`gaussianFreeField_satisfies_all_OS_axioms_generic`](../../OSforGFF/OS/Master.lean#L61),
[`μ_GFF`](../../OSforGFF/Measure/Construct.lean).

---

### [`gaussianFreeField_satisfies_all_OS_axioms_dim2`](../../OSforGFF/OS/Master.lean#L90) — Theorem

**Lean signature**
```lean
theorem gaussianFreeField_satisfies_all_OS_axioms_dim2 (m : ℝ) [Fact (0 < m)] :
    SatisfiesAllOS (μ_GFF 2 m)
```

**Statement**: Two-dimensional instance. The free GFF with the Bessel covariance
$K_0(mr)/(2\pi)$ satisfies all OS axioms:
$$\mathrm{SatisfiesAllOS}(\mu_{\mathrm{GFF}}\ 2\ m).$$

**Informal**: The `d = 2` specialization of the generic master theorem.

**Proof uses**: [`gaussianFreeField_satisfies_all_OS_axioms_generic`](../../OSforGFF/OS/Master.lean#L61),
[`μ_GFF`](../../OSforGFF/Measure/Construct.lean).

---

### [`gaussianFreeField_satisfies_all_OS_axioms_dim5`](../../OSforGFF/OS/Master.lean#L113) — Theorem

**Lean signature**
```lean
theorem gaussianFreeField_satisfies_all_OS_axioms_dim5 (m : ℝ) [Fact (0 < m)] :
    SatisfiesAllOS (μ_GFF 5 m)
```

**Statement**: Five-dimensional instance. The free GFF with the $K_{3/2}$ covariance
$(1 + mr)\, e^{-mr}/(8\pi^2 r^3)$ satisfies all OS axioms:
$$\mathrm{SatisfiesAllOS}(\mu_{\mathrm{GFF}}\ 5\ m).$$

**Informal**: The `d = 5` specialization of the generic master theorem.

**Proof uses**: [`gaussianFreeField_satisfies_all_OS_axioms_generic`](../../OSforGFF/OS/Master.lean#L61),
[`μ_GFF`](../../OSforGFF/Measure/Construct.lean).

---

*This file has **0** definitions and **6** theorems/lemmas (0 with sorry).*
