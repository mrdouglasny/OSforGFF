# `BesselK0.lean` — Informal Summary

> **Source**: [`OSforGFF/General/BesselK0.lean`](../../../OSforGFF/General/BesselK0.lean)
> **Generated**: 2026-07-05 (regenerated from current source)

## Overview

This file defines the modified Bessel function of the second kind of order zero, `besselK0`,
through its $\cosh$ integral representation. This $K_0$ profile is the shape of the free
covariance in two dimensions: the radial profile there is $\bigl(1/(2\pi)\bigr)\, K_0(m r)$.
The proper-time (Schwinger) evaluation
$$\int_0^\infty \frac{1}{t}\, e^{-m^2 t - r^2/(4t)}\, dt = 2\, K_0(m r)$$
is the order-zero case of the master identity `schwingerIntegral_eq_besselK`, provided as
`schwingerIntegral_eq_besselK0` (`OSforGFF.General.BesselK`). This file itself contains only
the definition.

## Status

**Main result**: Defines `besselK0` (0 sorries).

**Length**: 33 lines, 1 definition + 0 theorem(s)/lemma(s)

---

### [`besselK0`](../../../OSforGFF/General/BesselK0.lean#L32) — Definition

**Lean signature**
```lean
noncomputable def besselK0 (z : ℝ) : ℝ :=
  ∫ t : ℝ in Ici 0, exp (-z * cosh t)
```

**Informal**: The modified Bessel function $K_0(z)$ of the second kind of order zero, defined
by its $\cosh$ integral representation
$$K_0(z) = \int_0^\infty e^{-z \cosh t}\, dt.$$
Well-defined and positive for $z > 0$.

---

*This file has **1** definitions and **0** theorems/lemmas (0 with sorry).*
