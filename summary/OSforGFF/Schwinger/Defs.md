# `Defs.lean` — Informal Summary

> **Source**: [`OSforGFF/Schwinger/Defs.lean`](../../OSforGFF/Schwinger/Defs.lean)
> **Generated**: 2026-07-05 (regenerated from current source)

## Overview

This file defines the **Schwinger functions** (Euclidean $n$-point correlation functions) of a
probability measure on field configurations, together with the surrounding generating-functional
framework. For a measure $\mu$ on $\mathscr{S}'(\mathbb{R}^d)$ the $n$-point function is
$S_n(f_1,\dots,f_n) = \int \langle \omega, f_1\rangle \cdots \langle \omega, f_n\rangle\, d\mu(\omega)$,
the $n$-th moment of the field operators $\varphi(f) = \langle \omega, f\rangle$. Everything is
generic in the spacetime dimension: the section variables are `{d : ℕ}` (and `{𝕜 : Type} [RCLike 𝕜]`),
and the field lives on `FieldConfiguration d` paired with real test functions `SchwartzTestFunction d` or
complex test functions `SchwartzTestFunctionℂ d`. The file provides the real Schwinger functions and their
1- and 2-point specializations, the complex-test-function versions, and a bilinearity predicate for the
complex 2-point function (with a proof that integrability implies bilinearity). No new axioms are
declared here.

## Status

**Main result**: Fully proven (0 sorries).

**Length**: 235 lines, 6 definition(s) + 2 theorem(s)/lemma(s)

---

## Schwinger Functions

### [`SchwingerFunction`](../../OSforGFF/Schwinger/Defs.lean#L59) — Definition

**Lean signature**
```lean
def SchwingerFunction (dμ_config : ProbabilityMeasure (FieldConfiguration d)) (n : ℕ)
  (f : Fin n → (SchwartzTestFunction d)) : ℝ :=
  ∫ ω, (∏ i, distributionPairing ω (f i)) ∂dμ_config.toMeasure
```

**Informal**: The $n$-th Schwinger function, the $n$-point correlation of field operators
$$S_n(f_1,\dots,f_n) = \int \langle \omega, f_1\rangle\, \langle \omega, f_2\rangle \cdots \langle \omega, f_n\rangle \; d\mu(\omega),$$
the fundamental object of constructive QFT.

---

### [`SchwingerFunction₁`](../../OSforGFF/Schwinger/Defs.lean#L64) — Definition

**Lean signature**
```lean
def SchwingerFunction₁ (dμ_config : ProbabilityMeasure (FieldConfiguration d))
  (f : (SchwartzTestFunction d)) : ℝ :=
  SchwingerFunction dμ_config 1 ![f]
```

**Informal**: The 1-point Schwinger function (the mean field), i.e. $S_1(f)$.

---

### [`SchwingerFunction₂`](../../OSforGFF/Schwinger/Defs.lean#L69) — Definition

**Lean signature**
```lean
def SchwingerFunction₂ (dμ_config : ProbabilityMeasure (FieldConfiguration d))
  (f g : (SchwartzTestFunction d)) : ℝ :=
  SchwingerFunction dμ_config 2 ![f, g]
```

**Informal**: The 2-point Schwinger function (the covariance), i.e. $S_2(f, g)$.

---

### [`schwinger_eq_covariance`](../../OSforGFF/Schwinger/Defs.lean#L75) — Lemma

**Statement**: The 2-point Schwinger function equals the direct covariance integral:
$$S_2(f, g) = \int \langle \omega, f\rangle\, \langle \omega, g\rangle \; d\mu(\omega).$$

**Proof uses**: `SchwingerFunction₂`, `SchwingerFunction`, `Fin.prod_univ_two`

---

### [`SchwingerFunctionℂ`](../../OSforGFF/Schwinger/Defs.lean#L83) — Definition

**Lean signature**
```lean
def SchwingerFunctionℂ (dμ_config : ProbabilityMeasure (FieldConfiguration d)) (n : ℕ)
  (f : Fin n → (SchwartzTestFunctionℂ d)) : ℂ :=
  ∫ ω, (∏ i, distributionPairingℂ_real ω (f i)) ∂dμ_config.toMeasure
```

**Informal**: The complex-valued Schwinger function for complex test functions, using the
complex-linear real pairing $\mathrm{distributionPairingℂ\_real}$ in place of the real pairing.

---

### [`SchwingerFunctionℂ₂`](../../OSforGFF/Schwinger/Defs.lean#L89) — Definition

**Lean signature**
```lean
def SchwingerFunctionℂ₂ (dμ_config : ProbabilityMeasure (FieldConfiguration d))
  (φ ψ : (SchwartzTestFunctionℂ d)) : ℂ :=
  SchwingerFunctionℂ dμ_config 2 ![φ, ψ]
```

**Informal**: The complex 2-point Schwinger function $S_2^{\mathbb{C}}(\varphi, \psi)$, the natural
extension of `SchwingerFunction₂` to complex test functions.

---

### [`CovarianceBilinear`](../../OSforGFF/Schwinger/Defs.lean#L95) — Definition

**Lean signature**
```lean
def CovarianceBilinear (dμ_config : ProbabilityMeasure (FieldConfiguration d)) : Prop :=
  ∀ (c : ℂ) (φ₁ φ₂ ψ : (SchwartzTestFunctionℂ d)),
    SchwingerFunctionℂ₂ dμ_config (c • φ₁) ψ = c * SchwingerFunctionℂ₂ dμ_config φ₁ ψ ∧
    SchwingerFunctionℂ₂ dμ_config (φ₁ + φ₂) ψ = SchwingerFunctionℂ₂ dμ_config φ₁ ψ + SchwingerFunctionℂ₂ dμ_config φ₂ ψ ∧
    SchwingerFunctionℂ₂ dμ_config φ₁ (c • ψ) = c * SchwingerFunctionℂ₂ dμ_config φ₁ ψ ∧
    SchwingerFunctionℂ₂ dμ_config φ₁ (ψ + φ₂) = SchwingerFunctionℂ₂ dμ_config φ₁ ψ + SchwingerFunctionℂ₂ dμ_config φ₁ φ₂
```

**Informal**: The predicate that $S_2^{\mathbb{C}}$ is $\mathbb{C}$-bilinear in each argument
(scalar and additive in both slots) — a key property for Gaussian measures and essential for OS0
analyticity.

---

### [`CovarianceBilinear_of_integrable`](../../OSforGFF/Schwinger/Defs.lean#L104) — Lemma

**Statement**: If for all complex test functions $\varphi, \psi$ the product pairing
$\omega \mapsto \mathrm{distributionPairingℂ\_real}(\omega, \varphi)\,\mathrm{distributionPairingℂ\_real}(\omega, \psi)$
is integrable under $\mu$, then $S_2^{\mathbb{C}}$ is $\mathbb{C}$-bilinear, i.e.
`CovarianceBilinear dμ_config` holds.

**Proof uses**: `pairing_linear_combo`, `integral_smul`, `integral_add`, `Fin.prod_univ_two`, unfolding `SchwingerFunctionℂ₂`/`SchwingerFunctionℂ`

---

*This file has **6** definitions and **2** theorems/lemmas (0 with sorry).*
