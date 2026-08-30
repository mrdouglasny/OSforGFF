# `ComplexTestFunction.lean` — Informal Summary

> **Source**: [`OSforGFF/Spacetime/ComplexTestFunction.lean`](../../../OSforGFF/Spacetime/ComplexTestFunction.lean)
> **Generated**: 2026-07-05 (regenerated from current source)

## Overview

This file establishes linearity properties of complex test functions and their pairings with
field configurations, generic in the spacetime dimension `d : ℕ`. It records how the real/imaginary
decomposition of a complex test function behaves under $\mathbb{C}$-linear combinations
(`ω_re_decompose_linear`, `ω_im_decompose_linear`), and derives the key
$\mathbb{C}$-linearity of the complex pairing `distributionPairingℂ_real` in its test-function
argument (`pairing_linear_combo`) — needed for bilinearity of the Schwinger functions. It also
builds the real$\to$complex Schwartz embedding `toComplex` / `toComplexCLM` (using that the
$\mathbb{R} \to \mathbb{C}$ embedding is an isometry that preserves iterated-derivative norms), and
the pointwise conjugation operator `conjSchwartz` on complex Schwartz functions, culminating in the
conjugation identity $\overline{\langle\omega, f\rangle} = \langle\omega, \bar f\rangle$.

## Status

**Main result**: $\mathbb{C}$-linearity of the complex pairing plus the real$\to$complex embedding
and pointwise conjugation of Schwartz functions. Fully proven (0 sorries; no `sorry`/`admit`).

**Length**: 385 lines, 3 definition(s) + 19 theorem(s)/lemma(s)

---

### [`re_of_complex_combination`](../../../OSforGFF/Spacetime/ComplexTestFunction.lean#L51) — Lemma *(private)*

**Statement**: $\mathrm{Re}(a u + b v) = a_{\mathrm{re}} u_{\mathrm{re}} - a_{\mathrm{im}} u_{\mathrm{im}} + b_{\mathrm{re}} v_{\mathrm{re}} - b_{\mathrm{im}} v_{\mathrm{im}}$ for $a, b, u, v \in \mathbb{C}$.

---

### [`im_of_complex_combination`](../../../OSforGFF/Spacetime/ComplexTestFunction.lean#L58) — Lemma *(private)*

**Statement**: $\mathrm{Im}(a u + b v) = a_{\mathrm{re}} u_{\mathrm{im}} + a_{\mathrm{im}} u_{\mathrm{re}} + b_{\mathrm{re}} v_{\mathrm{im}} + b_{\mathrm{im}} v_{\mathrm{re}}$ for $a, b, u, v \in \mathbb{C}$.

---

### [`ω_re_decompose_linear`](../../../OSforGFF/Spacetime/ComplexTestFunction.lean#L67) — Lemma

**Statement**: $\omega$-linearity of the real component of the complex decomposition under a
combination $t \cdot f + s \cdot g$ ($t, s \in \mathbb{C}$):
$$\omega\bigl((\mathrm{decompose}(t f + s g)).1\bigr) = t_{\mathrm{re}}\,\omega(f_{\mathrm{re}}) - t_{\mathrm{im}}\,\omega(f_{\mathrm{im}}) + s_{\mathrm{re}}\,\omega(g_{\mathrm{re}}) - s_{\mathrm{im}}\,\omega(g_{\mathrm{im}}),$$
following from $\mathbb{R}$-linearity of $\omega$ and pointwise complex algebra.

**Proof uses**: [`re_of_complex_combination`](../../../OSforGFF/Spacetime/ComplexTestFunction.lean#L51), [`complex_testfunction_decompose`](../../../OSforGFF/Spacetime/Basic.lean#L191)

---

### [`ω_im_decompose_linear`](../../../OSforGFF/Spacetime/ComplexTestFunction.lean#L101) — Lemma

**Statement**: $\omega$-linearity of the imaginary component of the complex decomposition under
$t \cdot f + s \cdot g$:
$$\omega\bigl((\mathrm{decompose}(t f + s g)).2\bigr) = t_{\mathrm{re}}\,\omega(f_{\mathrm{im}}) + t_{\mathrm{im}}\,\omega(f_{\mathrm{re}}) + s_{\mathrm{re}}\,\omega(g_{\mathrm{im}}) + s_{\mathrm{im}}\,\omega(g_{\mathrm{re}}).$$

**Proof uses**: [`im_of_complex_combination`](../../../OSforGFF/Spacetime/ComplexTestFunction.lean#L58), [`complex_testfunction_decompose`](../../../OSforGFF/Spacetime/Basic.lean#L191)

---

### [`pairing_linear_combo`](../../../OSforGFF/Spacetime/ComplexTestFunction.lean#L134) — Lemma

**Statement**: The complex pairing is $\mathbb{C}$-linear in the test-function argument:
$$\langle\omega,\, t f + s g\rangle_{\mathbb{C}} = t\,\langle\omega, f\rangle_{\mathbb{C}} + s\,\langle\omega, g\rangle_{\mathbb{C}}.$$

**Proof uses**: [`ω_re_decompose_linear`](../../../OSforGFF/Spacetime/ComplexTestFunction.lean#L67), [`ω_im_decompose_linear`](../../../OSforGFF/Spacetime/ComplexTestFunction.lean#L101), [`distributionPairingℂ_real`](../../../OSforGFF/Spacetime/Basic.lean#L234)

---

### [`Complex.norm_ofRealCLM`](../../../OSforGFF/Spacetime/ComplexTestFunction.lean#L181) — Lemma

**Statement**: The $\mathbb{R}$-linear embedding $\mathbb{R} \to \mathbb{C}$ has operator norm $1$: $\lVert \mathrm{Complex.ofRealCLM}\rVert = 1$.

**Proof uses**: `ofRealCLM_norm`

---

### [`norm_compContinuousMultilinearMap_ofReal`](../../../OSforGFF/Spacetime/ComplexTestFunction.lean#L186) — Lemma

**Statement**: Composing a continuous multilinear map $m$ (into $\mathbb{R}$) with the
real$\to$complex embedding preserves the operator norm:
$$\lVert \mathrm{Complex.ofRealCLM.compContinuousMultilinearMap}\, m\rVert = \lVert m\rVert,$$
since the embedding is an isometry.

---

### [`iteratedFDeriv_ofReal_norm_eq`](../../../OSforGFF/Spacetime/ComplexTestFunction.lean#L209) — Lemma

**Statement**: For a real test function $f$, the $n$-th iterated derivative of the complexified
map has the same norm as that of $f$:
$$\lVert D^n\bigl(x \mapsto (f(x) : \mathbb{C})\bigr)(x)\rVert = \lVert D^n f(x)\rVert.$$

**Proof uses**: [`norm_compContinuousMultilinearMap_ofReal`](../../../OSforGFF/Spacetime/ComplexTestFunction.lean#L186), `ContinuousLinearMap.iteratedFDeriv_comp_left`

---

### [`toComplex`](../../../OSforGFF/Spacetime/ComplexTestFunction.lean#L220) — Definition

**Lean signature**
```lean
def toComplex (f : (SchwartzTestFunction d)) : (SchwartzTestFunctionℂ d)
```

**Informal**: Embed a real test function as a complex-valued test function by coercing values via
$\mathbb{R} \to \mathbb{C}$; smoothness and Schwartz-decay bounds are preserved because the
coercion is a norm-preserving continuous linear map.

---

### [`toComplex_apply`](../../../OSforGFF/Spacetime/ComplexTestFunction.lean#L236) — Lemma *(simp)*

**Statement**: $\mathrm{toComplex}\, f\, x = (f(x) : \mathbb{C})$ (by `rfl`).

---

### [`complex_testfunction_decompose_toComplex_fst`](../../../OSforGFF/Spacetime/ComplexTestFunction.lean#L241) — Lemma *(simp)*

**Statement**: The real part of `toComplex f` is `f` itself: $(\mathrm{decompose}(\mathrm{toComplex}\, f)).1 = f$.

---

### [`complex_testfunction_decompose_toComplex_snd`](../../../OSforGFF/Spacetime/ComplexTestFunction.lean#L246) — Lemma *(simp)*

**Statement**: The imaginary part of `toComplex f` vanishes: $(\mathrm{decompose}(\mathrm{toComplex}\, f)).2 = 0$.

---

### [`toComplex_add`](../../../OSforGFF/Spacetime/ComplexTestFunction.lean#L251) — Lemma *(simp)*

**Statement**: $\mathrm{toComplex}(f + g) = \mathrm{toComplex}\, f + \mathrm{toComplex}\, g$.

---

### [`toComplex_smul`](../../../OSforGFF/Spacetime/ComplexTestFunction.lean#L256) — Lemma *(simp)*

**Statement**: $\mathrm{toComplex}(c \cdot f) = (c : \mathbb{C}) \cdot \mathrm{toComplex}\, f$ for $c \in \mathbb{R}$.

---

### [`toComplexCLM`](../../../OSforGFF/Spacetime/ComplexTestFunction.lean#L267) — Definition

**Lean signature**
```lean
noncomputable def toComplexCLM : (SchwartzTestFunction d) →L[ℝ] (SchwartzTestFunctionℂ d)
```

**Informal**: The continuous $\mathbb{R}$-linear map version of `toComplex`, built via
`SchwartzMap.mkCLM` from linearity, smoothness, and the preserved derivative-norm bounds.

---

### [`toComplexCLM_apply`](../../../OSforGFF/Spacetime/ComplexTestFunction.lean#L283) — Lemma *(simp)*

**Statement**: $\mathrm{toComplexCLM}\, f = \mathrm{toComplex}\, f$.

---

### [`distributionPairingℂ_real_toComplex`](../../../OSforGFF/Spacetime/ComplexTestFunction.lean#L288) — Lemma *(simp)*

**Statement**: The complex pairing of $\omega$ with a complexified real test function reduces to
the real pairing: $\langle\omega, \mathrm{toComplex}\, f\rangle_{\mathbb{C}} = \langle\omega, f\rangle$.

---

### [`GJGeneratingFunctionalℂ_toComplex`](../../../OSforGFF/Spacetime/ComplexTestFunction.lean#L295) — Lemma *(simp)*

**Statement**: The complex generating functional on a complexified real test function equals the
real generating functional: $Z_{\mathbb{C}}[\mathrm{toComplex}\, f] = Z[f]$.

**Proof uses**: [`GJGeneratingFunctionalℂ`](../../../OSforGFF/Spacetime/Basic.lean#L241), [`GJGeneratingFunctional`](../../../OSforGFF/Spacetime/Basic.lean#L150)

---

### [`conjSchwartz`](../../../OSforGFF/Spacetime/ComplexTestFunction.lean#L312) — Definition

**Lean signature**
```lean
noncomputable def conjSchwartz {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : SchwartzMap E ℂ) : SchwartzMap E ℂ
```

**Informal**: Pointwise complex conjugation of a complex Schwartz function,
$(\mathrm{conjSchwartz}\, f)(x) = \overline{f(x)}$; again a Schwartz function because conjugation
`Complex.conjCLE` is a smooth continuous $\mathbb{R}$-linear isometry preserving all seminorms.

---

### [`conjSchwartz_apply`](../../../OSforGFF/Spacetime/ComplexTestFunction.lean#L343) — Lemma *(simp)*

**Statement**: $\mathrm{conjSchwartz}\, f\, x = \mathrm{starRingEnd}\, \mathbb{C}\,(f(x))$ (by `rfl`).

---

### [`conjSchwartz_conjSchwartz`](../../../OSforGFF/Spacetime/ComplexTestFunction.lean#L348) — Lemma *(simp)*

**Statement**: Conjugation is involutive: $\mathrm{conjSchwartz}(\mathrm{conjSchwartz}\, f) = f$.

---

### [`distributionPairingℂ_real_conj`](../../../OSforGFF/Spacetime/ComplexTestFunction.lean#L363) — Lemma

**Statement**: For a real field configuration $\omega$, conjugating the complex pairing equals
pairing with the conjugated test function:
$$\overline{\langle\omega, f\rangle_{\mathbb{C}}} = \langle\omega, \mathrm{conjSchwartz}\, f\rangle_{\mathbb{C}},$$
using that $(\bar f)_{\mathrm{re}} = f_{\mathrm{re}}$ and $(\bar f)_{\mathrm{im}} = -f_{\mathrm{im}}$.

**Proof uses**: [`distributionPairingℂ_real`](../../../OSforGFF/Spacetime/Basic.lean#L234), [`complex_testfunction_decompose_fst_apply`](../../../OSforGFF/Spacetime/Basic.lean#L195), [`complex_testfunction_decompose_snd_apply`](../../../OSforGFF/Spacetime/Basic.lean#L201)

---

*This file has **3** definitions and **19** theorems/lemmas (0 with sorry).*
