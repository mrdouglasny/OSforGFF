# Comparison of Two Proofs of Reflection Positivity for the Free Covariance

> **Branch**: `reorg-diag`
> **Written**: 2026-03-03

The `reorg-diag` branch contains two independent proofs that the free covariance
kernel satisfies bilinear-form reflection positivity:

$$0 \leq \operatorname{Re} \iint \overline{f(x)}\, C(\Theta x, y)\, f(y)\, dx\, dy$$

for all $f \in \mathcal{S}(\mathbb{R}^4, \mathbb{C})$ supported in positive time.

---

## Proof 1 — Momentum space (existing)

**Files**: `OS3_MixedRepInfra.lean` + `OS3_MixedRep.lean` + `OS3_CovarianceRP.lean`

**Key idea**: Express the bilinear form as a squared norm in Fourier space.

1. **Schwinger representation**: $C(\Theta x, y) = \int_0^\infty e^{-sm^2} H_s(\lVert \Theta x - y \rVert)\, ds$
2. **Fourier decomposition** (`heatKernel_bilinear_fourier_form`): after the $k_0$ integral (1D Gaussian FT), rewrite the bilinear form as
$$\frac{1}{(2\pi)^4} \int_0^\infty \int_{\bar{k}} \int\!\int e^{-s(\lvert \bar{k} \rvert^2 + m^2)} \lvert \hat{F}(\omega, \bar{k}) \rvert^2\, d\omega\, d^3\bar{k}\, ds$$
3. **Nonnegativity**: the integrand is $e^{-s\cdot} \lvert \hat{F} \rvert^2 \geq 0$ pointwise.

**Status**: Complete, no axioms, no sorries.

**Line counts**:

| File | Lines | Sorries |
|------|------:|--------:|
| `OS3_MixedRepInfra.lean` | 3781 | 0 |
| `OS3_MixedRep.lean` | 1888 | 0 |
| `OS3_CovarianceRP.lean` | 455 | 0 |
| **Total** | **6124** | **0** |

**Key bottleneck**: `heatKernel_bilinear_fourier_form` (464 lines) — performing the full
4D Fourier decomposition and $k_0$ integral evaluation via Laplace transform.

---

## Proof 2 — Real-space heat kernel factorization (new)

**Files**: `OS3_DiagonalRP.lean` + `OS3_HeatKernelRP.lean`

**Key idea**: Factor the 4D heat kernel into 1D × 3D parts, reduce to a 1D Hankel operator positivity axiom.

1. **Norm factorization**: $\lVert \Theta x - y \rVert^2 = (x_0 + y_0)^2 + \lVert \bar{x} - \bar{y} \rVert^2$
2. **Heat kernel product**: $H_s^{4D}(\lVert \Theta x - y \rVert) = H_s^{1D}(x_0 + y_0) \cdot H_s^{3D}(\lVert \bar{x} - \bar{y} \rVert)$
3. **Spatial Fourier reduction**: via Parseval on $\mathbb{R}^3$,
$$\operatorname{Re} \iint \overline{f(x)}\, H_s^{3D}(\lVert \bar{x} - \bar{y} \rVert)\, f(y)\, dx\, dy = \frac{1}{(2\pi)^3} \int_{\bar{k}} e^{-s\lvert \bar{k} \rvert^2}\! \left[\operatorname{Re} \iint \overline{\hat{F}(t_1,\bar{k})}\, H_s^{1D}(t_1 + t_2)\, \hat{F}(t_2,\bar{k})\, dt_1\, dt_2 \right] d^3\bar{k}$$
4. **1D axiom** (`heatKernel1D_RP`): each inner bracket is $\geq 0$ because the Hankel operator with kernel $H_s^{1D}(t_1+t_2)$ is positive semidefinite. (Proof sketch: its Laplace symbol is $\sigma(\omega) = \tfrac{1}{2} e^{s\omega^2} \operatorname{erfc}(\omega\sqrt{s}) > 0$; apply Krein's theorem.)
5. **Fubini**: interchange $\int_0^\infty e^{-sm^2}\, ds$ with $\iint f\, f$.

**Status**: Partially proved. Three sorries remain.

**Line counts**:

| File | Lines | Sorries | Status |
|------|------:|--------:|--------|
| `OS3_DiagonalRP.lean` | 304 | 1 | diagonal RP, bilinear form via Proof 1 |
| `OS3_HeatKernelRP.lean` | 252 | 3 | heat kernel route (in progress) |
| **Total (new files)** | **556** | **4** | |

**Estimated completed length**: ~380–450 lines for `OS3_HeatKernelRP.lean`, once
all three sorries are filled.

---

## Remaining sorries in `OS3_HeatKernelRP.lean`

### Sorry 1: `timeReflection_sub_norm_sq` (~15–25 lines)

**Statement**: $\lVert \Theta x - y \rVert^2 = (x_0 + y_0)^2 + \lVert \bar{x} - \bar{y} \rVert^2$

**Approach**: Use `PiLp.norm_sq_eq_of_L2` (as in `OS3_DiagonalRP`), split the
Finset sum at $i = 0$ using `timeReflection_sub_time` and `timeReflection_sub_spatial`,
then reindex the spatial sum to `spatialPart x - spatialPart y`.

**Prereqs already in repo**: `timeReflection_sub_zero`, `spatialPart_timeReflection_sub`
(one-line `rfl` proofs in `OS3_MixedRep.lean`).

---

### Sorry 2: `heatKernelBilinear_nonneg` (~100–150 lines) ← **the hard sorry**

**Statement**: For each $s > 0$,
$$0 \leq \operatorname{Re} \iint \overline{f(x)}\, H_s^{4D}(\lVert \Theta x - y \rVert)\, f(y)\, dx\, dy$$

**Approach**:
1. Substitute `heatKernelFactorization` to split $H_s^{4D} = H_s^{1D} \cdot H_s^{3D}$.
2. Fubini to separate time and spatial integrals.
3. Spatial Parseval: for fixed $t_1, t_2$, the spatial convolution with $H_s^{3D}$ becomes multiplication by $e^{-s\lvert \bar{k} \rvert^2}$ in Fourier space.
4. Apply `heatKernel1D_RP` to the Fourier fiber $g_{t,\bar{k}}(t) = \hat{F}(t, \bar{k})$.

**Infrastructure reused**: `heatKernel_bilinear_fourier_form` from `OS3_MixedRep.lean`
provides the Fourier decomposition machinery, avoiding much of the 464-line proof from scratch.
The key new ingredient is connecting the spatial Fourier fiber to the 1D axiom.

---

### Sorry 3: Fubini in `freeCovariance_RP_heat_kernel` (~15–25 lines)

**Statement**: $\operatorname{Re} \iint \overline{f}\, C(\Theta x, y)\, f = \int_0^\infty e^{-sm^2} \operatorname{Re} \iint \overline{f}\, H_s^{4D}(\lVert \Theta x - y \rVert)\, f\, ds$

**Approach**: Apply `bilinear_schwinger_eq_heatKernel` from `OS3_MixedRep.lean` (110 lines,
already proved using `schwinger_bilinear_integrable` and `schwinger_fubini_swap`), then
take `.re` of both sides and commute it inside the $\int_s$.

---

## Head-to-head comparison

| Criterion | Proof 1 (momentum) | Proof 2 (heat kernel) |
|-----------|-------------------|----------------------|
| Self-contained line count | 6124 | ~5700 est. (reusing MixedRep infra) + new axiom |
| New axioms | None | `heatKernel1D_RP` (Krein's theorem) |
| Core nonnegativity argument | $\lvert \hat{F} \rvert^2 \geq 0$ (algebraic) | 1D Hankel operator $\geq 0$ (analytic axiom) |
| Fourier machinery required | Full 4D including $k_0$ Laplace transform | 3D spatial Parseval only |
| Conceptual clarity | Good; one long computation | Very good; factorization is transparent |
| Scalability to interacting | Hard (kernel is not a heat kernel) | Same difficulty |

**Assessment**: The two proofs are comparable in total length. Proof 2 is conceptually
cleaner — the factorization $\lVert \Theta x - y \rVert^2 = (x_0 + y_0)^2 + \lVert \bar{x} - \bar{y} \rVert^2$
makes the time-reflection structure completely explicit. However, Proof 2 introduces
`heatKernel1D_RP` as an axiom (Krein's theorem), deferring nontrivial analytic content.
Proof 1 is complete with no new axioms.

The main overlap is the Fubini/integrability infrastructure (`OS3_MixedRepInfra.lean`,
`OS3_MixedRep.lean` lines 849–1396), which both proofs rely on. The divergence point is
the nonnegativity argument: Proof 1 uses the algebraic fact $\lvert z \rvert^2 \geq 0$
after a Fourier change of variables; Proof 2 uses the deeper analytic fact that a
specific Hankel operator is positive semidefinite.

---

## Euclidean invariance: from diagonal RP to bilinear-form RP?

### What `OS3_DiagonalRP.lean` establishes

`OS3_DiagonalRP.lean` exploits Euclidean invariance in two ways:

**1. Pointwise nonnegativity** (`freeCovariance_reflection_nonneg`):
$C(\Theta x, y) \geq 0$ for all positive-time $x, y$.
Proof: since the covariance depends only on Euclidean distance,
$C(\Theta x, y) = G(\lVert \Theta x - y \rVert)$, we can find a point $x' = (t, 0, 0, 0)$
on the time axis with $\lVert \Theta x' - x' \rVert = \lVert \Theta x - y \rVert$, hence
$C(\Theta x, y) = C(\Theta x', x') \geq 0$ by the diagonal theorem.

**2. Axis normalization** (`exists_euclidean_to_axis_form`):
For any $x, y \in \mathbb{R}^4$ there exists a Euclidean motion $g$ and $t \geq 0$ such
that $g(x) = (t, 0, 0, 0)$ and $g(y) = (-t, 0, 0, 0)$.  Proved via:
(i) find $R \in O(4)$ rotating $x - y$ onto the time axis (`exists_rotation_map_to_timeAxis`);
(ii) compose with a spatial translation to center the pair.

The proof of `freeCovariance_reflection_nonneg` actually uses a simpler argument —
it does not invoke `exists_euclidean_to_axis_form` but instead directly constructs
$x' = \text{onTimeAxis}(t)$ for $t = \lVert \Theta x - y \rVert / 2$ and uses the
fact that $G$ depends only on the scalar distance.  The full axis normalization theorem
is available for future use.

### The question for bilinear-form RP

The pointwise approach reduces a two-point question to a one-number question by using
Euclidean invariance.  Can the same idea be used to prove positive *definiteness* of the
kernel $K(x, y) = C(\Theta x, y)$?

The kernel $K(x,y) = G(\lVert \Theta x - y \rVert)$ has the following invariance: it
depends only on the "pseudo-distance" $d(x,y) = \lVert \Theta x - y \rVert$, which is
Euclidean-invariant under simultaneous spatial rotations and translations of both $x$ and
$y$.  Two classical theorems relate radial positive definiteness to scalar properties of
$G$:

**Bochner's theorem** (translation-invariant kernels): a kernel $K(x,y) = G(x - y)$ on
$\mathbb{R}^n$ is positive definite if and only if its Fourier transform $\hat{G} \geq 0$.
This applies to $H_s^{3D}(\lVert \bar{x} - \bar{y} \rVert)$ (the spatial factor): its
Fourier transform is $e^{-s\lvert \bar{k} \rvert^2} \geq 0$, so $H_s^{3D}$ is positive
definite on $\mathbb{R}^3$ by Bochner.  This would be a cleaner replacement for the
explicit Parseval computation in Sorry 2.

**Schoenberg's theorem** (radial positive definiteness): a radial function $G(r)$ gives a
positive definite kernel $G(\lVert x - y \rVert)$ on $\mathbb{R}^n$ (for all $n$) if and
only if $G$ is *completely monotone*, i.e. $(-1)^k G^{(k)} \geq 0$ for all $k \geq 0$.
The Schwinger representation $G(r) = \int_0^\infty e^{-sm^2} H_s(r)\, ds$ is precisely
the Bernstein/Laplace-transform witness for complete monotonicity of $r \mapsto G(\sqrt{r})$.
So Schoenberg's theorem would reduce bilinear-form RP for the full covariance to the fact
that the Bessel kernel $G$ is completely monotone — a very clean one-line argument in
principle.

**Open question**: Can `exists_euclidean_to_axis_form` (or Schoenberg/Bochner applied to
the full 4D radial structure) give a self-contained proof of bilinear-form RP that avoids
both the explicit Fourier computation of Proof 1 and the 1D Hankel axiom of Proof 2?

The likely answer is yes for the 3D spatial factor (Bochner is more or less
formalizable once translation-invariant convolution kernels are in Mathlib), but the 1D
time factor — the key point of RP — still requires either the Laplace symbol argument
(`heatKernel1D_RP`) or the direct Fourier trick (`|F̂|² ≥ 0`) of Proof 1.  Schoenberg
in full generality would formalize this cleanly but is itself a substantial Mathlib gap.
