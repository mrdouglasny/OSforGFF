# General Mathematics

Results that do not depend on any project-specific definitions. These are pure extensions of Mathlib covering functional analysis, Schwartz function theory, special function integrals, and positive-definite kernels.

## 1. Functional Analysis

### Mathematical Background

This section develops $L^2$ space infrastructure and properties of bilinear forms involving Schwartz functions and singular kernels. Key results include:

- **$L^p$ embeddings:** Schwartz functions embed continuously into $L^2$ spaces. The embedding `schwartzToL2` sends $\mathcal{S}(\mathbb{R}^d, \mathbb{C})$ into $L^2(\mathbb{R}^d, \mathbb{C})$.
- **Bounded multiplier operators:** If $|g(x)| \le C$ a.e., then $f \mapsto gf$ is a CLM on $L^2$ with $\|gf\|_2 \le C\|f\|_2$.
- **Local integrability:** Functions with $|f(x)| \le C\|x\|^{-\alpha}$ and $\alpha < d$ are locally integrable in dimension $d \ge 3$.
- **Double mollifier convergence:** For a kernel $C$ continuous away from the origin, the double convolution with approximate identities converges to $C(a)$ as the support shrinks to zero.

### Key Declarations (`OSforGFF/General/FunctionalAnalysis.lean`)

| Declaration | Description |
|-------------|-------------|
| [`schwartzToL2`](../OSforGFF/General/FunctionalAnalysis.lean#L254) | $\mathcal{S}(\mathbb{R}^d,\mathbb{C}) \hookrightarrow L^2$ as CLM |
| [`schwartzToL2'`](../OSforGFF/General/FunctionalAnalysis.lean#L260) | Variant for `EuclideanSpace` |
| [`linfty_mul_L2_CLM`](../OSforGFF/General/FunctionalAnalysis.lean#L303) | $L^\infty$ multiplier as CLM on $L^2$ |
| [`linfty_mul_L2_CLM_norm_bound`](../OSforGFF/General/FunctionalAnalysis.lean#L347) | $\lVert gf\rVert_2 \le C\lVert f\rVert_2$ |
| [`locallyIntegrable_of_rpow_decay_real`](../OSforGFF/General/FunctionalAnalysis.lean#L513) | $\lvert f(x)\rvert \le C\lVert x\rVert^{-\alpha},\ \alpha < d \implies$ locally integrable ($d \ge 3$) |
| [`integrableOn_ball_of_rpow_decay`](../OSforGFF/General/FunctionalAnalysis.lean#L408) | Integrability on balls for power-law singularity |
| [`schwartz_bilinear_integrable_of_translationInvariant_L1`](../OSforGFF/General/FunctionalAnalysis.lean#L585) | $f(x)\ K_0(x-y)\ g(y)$ integrable when $K_0 \in L^1$ |
| [`schwartz_integrable_decay`](../OSforGFF/General/FunctionalAnalysis.lean#L887) | $\lvert f(x)\rvert \le C(1+\lVert x\rVert)^{-N}$ for all $N$ |
| [`schwartz_vanishing_linear_bound_general`](../OSforGFF/General/FunctionalAnalysis.lean#L758) | $f\mid_{t\le 0}=0 \implies \lvert f(t,x)\rvert \le Ct$ |
| [`SchwartzMap.translate`](../OSforGFF/General/FunctionalAnalysis.lean#L858) | Translation of Schwartz functions |
| [`double_mollifier_convergence`](../OSforGFF/General/FunctionalAnalysis.lean#L1045) | Double convolution with bump functions $\to$ kernel value |
| [`polynomial_decay_integrable_3d`](../OSforGFF/General/FunctionalAnalysis.lean#L553) | $(1+\lVert x\rVert)^{-4}$ integrable in $\mathbb{R}^3$ |

### Detailed Proof Outline

**Double mollifier convergence** (`double_mollifier_convergence`): Given $C$ continuous on $\{x \ne 0\}$ and $a \ne 0$, with a sequence of bump functions $\varphi_i$ whose support shrinks to zero:

1. Rewrite the double convolution as a single integral against the self-convolution `bumpSelfConv`.
2. Show `bumpSelfConv` is a non-negative approximate identity: integral 1, support in $B(0, 2r_{\mathrm{out}})$.
3. Apply the general approximate identity convergence theorem for continuous functions.

The helper `bumpSelfConv` is the convolution of a normalized bump function with itself. Key properties proved: `bumpSelfConv_nonneg`, `bumpSelfConv_integral` (= 1), `bumpSelfConv_support_subset`, and `bumpSelfConv_support_tendsto`.

---

## 2. Schwartz Functions and Decay Estimates

### Mathematical Background

This section establishes quantitative decay estimates for Schwartz functions and their bilinear pairings with singular kernels. The main results concern:

- **Polynomial decay bounds:** Every $f \in \mathcal{S}$ satisfies $\|f(x)\| \le C(1+\|x\|)^{-N}$ for any $N > 0$.
- **Convolution decay:** Convolutions of Schwartz functions with locally integrable kernels decay at any polynomial rate.
- **Bilinear translation decay:** $\iint f(x)\ K(x-y)\ g(y-a)\ dx\ dy \to 0$ as $\|a\| \to \infty$, with polynomial rate when $K$ has exponential tail decay.

### Proof Strategy

The bilinear decay proofs decompose the kernel $K$ into a singular part (supported on a ball) and a tail part:

$$K(z) = K_{\mathrm{sing}}(z) + K_{\mathrm{tail}}(z)$$

where $K_{\mathrm{sing}}$ is compactly supported and $K_{\mathrm{tail}}$ is bounded. Each piece is handled separately:
- **Singular part:** Compact support means the convolution with a Schwartz function inherits any polynomial decay rate.
- **Tail part:** Exponential decay of $K_{\mathrm{tail}}$ combined with polynomial decay of $f$ gives polynomial decay of the convolution.

The final result combines both pieces using the triangle inequality.

### Key Declarations (`OSforGFF/General/QuantitativeDecay.lean`)

| Declaration | Description |
|-------------|-------------|
| [`PolynomialDecayBound`](../OSforGFF/General/QuantitativeDecay.lean#L58) | Structure: $\lvert f(x)\rvert \le C(1+\lVert x\rVert)^{-N}$ |
| [`schwartz_has_polynomial_decay`](../OSforGFF/General/QuantitativeDecay.lean#L70) | Schwartz functions have polynomial decay of any integer order |
| [`schwartz_has_polynomial_decay_real`](../OSforGFF/General/QuantitativeDecay.lean#L103) | Same for any real exponent $N > 0$ |
| [`exp_decay_implies_polynomial_decay`](../OSforGFF/General/QuantitativeDecay.lean#L122) | $e^{-mx} \le C(1+x)^{-\alpha}$ for any $\alpha$ |
| [`norm_exp_decay_implies_polynomial_decay`](../OSforGFF/General/QuantitativeDecay.lean#L164) | Exponential norm decay $\implies$ polynomial decay |
| [`convolution_polynomial_decay`](../OSforGFF/General/QuantitativeDecay.lean#L276) | Polynomial decay of convolution when both factors decay |
| [`convolution_compactSupport_decay`](../OSforGFF/General/QuantitativeDecay.lean#L440) | Convolution with compactly supported kernel inherits Schwartz decay |
| [`convolution_expDecay_polynomial_decay`](../OSforGFF/General/QuantitativeDecay.lean#L617) | Schwartz $*$ exp-decaying kernel has polynomial decay |

### Key Declarations (`OSforGFF/General/SchwartzTranslationDecay.lean`)

| Declaration | Description |
|-------------|-------------|
| [`schwartz_bilinear_translation_decay_proof`](../OSforGFF/General/SchwartzTranslationDecay.lean#L591) | $\iint f\ K\ g(\cdot - a) \to 0$ at cocompact (power-law $K$) |
| [`schwartz_bilinear_translation_decay_polynomial_proof`](../OSforGFF/General/QuantitativeDecay.lean#L758) | Quantitative polynomial bound (exp-decaying $K$) |
| [`convolution_vanishes_of_integrable_and_C0`](../OSforGFF/General/SchwartzTranslationDecay.lean#L279) | $L^1 * C_0 \to 0$ at infinity |
| [`schwartz_bilinear_prod_integrable`](../OSforGFF/General/SchwartzTranslationDecay.lean#L435) | $f(x)\ K(x-y)\ g(y)$ jointly integrable |
| [`kernelSingular`](../OSforGFF/General/SchwartzTranslationDecay.lean#L105) | Truncation of kernel to a ball |
| [`kernelTail`](../OSforGFF/General/SchwartzTranslationDecay.lean#L109) | Kernel restricted to complement of ball |

---

## 3. Special Functions and Integrals

### Mathematical Background

This section provides closed-form evaluations of special integrals arising in quantum field theory, particularly Fourier transforms of Lorentzian and exponential decay functions, and the Laplace-type integral appearing in the Schwinger representation.

Key identities proved:

- **Fourier transform of exponential decay:**
  $\displaystyle\int_{-\infty}^{\infty} e^{ikx}\ e^{-\mu|x|}\ dx = \frac{2\mu}{k^2+\mu^2}$

- **Fourier inversion for Lorentzian:**
  $\displaystyle\int_{-\infty}^{\infty} \frac{e^{ikx}}{k^2+\mu^2}\ dk = \frac{\pi}{\mu}\ e^{-\mu|x|}$

- **Laplace integral (Glasser's identity):**
  $\displaystyle\int_0^{\infty} s^{-1/2}\ e^{-a/s - bs}\ ds = \sqrt{\pi/b}\ e^{-2\sqrt{ab}}$

### Proof Strategy

**Fourier transforms:** Split the integral at 0. On each half-line, $e^{ikx \mp \mu x}$ has a decaying exponential factor whose antiderivative is computed explicitly. The results combine via $|x| = \pm x$ on each half-line.

**Laplace integral:** The proof chain is:
1. Substitution $s = t^2$ reduces to an integral over $(0, \infty)$.
2. Complete the square: $a/t^2 + bt^2 = (\sqrt{a}/t - \sqrt{b}\ t)^2 + 2\sqrt{ab}$.
3. Factor out $e^{-2\sqrt{ab}}$.
4. Glasser's master theorem (a change-of-variables identity) evaluates the remaining Gaussian-like integral as $\sqrt{\pi}/(2\sqrt{b})$.

### Key Declarations (`OSforGFF/General/FourierTransforms.lean`)

| Declaration | Description |
|-------------|-------------|
| [`fourier_exponential_decay`](../OSforGFF/General/FourierTransforms.lean#L521) | $\widehat{e^{-\mu\lvert x\rvert}} = 2\mu/(k^2+\mu^2)$ |
| [`fourier_exponential_decay'`](../OSforGFF/General/FourierTransforms.lean#L483) | Same with opposite sign convention |
| [`fourier_exp_decay_positive_halfline`](../OSforGFF/General/FourierTransforms.lean#L328) | $\int_0^\infty e^{ikx}\ e^{-\mu x}\ dx$ |
| [`fourier_exp_decay_negative_halfline`](../OSforGFF/General/FourierTransforms.lean#L386) | $\int_{-\infty}^0 e^{ikx}\ e^{\mu x}\ dx$ |
| [`fourier_inversion_exp_decay`](../OSforGFF/General/FourierTransforms.lean#L641) | $(2\pi)^{-1}\int e^{ikx}\ 2\mu/(k^2+\mu^2)\ dk$ |
| [`fourier_lorentzian_1d`](../OSforGFF/General/FourierTransforms.lean#L723) | $\int e^{ikx}/(k^2+\mu^2)\ dk = (\pi/\mu)\ e^{-\mu\lvert x\rvert}$ |
| [`integrable_exponential_decay`](../OSforGFF/General/FourierTransforms.lean#L138) | $e^{-\mu\lvert x\rvert} \in L^1(\mathbb{R})$ |
| [`integrable_exponential_decay_fourier`](../OSforGFF/General/FourierTransforms.lean#L161) | $e^{ikx}\ e^{-\mu\lvert x\rvert} \in L^1(\mathbb{R})$ |
| [`tendsto_cexp_atTop_zero`](../OSforGFF/General/FourierTransforms.lean#L224) | $e^{cx} \to 0$ as $x \to +\infty$ when $\mathrm{Re}(c) < 0$ |
| [`tendsto_cexp_atBot_zero`](../OSforGFF/General/FourierTransforms.lean#L239) | $e^{cx} \to 0$ as $x \to -\infty$ when $\mathrm{Re}(c) > 0$ |

### Key Declarations (`OSforGFF/General/LaplaceIntegral.lean`)

| Declaration | Description |
|-------------|-------------|
| [`laplace_integral_half_power`](../OSforGFF/General/LaplaceIntegral.lean#L542) | $\int_0^\infty s^{-1/2}\ e^{-a/s-bs}\ ds = \sqrt{\pi/b}\ e^{-2\sqrt{ab}}$ |
| [`laplace_integral_half_power_nonneg`](../OSforGFF/General/LaplaceIntegral.lean#L558) | Extension to $a \ge 0$ |
| [`glasser_gaussian_integral`](../OSforGFF/General/LaplaceIntegral.lean#L447) | $\int_0^\infty e^{-(c/u - u)^2}\ du = \sqrt{\pi}/2$ |
| [`weighted_glasser_integral_eq_gaussian`](../OSforGFF/General/LaplaceIntegral.lean#L414) | $\int_0^\infty (1+c/u^2)\ e^{-(c/u-u)^2}\ du = \sqrt{\pi}$ |
| [`glasser_integral_substitution_identity`](../OSforGFF/General/LaplaceIntegral.lean#L100) | Substitution symmetry for Glasser integrals |

---

## 4. $L^2$ Time Integral Estimates

### Mathematical Background

This section provides measure-theoretic estimates for time averages of stochastic processes, used in the ergodicity arguments (OS axiom 4). The main results are:

- **Cauchy-Schwarz for set integrals:** $\displaystyle\left\|\int_{[a,b]} f\right\|^2 \le (b-a)\int_{[a,b]}\|f\|^2$
- **$L^2$ time average bound:** If $\int \|A(s)\|^2\ d\mu \le M$ for all $s \in [0,T]$, then $\int \|T^{-1}\int_0^T A(s)\ ds\|^2\ d\mu \le M$.
- **Product $L^2$ membership:** Joint measurability + uniform slice $L^2$ bounds $\implies$ $L^2$ membership on the product.
- **Double integral polynomial decay:** $\displaystyle\int_0^T\int_0^T (1+|s-u|)^{-\alpha}\ ds\ du \le CT$ for $\alpha > 1$.

### Key Declarations (`OSforGFF/General/L2TimeIntegral.lean`)

| Declaration | Description |
|-------------|-------------|
| [`sq_setIntegral_le_measure_mul_setIntegral_sq_proved`](../OSforGFF/General/L2TimeIntegral.lean#L86) | $\lVert\int_{[a,b]} f\rVert^2 \le (b-a)\int_{[a,b]}\lVert f\rVert^2$ |
| [`L2_time_average_bound`](../OSforGFF/General/L2TimeIntegral.lean#L204) | $L^2$ norm of time average $\le$ sup of slicewise $L^2$ |
| [`time_average_memLp_two`](../OSforGFF/OS/OS4_Ergodicity.lean#L267) | Time average of $L^2$ process $\in L^2$ |
| [`memLp_prod_of_uniform_slicewise_bound`](../OSforGFF/General/L2TimeIntegral.lean#L298) | Product $L^2$ from uniform slicewise bounds |
| [`double_integral_polynomial_decay_bound_proved`](../OSforGFF/General/L2TimeIntegral.lean#L495) | $\int_0^T\int_0^T(1+\lvert s-u\rvert)^{-\alpha}\ ds\ du \le CT$ |
| [`L2_variance_time_average_bound`](../OSforGFF/General/L2TimeIntegral.lean#L725) | $\mathrm{Var}(\text{time avg}) \le \iint \mathrm{Cov}$ |
| [`L2_process_covariance_fubini_integrable`](../OSforGFF/General/L2TimeIntegral.lean#L875) | Fubini integrability for $L^2$ process covariance |
| [`minkowski_weighted_L2_sum_proved`](../OSforGFF/General/L2TimeIntegral.lean#L666) | Minkowski inequality for weighted $L^2$ sums |
| [`gff_covariance_norm_integrableOn_slice_proved`](../OSforGFF/General/L2TimeIntegral.lean#L459) | Covariance norm integrable on time slices |

---

## 5. Positive-Definite Kernels and Matrix Theory

### Mathematical Background

This section develops the theory of positive-definite functions and matrices needed for the Gaussian measure construction. The main results are:

- **Schur product theorem:** $A \circ B \succeq 0$ when $A, B \succeq 0$ (Hadamard product).
- **Hadamard exponential:** $\exp_\circ(R) \succeq 0$ when $R \succeq 0$, proved via the series expansion $\exp_\circ = \sum R^{\circ k}/k!$ and the Schur product theorem.
- **Gaussian RBF positive definiteness:** $h \mapsto e^{-\|h\|^2/2}$ is positive definite on any inner product space.
- **Abstract positive definiteness:** The type class `IsPositiveDefinite` for translation-invariant positive-definite functions on groups.

### Key Declarations (`OSforGFF/General/SchurProduct.lean`)

| Declaration | Description |
|-------------|-------------|
| [`schur_product_posDef`](../OSforGFF/General/SchurProduct.lean#L491) | $A \circ B \succeq 0$ when $A, B \succeq 0$ (Schur product) |
| [`kronLike_posDef`](../OSforGFF/General/SchurProduct.lean#L383) | Kronecker-like product of PosDef matrices is PosDef |

### Key Declarations (`OSforGFF/General/HadamardExp.lean`)

| Declaration | Description |
|-------------|-------------|
| [`entrywiseExp`](../OSforGFF/General/HadamardExp.lean#L38) | Entrywise exponential $(\exp_\circ R)_{ij} = e^{R_{ij}}$ |
| [`posDef_entrywiseExp_hadamardSeries_of_posDef`](../OSforGFF/General/HadamardExp.lean#L310) | $R \succ 0 \implies \exp_\circ(R) \succ 0$ |
| [`posSemidef_entrywiseExp_hadamardSeries_of_posSemidef`](../OSforGFF/General/HadamardExp.lean#L425) | $R \succeq 0 \implies \exp_\circ(R) \succeq 0$ |
| [`hadamardPow_posDef_of_posDef`](../OSforGFF/General/HadamardExp.lean#L141) | $R \succ 0 \implies R^{\circ k} \succ 0$ |

### Key Declarations (`OSforGFF/General/PositiveDefinite.lean`, `OSforGFF/General/GaussianRBF.lean`)

| Declaration | Description |
|-------------|-------------|
| [`IsPositiveDefinite`](../OSforGFF/General/PositiveDefinite.lean#L36) | Positive-definite function on an additive group |
| [`IsPositiveDefiniteKernel`](../OSforGFF/General/GaussianRBF.lean#L24) | Positive-definite kernel $K(x,y)$ |
| [`gaussian_rbf_pd_innerProduct_proof`](../OSforGFF/General/GaussianRBF.lean#L223) | $h \mapsto e^{-\lVert h\rVert^2/2}$ is positive definite |

---

## 6. Nuclear Space Axiom

### Mathematical Background

A small number of standard mathematical results are assumed as axioms (via `axiom`) because their proofs would require substantial Mathlib extensions.

### Key Declarations (`OSforGFF/Measure/NuclearSpace.lean`)

| Declaration | Description |
|-------------|-------------|
| [`NuclearSpace`](../OSforGFF/Measure/NuclearSpace.lean#L126) | Nuclear space via Hilbert-Schmidt embedding characterization |
| [`schwartz_nuclear`](../OSforGFF/Measure/NuclearSpace.lean#L145) | $\mathcal{S}$ is nuclear (assumed) |

## References

- Reed, M. and Simon, B. *Methods of Modern Mathematical Physics*, Vol. I-II.
- Folland, G. *Real Analysis: Modern Techniques and Their Applications*.
- Rudin, W. *Functional Analysis*.
- Glimm, J. and Jaffe, A. *Quantum Physics: A Functional Integral Point of View*.
- Schilling, R. *Measures, Integrals and Martingales*.
