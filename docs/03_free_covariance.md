# Free Covariance

The free massive scalar field propagator $C(x, y)$ and its properties. The construction proceeds from momentum space through Fourier transform to position space, establishing all the analytic properties needed for the OS axioms.

## Mathematical Background

The free Euclidean propagator for a massive scalar field with mass $m > 0$ in $d = 4$ dimensions is defined in momentum space as:

$$\hat{C}(k) = \frac{1}{\|k\|^2 + m^2}$$

The position-space kernel is obtained by inverse Fourier transform:

$$C(x - y) = \frac{1}{(2\pi)^4} \int_{\mathbb{R}^4} \frac{e^{ik\cdot(x-y)}}{\|k\|^2 + m^2}\  d^4k$$

In 4D, this evaluates to the Bessel function representation:

$$C(x, y) = \frac{m}{4\pi^2 \|x - y\|} K_1(m\|x - y\|)$$

where $K_1$ is the modified Bessel function of the second kind. Key properties:
- **Positivity:** $C(x, y) > 0$ for $x \ne y$
- **Symmetry:** $C(x, y) = C(y, x)$
- **Euclidean invariance:** $C(gx, gy) = C(x, y)$ for all $g \in E(4)$
- **Singularity:** $C(x, y) \sim \text{const}/\|x-y\|^2$ as $x \to y$
- **Exponential decay:** $C(x, y) \sim \text{const} \cdot e^{-m\|x-y\|}/\|x-y\|^{3/2}$ as $\|x-y\| \to \infty$

## Proof Strategy

The construction and verification involves four major components:

### 1. Schwinger Representation and Heat Kernel

The propagator admits a proper-time (Schwinger) representation:

$$\frac{1}{\|k\|^2 + m^2} = \int_0^{\infty} e^{-t(\|k\|^2 + m^2)}\  dt$$

Performing the Fourier transform under the proper-time integral yields the **heat kernel representation**:

$$C(x, y) = \int_0^{\infty} e^{-tm^2} H_t(\|x-y\|)\  dt$$

where $H_t(r) = \frac{1}{16\pi^2 t^2} e^{-r^2/(4t)}$ is the 4D heat kernel.

### 2. Regularization Strategy

To rigorously justify Fubini-type exchanges of integration, a Gaussian regulator $e^{-\alpha\|k\|^2}$ is introduced:

$$C_\alpha(x, y) = \int \frac{e^{-\alpha\|k\|^2} e^{ik\cdot(x-y)}}{\|k\|^2 + m^2} \frac{dk}{(2\pi)^4}$$

This makes all integrals absolutely convergent. The true covariance is recovered as $\alpha \to 0^+$. The key technical result is that $C_\alpha(x, y) = C_\alpha^{\text{Schwinger}}(\|x-y\|)$, where the right-hand side involves a regulated Schwinger integral that can be explicitly bounded.

### 3. Bilinear Form and Parseval Identity

For test functions $f, g \in \mathcal{S}(\mathbb{R}^4, \mathbb{C})$, the bilinear covariance form is:

$$\langle f, Cg\rangle = \iint \overline{f(x)}\  C(x-y)\  g(y)\  dx\  dy$$

The **Parseval identity** relates this to momentum space:

$$\mathrm{Re}\langle f, Cf\rangle = \int \frac{|\hat{f}(k)|^2}{\|k\|^2 + m^2}\  dk$$

This immediately gives **positive semi-definiteness**: $\mathrm{Re}\langle f, Cf\rangle \ge 0$ since the integrand is non-negative.

### 4. Hilbert Space Embedding

The covariance form factors through a Hilbert space. Define the map $T\colon \text{TestFunction} \to L^2$ by:

$$Tf(k) = \hat{f}(k) \sqrt{\frac{1}{\|k\|^2 + m^2}}$$

Then $C(f, f) = \|Tf\|^2$, establishing the Hilbert space embedding required by the Minlos theorem.

## Key Declarations

### Momentum Space (`Covariance/Momentum.lean`)

| Declaration | Description |
|-------------|-------------|
| [`freePropagatorMomentum`](../OSforGFF/Covariance/Momentum.lean#L128) | $\hat{C}(k) = 1/(\lVert k\rVert^2 + m^2)$ in physics conventions |
| [`freePropagatorMomentum_mathlib`](../OSforGFF/Covariance/Momentum.lean#L140) | Same in Mathlib Fourier conventions |
| [`freePropagator_pos`](../OSforGFF/Covariance/Momentum.lean#L2092) | $\hat{C}(k) > 0$ |
| [`freePropagator_bounded`](../OSforGFF/Covariance/Momentum.lean#L2101) | $\hat{C}(k) \le 1/m^2$ |
| [`freePropagator_even`](../OSforGFF/Covariance/Momentum.lean#L132) | $\hat{C}(-k) = \hat{C}(k)$ |
| [`freePropagator_smooth`](../OSforGFF/Covariance/Momentum.lean#L2059) | $\hat{C}$ is smooth |
| [`freeCovariance_regulated`](../OSforGFF/Covariance/Momentum.lean#L168) | Gaussian-regulated propagator $C_\alpha(x,y)$ in position space |
| [`freeCovariance`](../OSforGFF/Covariance/Momentum.lean#L468) | The covariance $C(x,y)$ (limit of $C_\alpha$) |
| [`freeCovarianceBessel`](../OSforGFF/Covariance/Momentum.lean#L462) | Bessel representation: $C(x,y) = \frac{m}{4\pi^2 r} K_1(mr)$ |
| [`freeCovarianceKernel`](../OSforGFF/Covariance/Momentum.lean#L1689) | Translation-invariant kernel $C(x-y)$ |
| [`schwingerIntegrand`](../OSforGFF/Covariance/Momentum.lean#L201) | Schwinger integrand $e^{-t(\lVert k\rVert^2+m^2)}$ |
| [`schwinger_representation`](../OSforGFF/Covariance/Momentum.lean#L220) | $\int_0^\infty e^{-t(\lVert k\rVert^2+m^2)}\ dt = 1/(\lVert k\rVert^2+m^2)$ |
| [`heatKernelPositionSpace`](../OSforGFF/Covariance/Momentum.lean#L236) | 4D heat kernel $H_t(r)$ |
| [`heatKernelPositionSpace_integral_eq_one`](../OSforGFF/Covariance/Momentum.lean#L372) | $\int H_t = 1$ |
| [`covarianceSchwingerRep`](../OSforGFF/Covariance/Momentum.lean#L412) | Schwinger representation of covariance |
| [`covarianceSchwingerRep_eq_besselFormula`](../OSforGFF/Covariance/Momentum.lean#L437) | $C^{\text{Schwinger}} = \frac{m}{4\pi^2 r} K_1(mr)$ |
| [`momentumWeight`](../OSforGFF/Covariance/Momentum.lean#L2158) | $\lVert k\rVert^2 + m^2$ as a weight function |
| [`momentumWeightSqrt`](../OSforGFF/Covariance/Momentum.lean#L2167) | $\sqrt{1/(\lVert k\rVert^2 + m^2)}$ |
| [`momentumWeightSqrt_mul_CLM`](../OSforGFF/Covariance/Momentum.lean#L2289) | Multiplication by $\sqrt{\hat{C}(k)}$ as CLM on $L^2$ |

### Convergence and Bounds (`Covariance/Momentum.lean`)

| Declaration | Description |
|-------------|-------------|
| [`freeCovariance_regulated_tendsto_bessel`](../OSforGFF/Covariance/Momentum.lean#L1163) | $C_\alpha \to C_{\text{Bessel}}$ as $\alpha \to 0^+$ |
| [`freeCovariance_regulated_limit_eq_freeCovariance`](../OSforGFF/Covariance/Momentum.lean#L1196) | $C_\alpha \to C$ as $\alpha \to 0^+$ |
| [`freeCovariance_regulated_le_const_mul_freeCovariance`](../OSforGFF/Covariance/Momentum.lean#L1317) | $|C_\alpha| \le e^{m^2} C$ for $\alpha \in (0,1]$ |
| [`freeCovariance_regulated_uniformly_bounded`](../OSforGFF/Covariance/Momentum.lean#L1363) | $C_\alpha$ is uniformly bounded |
| [`freeCovariance_symmetric`](../OSforGFF/Covariance/Momentum.lean#L2043) | $C(x,y) = C(y,x)$ |
| [`freeCovarianceBessel_pos`](../OSforGFF/Covariance/Momentum.lean#L478) | $C(x,y) > 0$ for $x \ne y$ |
| [`freeCovarianceKernel_decay_bound`](../OSforGFF/Covariance/Momentum.lean#L1731) | $\lvert C(z)\rvert \le \text{const} \cdot \lVert z\rVert^{-2}$ |
| [`freeCovariance_exponential_bound`](../OSforGFF/Covariance/Momentum.lean#L1892) | $\lvert C(u,v)\rvert \le \text{const} \cdot e^{-m\lVert u-v\rVert}$ for large separation |
| [`freeCovarianceKernel_integrable`](../OSforGFF/Covariance/Momentum.lean#L1698) | $C_{\text{kernel}} \in L^1$ |
| [`freeCovarianceKernel_continuousOn`](../OSforGFF/Covariance/Momentum.lean#L1971) | $C_{\text{kernel}}$ continuous on $\{z \ne 0\}$ |
| [`fubini_schwinger_fourier`](../OSforGFF/Covariance/Momentum.lean#L824) | $C_\alpha(x,y) = C_\alpha^{\text{Schwinger}}(\lVert x-y\rVert)$ |
| [`gaussianFT_eq_heatKernel_times_norm`](../OSforGFF/Covariance/Momentum.lean#L537) | Gaussian FT $= (2\pi)^d H_t(\lVert z\rVert)$ |

### Parseval Identity (`Covariance/Parseval.lean`)

| Declaration | Description |
|-------------|-------------|
| [`parseval_covariance_schwartz_regulated`](../OSforGFF/Covariance/Parseval.lean#L593) | $\mathrm{Re}\langle f, C_\alpha f\rangle = \int G_\alpha |\hat{f}|^2 \hat{C}\ dk$ |
| [`parseval_covariance_schwartz_correct`](../OSforGFF/Covariance/Parseval.lean#L653) | $\mathrm{Re}\langle f, C_\alpha f\rangle \to \int |\hat{f}|^2 \hat{C}\ dk$ as $\alpha \to 0^+$ |
| [`bilinear_covariance_regulated_tendstoℂ`](../OSforGFF/Covariance/Parseval.lean#L739) | $\langle f, C_\alpha g\rangle \to \langle f, Cg\rangle$ as $\alpha \to 0^+$ |
| [`regulated_fubini_factorization`](../OSforGFF/Covariance/Parseval.lean#L455) | $\mathrm{Re}\langle f, C_\alpha f\rangle$ factors through Fourier transforms |
| [`change_of_variables_momentum`](../OSforGFF/Covariance/Parseval.lean#L418) | Rescaling from physics to Mathlib Fourier conventions |
| [`physicsFourierTransform`](../OSforGFF/Covariance/Parseval.lean#L138) | Physics-convention Fourier transform |
| [`physicsFT_rescale`](../OSforGFF/Covariance/Parseval.lean#L386) | Relation between physics FT and Mathlib FT |
| [`freeCovarianceℂ_bilinear`](../OSforGFF/Covariance/Parseval.lean#L948) | The bilinear form $\langle f, Cg\rangle$ on complex test functions |

### Covariance Properties (`Covariance/Position.lean`, `Covariance/RealForm.lean`)

| Declaration | Description |
|-------------|-------------|
| [`freeCovarianceℂ_bilinear_integrable`](../OSforGFF/Covariance/Position.lean#L205) | $f(x)\ C(x,y)\ g(y)$ is integrable for Schwartz $f, g$ |
| [`freeCovarianceℂ_positive`](../OSforGFF/Covariance/Position.lean#L630) | $\mathrm{Re}\langle f, Cf\rangle \ge 0$ |
| [`parseval_covariance_schwartz_bessel`](../OSforGFF/Covariance/Position.lean#L657) | $\mathrm{Re}\langle f, Cf\rangle = \int |\hat{f}|^2 \hat{C}\ dk$ (final form) |
| [`freeCovariance_euclidean_invariant`](../OSforGFF/Covariance/Position.lean#L403) | $C(gx, gy) = C(x, y)$ for $g \in E(4)$ |
| [`covariance_timeReflection_invariant`](../OSforGFF/Covariance/Position.lean#L424) | $C(\Theta x, \Theta y) = C(x, y)$ |
| [`freeCovarianceℂ_bilinear_symm`](../OSforGFF/Covariance/Position.lean#L557) | $\langle f, Cg\rangle = \langle g, Cf\rangle$ |
| [`freeCovarianceℂ_bilinear_add_left`](../OSforGFF/Covariance/Position.lean#L524) | Additivity in first argument |
| [`freeCovarianceℂ_bilinear_smul_left`](../OSforGFF/Covariance/Position.lean#L534) | Homogeneity in first argument |
| [`freeCovarianceFormR`](../OSforGFF/Covariance/RealForm.lean#L47) | Restriction to real test functions |
| [`freeCovarianceFormR_pos`](../OSforGFF/Covariance/RealForm.lean#L464) | $0 \le C(f, f)$ for real $f$ |
| [`freeCovarianceFormR_symm`](../OSforGFF/Covariance/RealForm.lean#L478) | $C(f, g) = C(g, f)$ for real $f, g$ |
| [`freeCovarianceFormR_continuous`](../OSforGFF/Covariance/RealForm.lean#L451) | $f \mapsto C(f, f)$ is continuous |

### Hilbert Space Embedding (`Covariance/RealForm.lean`)

| Declaration | Description |
|-------------|-------------|
| [`sqrtPropagatorMap`](../OSforGFF/Covariance/RealForm.lean#L89) | $Tf(k) = \hat{f}(k)\sqrt{\hat{C}(k)}$ |
| [`sqrtPropagatorMap_memLp`](../OSforGFF/Covariance/RealForm.lean#L149) | $Tf \in L^2$ |
| [`sqrtPropagatorMap_norm_eq_covariance`](../OSforGFF/Covariance/RealForm.lean#L204) | $\lVert Tf\rVert^2 = C(f,f)$ |
| [`embeddingMap`](../OSforGFF/Covariance/RealForm.lean#L270) | $T$ as a linear map $\text{TestFunction} \to L^2$ |
| [`embeddingMapCLM`](../OSforGFF/Covariance/RealForm.lean#L297) | $T$ as a continuous linear map |
| [`sqrtPropagatorEmbedding`](../OSforGFF/Covariance/RealForm.lean#L342) | $\exists\  H, T$ with $C(f,f) = \lVert Tf\rVert^2$ |
| [`freeCovarianceFormR_eq_normSq`](../OSforGFF/Covariance/RealForm.lean#L432) | $C(f,f) = \lVert\text{embeddingMap}\ f\rVert^2$ |
| [`embeddingMap_continuous`](../OSforGFF/Covariance/RealForm.lean#L439) | $\text{embeddingMap}$ is continuous |

### Reflection Positivity Ingredients (`Covariance/RealForm.lean`)

| Declaration | Description |
|-------------|-------------|
| [`freeCovarianceFormR_reflection_invariant`](../OSforGFF/Covariance/RealForm.lean#L603) | $C(\Theta f, \Theta g) = C(f, g)$ |
| [`freeCovarianceFormR_reflection_cross`](../OSforGFF/Covariance/RealForm.lean#L685) | $C(\Theta f, g) = C(\Theta g, f)$ |
| [`freeCovarianceFormR_left_linear_any_right`](../OSforGFF/Covariance/RealForm.lean#L727) | Linearity of $\sum_i c_i\  C(\Theta f_i, g)$ |

## Detailed Proof Outline

### Parseval Identity

The Parseval identity is proved in four stages:

**Stage 1: Regulated Fubini factorization.** For the regulated integral $\langle f, C_\alpha f\rangle$, the Gaussian regulator $e^{-\alpha\|k\|^2}$ makes the triple integral $(x, y, k)$ absolutely convergent. Apply Fubini to reorder integration, obtaining:

$$\mathrm{Re}\langle f, C_\alpha f\rangle = \int_k G_\alpha(k) \cdot |\hat{f}(k)|^2 \cdot \hat{C}(k)\  dk$$

where $G_\alpha(k) = e^{-\alpha\|k\|^2}$ is the regulator.

**Stage 2: Change of variables.** Rescale from physics Fourier conventions ($\int e^{ikx}$) to Mathlib conventions ($\int e^{-2\pi i k \cdot x}$), absorbing factors of $(2\pi)^d$.

**Stage 3: Monotone convergence.** As $\alpha \to 0^+$, the regulated integrand increases monotonically to the unregulated integrand. The dominated convergence theorem (with dominator $|\hat{f}|^2/m^2$) gives convergence.

**Stage 4: Bilinear extension.** Extend from $\langle f, Cf\rangle$ to $\langle f, Cg\rangle$ via the polarization identity.

### Schwinger Representation

1. Evaluate $\int_0^\infty e^{-t(a^2+m^2)}\ dt = 1/(a^2+m^2)$ for $a^2 = \|k\|^2$.
2. Exchange the $k$-integral and $t$-integral (Fubini, justified by the regulator).
3. The inner $k$-integral is a Gaussian integral giving the heat kernel: $\int e^{-t\|k\|^2 - ik\cdot z}\ dk = (2\pi)^d H_t(\|z\|)$.
4. Complete the square to obtain the Schwinger representation of $C(x,y)$.
5. Evaluate via the Laplace integral (`General/LaplaceIntegral.lean`) to get the Bessel form.

## References

- Glimm, J. and Jaffe, A. *Quantum Physics: A Functional Integral Point of View*, Ch. 6.
- Osterwalder, K. and Schrader, R. "Axioms for Euclidean Green's functions II", *Comm. Math. Phys.* 42 (1975), 281-305.
- Simon, B. *Functional Integration and Quantum Physics*, Academic Press (1979).
- The rp_proof_explained.md document in this repository for the spatial regularization strategy.
