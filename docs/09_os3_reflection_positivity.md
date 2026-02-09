# OS3: Reflection Positivity

## Mathematical Background

Reflection positivity (OS3) is the most technically demanding of the Osterwalder-Schrader axioms. It is the Euclidean manifestation of **unitarity** -- the requirement that quantum mechanics has positive probabilities and the Hilbert space has a positive-definite inner product. Without OS3, a Euclidean field theory cannot be analytically continued to define a physical relativistic QFT.

### Key definitions

**Time reflection.** The operator

$$\Theta: (x_0, \vec{x}) \mapsto (-x_0, \vec{x})$$

flips the time coordinate. It is an involution ($\Theta^2 = \mathrm{id}$) and preserves Lebesgue measure.

**Positive-time test functions.** The space $\mathcal{S}_+$ consists of Schwartz functions supported on $\lbrace x : x_0 > 0\rbrace$.

**Reflection positivity inner product.** For the free covariance $C(x,y) = \frac{m}{4\pi^2\lVert x-y\rVert} K_1(m\lVert x-y\rVert)$:

$$\langle \Theta f, f \rangle_C := \int_{\mathbb{R}^4} \int_{\mathbb{R}^4} \overline{f(\Theta x)}\  C(x,y)\  f(y)\  dx\  dy$$

**OS3 axiom (Glimm-Jaffe form).** For positive-time test functions and real coefficients:

$$f_1, \ldots, f_n \in \mathcal{S}_+, \qquad c_1, \ldots, c_n \in \mathbb{R}$$

$$\sum_{i,j} c_i c_j \  \mathrm{Re}\left(Z[f_i - \Theta f_j]\right) \geq 0$$

where the generating functional (characteristic functional) is

$$Z[f] = \int e^{i\langle\omega,f\rangle}\ d\mu(\omega)$$

For the GFF, this evaluates to $Z[f] = e^{-C(f,f)/2}$ for real $f$.

## Proof Strategy

The proof has two main parts that work together:

1. **Covariance reflection positivity via Fourier analysis:** Show $\mathrm{Re}\langle \Theta f, Cf \rangle \geq 0$ for each positive-time $f$ by rewriting the bilinear form in momentum space and factorizing into a squared norm.

2. **Matrix assembly via the Hadamard (Schur) product theorem:** Extend from a single test function to the general $n$-function case using Gaussian factorization and the fact that entrywise exponentials of PSD matrices remain PSD.

### Literature references

- Osterwalder-Schrader (1973, 1975): Original axioms and reconstruction theorem.
- Glimm-Jaffe, *Quantum Physics* (2nd ed.): Generating functional formulation.
- Polya-Szego / Schur: Entrywise (Hadamard) product theorem for PSD matrices.

## Key Declarations

### Covariance RP infrastructure (`OS3_MixedRepInfra.lean`, `OS3_MixedRep.lean`)

| Declaration | Description |
|-------------|-------------|
| [`heatKernel_eq_gaussianFT`](../OSforGFF/OS3_MixedRepInfra.lean#L191) | $H_t(z) = \mathcal{F}[e^{-t\lVert k\rVert^2}](z)$ |
| [`schwinger_bilinear_integrable`](../OSforGFF/OS3_MixedRep.lean#L883) | $\int_0^\infty e^{-sm^2} \lvert\langle f, H_s g\rangle\rvert\ ds < \infty$ |
| [`schwinger_fubini_core`](../OSforGFF/OS3_MixedRep.lean#L1102) | Fubini swap: $(x,y)$-integral vs $s$-integral |
| [`schwinger_fubini_swap`](../OSforGFF/OS3_MixedRep.lean#L1182) | Pull $s$-integral inside the bilinear form |
| [`bilinear_schwinger_eq_heatKernel`](../OSforGFF/OS3_MixedRep.lean#L1321) | $\langle\Theta f, Cf\rangle = \int_0^\infty e^{-sm^2}\langle\Theta f, H_s f\rangle\ ds$ |
| [`heatKernel_bilinear_fourier_form`](../OSforGFF/OS3_MixedRep.lean#L259) | $\langle f, H_s g\rangle = \int e^{-s\lVert k\rVert^2}\hat{f}(-k)\hat{g}(k)\ dk$ |
| [`laplace_s_integral_with_norm`](../OSforGFF/OS3_MixedRep.lean#L723) | $\int_0^\infty \sqrt{\pi/s}\ e^{-t^2/(4s)-s\omega^2}\ ds = (\pi/\omega)e^{-\omega\lvert t\rvert}$ |
| [`bessel_bilinear_eq_mixed_representation`](../OSforGFF/OS3_MixedRep.lean#L1711) | Mixed (energy-momentum) representation of $\langle\Theta f, Cf\rangle$ |
| [`bilinear_to_k0_inside`](../OSforGFF/OS3_MixedRep.lean#L1773) | Rewrite with $k_0$ integral internalized |
| [`fubini_s_ksp_swap`](../OSforGFF/OS3_MixedRepInfra.lean#L2848) | Fubini swap: proper-time $s$ vs spatial momentum $\vec{k}$ |
| [`fubini_s_xy_swap`](../OSforGFF/OS3_MixedRepInfra.lean#L3064) | Fubini swap: proper-time $s$ vs spacetime $(x,y)$ |
| [`fubini_ksp_xy_swap`](../OSforGFF/OS3_MixedRepInfra.lean#L3547) | Fubini swap: spatial momentum $\vec{k}$ vs spacetime $(x,y)$ |

### Covariance RP direct proof (`OS3_CovarianceRP.lean`)

| Declaration | Description |
|-------------|-------------|
| [`QFT.RPProof.rpInnerProduct`](../OSforGFF/OS3_CovarianceRP.lean#L115) | RP inner product: $\langle \Theta f, f\rangle_C$ via Bessel kernel |
| [`QFT.RPProof.weightedLaplaceFourier`](../OSforGFF/OS3_MixedRepInfra.lean#L122) | $F_\omega(\vec{k}) = \int f(x)\ e^{-\omega x_0}e^{-i\vec{k}\cdot\vec{x}}\ dx$ |
| [`QFT.RPProof.mixed_representation`](../OSforGFF/OS3_CovarianceRP.lean#L148) | Mixed representation of the RP inner product |
| [`QFT.RPProof.factorization_to_squared_norm_direct`](../OSforGFF/OS3_CovarianceRP.lean#L256) | Positive-time factorization into $\lvert F_\omega\rvert^2$ |
| [`QFT.RPProof.rp_equals_squared_norm_integral`](../OSforGFF/OS3_CovarianceRP.lean#L350) | $\langle\Theta f, f\rangle_C = \frac{1}{2(2\pi)^3}\int \frac{\lvert F_\omega(\vec{k})\rvert^2}{\omega}\ d\vec{k}$ |
| [`QFT.RPProof.freeCovariance_reflection_positive_direct`](../OSforGFF/OS3_CovarianceRP.lean#L375) | $\mathrm{Re}\langle \Theta f, f\rangle_C \geq 0$ |

### Bridge and real formulation (`OS3_CovarianceRP.lean`)

| Declaration | Description |
|-------------|-------------|
| [`QFT.rpInnerProduct`](../OSforGFF/OS3_CovarianceRP.lean#L78) | RP inner product in QFT namespace |
| [`QFT.rpInnerProduct_eq_rpProof`](../OSforGFF/OS3_CovarianceRP.lean#L409) | Bridge: QFT and RPProof definitions agree (by `rfl`) |
| [`QFT.freeCovariance_reflection_positive_bilinear`](../OSforGFF/OS3_CovarianceRP.lean#L427) | $\mathrm{Re}\langle\Theta f, Cf\rangle \geq 0$ for complex $f \in \mathcal{S}_+$ |
| [`QFT.freeCovariance_reflection_positive_bilinear_real`](../OSforGFF/OS3_CovarianceRP.lean#L457) | $\langle\Theta f, Cf\rangle \geq 0$ for real $f \in \mathcal{S}_+$ |
| [`QFT.freeCovariance_reflection_positive_real`](../OSforGFF/OS3_CovarianceRP.lean#L478) | Alias for the real version |

### GFF OS3 assembly (`OS3_GFF.lean`)

| Declaration | Description |
|-------------|-------------|
| [`freeCovarianceFormR_reflection_matrix_posSemidef`](../OSforGFF/OS3_GFF.lean#L68) | $R_{ij} = \langle\Theta f_i, Cf_j\rangle$ is PSD |
| [`freeCovarianceFormR_reflection_expansion`](../OSforGFF/OS3_GFF.lean#L215) | $C(f-\Theta g, f-\Theta g) = C(f,f) + C(g,g) - 2\langle\Theta f, Cg\rangle$ |
| [`gaussianFreeField_real_generating_re`](../OSforGFF/OS3_GFF.lean#L329) | $\mathrm{Re}(Z[h]) = \exp(-C(h,h)/2)$ for real $h$ |
| [`gaussianFreeField_real_entry_factor`](../OSforGFF/OS3_GFF.lean#L349) | $\mathrm{Re}(Z[f_i - \Theta f_j]) = Z[f_i] \cdot Z[f_j] \cdot e^{R_{ij}}$ |
| [`gaussianFreeField_OS3_matrix_real`](../OSforGFF/OS3_GFF.lean#L440) | $\sum_{ij} c_i c_j \mathrm{Re}(Z[f_i - \Theta f_j]) \geq 0$ |
| [`gaussianFreeField_OS3_real`](../OSforGFF/OS3_GFF.lean#L509) | **Master OS3 theorem**: GFF satisfies `OS3_ReflectionPositivity` |

## Detailed Proof Outline

### Part 1: Covariance Reflection Positivity

**Goal:** For any complex test function $f$ with $f(x) = 0$ when $x_0 \leq 0$, show $\mathrm{Re}\langle\Theta f, f\rangle_C \geq 0$.

#### Step 1 -- Change of variables and Schwinger representation

Replace $C(\Theta x, y)$ by its proper-time (Schwinger) representation:

$$C(\Theta x, y) = \int_0^\infty e^{-sm^2} H(s, \|\Theta x - y\|)\  ds$$

where $H(s, r) = (4\pi s)^{-d/2} e^{-r^2/(4s)}$ is the heat kernel. Integrability of the Schwinger integrand against Schwartz test functions is established in `schwinger_bilinear_integrable`.

#### Step 2 -- Fourier decomposition of the heat kernel

Write the heat kernel as a Fourier integral:

$$H(s, \|z\|) = \frac{1}{(2\pi)^4} \int_{\mathbb{R}^4} e^{ik\cdot z}\  e^{-s\|k\|^2}\  dk$$

Decompose $k = (k_0, \vec{k})$ and separate the time and spatial contributions. Three Fubini interchanges (`fubini_s_ksp_swap`, `fubini_s_xy_swap`, `fubini_ksp_xy_swap`) are proved with explicit integrability bounds.

#### Step 3 -- Evaluate the proper-time integral

After separating momentum components, evaluate the $s$-integral analytically. The key identity (`s_integral_eval`) is:

$$\int_0^\infty \sqrt{\pi/s}\  e^{-t^2/(4s)}\  e^{-s\omega^2}\  ds = \frac{\pi}{\omega}\  e^{-\omega|t|}$$

where $\omega = \sqrt{\lVert\vec{k}\rVert^2 + m^2}$. This yields the **mixed representation** (`bessel_bilinear_eq_mixed_representation`):

$$\langle\Theta f, f\rangle_C = \frac{1}{2(2\pi)^3} \int_{\mathbb{R}^3} \frac{1}{\omega}\  (\text{inner integral})\  d\vec{k}$$

#### Step 4 -- Factorization using positive-time support

The inner integral involves $e^{-\omega\lvert -x_0 - y_0\rvert}$. For positive-time test functions ($x_0 > 0$, $y_0 > 0$), we have $\lvert -x_0 - y_0\rvert = x_0 + y_0$. This gives the key factorization:

$$e^{-\omega(x_0 + y_0)} = e^{-\omega x_0} \cdot e^{-\omega y_0}$$

Similarly, the spatial phase factor splits:

$$e^{-i\vec{k}\cdot(\vec{x} - \vec{y})} = e^{-i\vec{k}\cdot\vec{x}} \cdot e^{i\vec{k}\cdot\vec{y}}$$

The double $(x,y)$-integral then factors into $\lvert F_\omega(\vec{k})\rvert^2$ where $F_\omega$ is the **weighted Laplace-Fourier transform** (`weightedLaplaceFourier`):

$$F_\omega(\vec{k}) = \int_{\mathbb{R}^4} f(x)\  e^{-\omega x_0}\  e^{-i\vec{k}\cdot\vec{x}}\  dx$$

This factorization is proved in `factorization_to_squared_norm_direct`.

#### Step 5 -- Non-negativity

The final form is (`rp_equals_squared_norm_integral`):

$$\langle\Theta f, f\rangle_C = \frac{1}{2(2\pi)^3} \int_{\mathbb{R}^3} \frac{1}{\omega(\vec{k})}\  |F_\omega(-\vec{k})|^2\  d\vec{k}$$

Since $\omega > 0$ (because $m > 0$) and $\lvert F_\omega\rvert^2 \geq 0$, the integrand is pointwise non-negative, so the integral is non-negative. This is concluded in `freeCovariance_reflection_positive_direct`.

### Part 2: From Single Function to Matrix PSD

#### Step 6 -- Reflection covariance matrix is PSD

Define $R_{ij} = \langle\Theta f_i, C f_j\rangle$. For any real vector $c$:

$$\sum_{ij} c_i c_j R_{ij} = \langle\Theta g, Cg\rangle \geq 0 \quad\text{where } g = \sum_i c_i f_i$$

This uses bilinearity of the covariance form and the single-function result from Part 1. The sum $g$ remains a positive-time function. Proved in `freeCovarianceFormR_reflection_matrix_posSemidef`.

#### Step 7 -- Hadamard exponential preserves PSD

By the **Schur product theorem**, if $R$ is PSD then the entrywise exponential $E_{ij} = e^{R_{ij}}$ is also PSD. The proof uses the Hadamard series expansion:

$$e^{R_{ij}} = \sum_{k=0}^\infty \frac{(R_{ij})^k}{k!}$$

Each term is an entrywise $k$-th power of a PSD matrix, which is PSD by repeated Hadamard products. The convergent sum of PSD matrices is PSD. This is proved via `entrywiseExp_posSemidef_of_posSemidef` (using infrastructure from `HadamardExp.lean`).

#### Step 8 -- Entry factorization and assembly

For the Gaussian generating functional, the quadratic expansion (`freeCovarianceFormR_reflection_expansion`) gives:

$$C(f - \Theta g, f - \Theta g) = C(f,f) + C(g,g) - 2\langle\Theta f, Cg\rangle$$

This yields the entry factorization (`gaussianFreeField_real_entry_factor`):

$$\mathrm{Re}\left(Z[f_i - \Theta f_j]\right) = Z[f_i] \cdot Z[f_j] \cdot e^{R_{ij}}$$

where $Z[f] = \exp(-C(f,f)/2) > 0$.

Setting $y_i = c_i \cdot Z[f_i]$ and assembling the matrix inequality (`gaussianFreeField_OS3_matrix_real`):

$$\sum_{ij} c_i c_j\  \mathrm{Re}\  Z[f_i - \Theta f_j] = \sum_{ij} y_i y_j\  E_{ij} = y^T E y \geq 0$$

The final theorem `gaussianFreeField_OS3_real` simply invokes this matrix result.

### Dependency chain

```
Level 0: Fourier analysis foundations
  heatKernel_eq_gaussianFT, s_integral_eval, gaussian_fourier_1d

Level 1: Mixed representation
  bessel_bilinear_eq_mixed_representation
  (chains through: bilinear_schwinger_eq_heatKernel
   -> heatKernel_bilinear_fourier_form -> laplace_s_integral_with_norm)

Level 2: Factorization
  factorization_to_squared_norm_direct
  rp_equals_squared_norm_integral

Level 3: Single-function RP
  freeCovariance_reflection_positive_direct (RPProof)
  -> freeCovariance_reflection_positive_bilinear (QFT)
  -> freeCovariance_reflection_positive_real

Level 4: Matrix infrastructure
  freeCovarianceFormR_reflection_matrix_posSemidef
  entrywiseExp_posSemidef_of_posSemidef (HadamardExp.lean)

Level 5: Gaussian factorization
  freeCovarianceFormR_reflection_expansion
  gaussianFreeField_real_entry_factor

Level 6: Master OS3
  gaussianFreeField_OS3_matrix_real
  gaussianFreeField_OS3_real
```

## References

- K. Osterwalder and R. Schrader, "Axioms for Euclidean Green's Functions I, II," *Comm. Math. Phys.* 31 (1973), 83--112; 42 (1975), 281--305.
- J. Glimm and A. Jaffe, *Quantum Physics: A Functional Integral Point of View*, 2nd ed., Springer, 1987.
- R.A. Horn and C.R. Johnson, *Matrix Analysis*, Cambridge University Press, 2013, Section 5.2 (Schur product theorem).
- G.B. Folland, *Introduction to Partial Differential Equations*, 2nd ed., Princeton University Press, 1995 (heat kernel and Schwinger representation).
