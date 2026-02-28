# OS1 Regularity

## Mathematical Background

OS1 (Regularity) establishes that the generating functional $Z[f]$ has controlled growth as a function of the test function $f$. This is critical for:

1. **Well-defined measures**: The field theory measure does not concentrate on wild configurations.
2. **Tempered distributions**: The Schwinger functions are tempered, not arbitrary generalized functions.
3. **OS reconstruction**: The exponential bound is a prerequisite for the Osterwalder-Schrader reconstruction theorem.

**Theorem (OS1).** There exist $p \in [1,2]$ and $c > 0$ such that for all $f \in \mathcal{S}(\mathbb{R}^4, \mathbb{C})$:

$$|Z[f]| \le \exp\left(c \cdot \left(\|f\|_{L^1} + \|f\|_{L^p}^p\right)\right)$$

When $p = 2$, the two-point Schwinger function $S_2(x)$ must be locally integrable.

For the GFF with mass $m > 0$, the proof establishes this with $p = 2$ and $c = 1/(2m^2)$.

## Proof Strategy

The proof has two parts:

**Part 1 (Exponential bound).** The GFF generating functional has the closed form $Z[f] = \exp(-\tfrac{1}{2}\langle f, Cf\rangle_{\mathbb{C}})$. The strategy is:
1. Use $|e^z| = e^{\mathrm{Re}(z)}$ to extract the norm.
2. Decompose $f = f_{\mathrm{re}} + if_{\mathrm{im}}$ and expand the bilinear form.
3. Use positive-definiteness of the covariance to bound $-\mathrm{Re}\langle f, Cf\rangle \le \langle f_{\mathrm{im}}, Cf_{\mathrm{im}}\rangle$.
4. Pass to momentum space where the propagator is diagonal: $\hat{C}(k) = 1/((2\pi)^2\|k\|^2 + m^2) \le 1/m^2$.
5. Apply Plancherel's theorem: $\langle f_{\mathrm{im}}, Cf_{\mathrm{im}}\rangle \le (1/m^2)\|f\|_{L^2}^2$.

**Part 2 (Local integrability).** The two-point function satisfies $|S_2(x)| \le C/\|x\|^2$ (from Bessel function asymptotics). Since $\|x\|^{-2}$ is locally integrable in 4 dimensions ($2 < 4$), local integrability follows.

**Literature**: Glimm-Jaffe Ch. 6  Peskin-Schroeder Appendix (propagator asymptotics).

## Key Declarations

| Declaration | Description |
|-------------|-------------|
| [`gaussianFreeField_satisfies_OS1_revised`](../OSforGFF/OS/OS1_Regularity.lean#L528) | Main theorem: GFF satisfies OS1 with $p=2$, $c=1/(2m^2)$ |
| [`fourier_plancherel_schwartz`](../OSforGFF/OS/OS1_Regularity.lean#L60) | $\lVert\hat{f}\rVert_{L^2} = \lVert f\rVert_{L^2}$ for Schwartz functions |
| [`SchwingerTwoPointFunction_GFF`](../OSforGFF/OS/OS1_Regularity.lean#L83) | $S_2^{\mathrm{GFF}}(x) := C_{\mathrm{free}}(x)$ |
| [`schwingerTwoPoint_eq_freeCovarianceKernel`](../OSforGFF/OS/OS1_Regularity.lean#L87) | $S_2^{\mathrm{GFF}}(x) = C_{\mathrm{free}}(m, x)$ (definitional) |
| [`schwingerTwoPointFunction_eq_GFF`](../OSforGFF/OS/OS1_Regularity.lean#L99) | Abstract $S_2(x) = S_2^{\mathrm{GFF}}(x)$ for $x \ne 0$ |
| [`schwinger_two_point_decay_bound_GFF`](../OSforGFF/OS/OS1_Regularity.lean#L145) | $\lvert S_2^{\mathrm{GFF}}(x-y)\rvert \le C\lVert x-y\rVert^{-2}$ |
| [`schwinger_two_point_decay_bound`](../OSforGFF/OS/OS1_Regularity.lean#L162) | $\lvert S_2(x-y)\rvert \le C\lVert x-y\rVert^{-2}$ |
| [`schwingerTwoPoint_measurable`](../OSforGFF/OS/OS1_Regularity.lean#L189) | $S_2$ is AE-strongly measurable |
| [`gff_generating_norm_eq`](../OSforGFF/OS/OS1_Regularity.lean#L219) | $\lvert Z[f]\rvert = \exp(-\tfrac{1}{2}\mathrm{Re}\langle f, Cf\rangle)$ |
| [`gff_generating_bound_by_imaginary`](../OSforGFF/OS/OS1_Regularity.lean#L229) | $\exp(-\tfrac{1}{2}\mathrm{Re}\langle f, Cf\rangle) \le \exp(\tfrac{1}{2}\langle f_{\mathrm{im}}, Cf_{\mathrm{im}}\rangle)$ |
| [`gff_generating_L2_bound`](../OSforGFF/OS/OS1_Regularity.lean#L468) | $\lvert Z[f]\rvert \le \exp((1/(2m^2))\lVert f\rVert_{L^2}^2)$ |

## Detailed Proof Outline

### Part 1: Exponential Bound

**Step 1: Norm via complex exponential.**
For the GFF, $Z[f] = \exp(-\tfrac{1}{2}\langle f, Cf\rangle_{\mathbb{C}})$. Taking norms:

$$|Z[f]| = |\exp(-\tfrac{1}{2}\langle f, Cf\rangle_{\mathbb{C}})| = \exp\left(-\tfrac{1}{2}\mathrm{Re}\langle f, Cf\rangle_{\mathbb{C}}\right)$$

This uses the identity $|e^z| = e^{\mathrm{Re}(z)}$ and the Gaussian structure of the GFF measure via `gff_complex_generating` and `gff_two_point_equals_covarianceℂ_free`.

**Lean lemma**: `gff_generating_norm_eq`

**Step 2: Bound by imaginary part.**
Decomposing $f = f_{\mathrm{re}} + if_{\mathrm{im}}$ and expanding the sesquilinear form via bilinearity (`freeCovarianceℂ_bilinear_add_left`, `freeCovarianceℂ_bilinear_add_right`, `freeCovarianceℂ_bilinear_smul_left`, `freeCovarianceℂ_bilinear_smul_right`):

$$\mathrm{Re}\langle f, Cf\rangle = \mathrm{Re}\langle f_{\mathrm{re}}, Cf_{\mathrm{re}}\rangle - \mathrm{Re}\langle f_{\mathrm{im}}, Cf_{\mathrm{im}}\rangle$$

The cross terms vanish because the covariance is real-valued and symmetric on real test functions (`freeCovarianceℂ_bilinear_agrees_on_reals`, `freeCovarianceℂ_bilinear_symm`). Since the covariance is positive semi-definite (`freeCovarianceℂ_positive`), $\mathrm{Re}\langle f_{\mathrm{re}}, Cf_{\mathrm{re}}\rangle \ge 0$, giving:

$$-\mathrm{Re}\langle f, Cf\rangle \le \mathrm{Re}\langle f_{\mathrm{im}}, Cf_{\mathrm{im}}\rangle$$

**Lean lemma**: `gff_generating_bound_by_imaginary`

**Step 3: Momentum space bound.**
In momentum space, the covariance becomes multiplicative:

$$\langle g, Cg\rangle = \int \frac{|\hat{g}(k)|^2}{(2\pi)^2 \|k\|^2 + m^2}\  dk$$

The free propagator satisfies the pointwise bound $1/((2\pi)^2\|k\|^2 + m^2) \le 1/m^2$. Therefore:

$$\langle g, Cg\rangle \le \frac{1}{m^2} \int |\hat{g}(k)|^2\  dk = \frac{1}{m^2}\|g\|_{L^2}^2$$

where the last equality is the Plancherel theorem (`fourier_plancherel_schwartz`). The connection between position-space and momentum-space representations uses the Parseval identity (`parseval_covariance_schwartz_bessel` from `Covariance/RealForm.lean`).

Since $\|f_{\mathrm{im}}\|_{L^2} \le \|f\|_{L^2}$ pointwise ($|f_{\mathrm{im}}(x)| \le |f(x)|$), combining gives:

$$|Z[f]| \le \exp\left(\frac{1}{2m^2}\|f\|_{L^2}^2\right)$$

**Lean lemma**: `gff_generating_L2_bound`

**Step 4: Add $L^1$ term.**
Since $\|f\|_{L^1} \ge 0$, the $L^2$ bound is strengthened to match the OS1 form:

$$|Z[f]| \le \exp\left(\frac{1}{2m^2}\left(\|f\|_{L^1} + \|f\|_{L^2}^2\right)\right)$$

### Part 2: Two-Point Local Integrability

**Step 5: Decay bound.**
The GFF two-point function is $S_2^{\mathrm{GFF}}(x) = C_{\mathrm{free}}(x) = (m/(4\pi^2\|x\|))K_1(m\|x\|)$, where $K_1$ is the modified Bessel function of the second kind.

From Bessel function asymptotics ($K_1(z) \sim 1/z$ near the origin, exponential decay at infinity), there exists $C > 0$ such that $|S_2(x-y)| \le C\|x-y\|^{-2}$ for all $x, y$. This is proved in `schwinger_two_point_decay_bound_GFF` using `freeCovarianceKernel_decay_bound` from `Covariance/Momentum.lean`, which relies on `besselK1_near_origin_bound` and `besselK1_asymptotic`.

**Lean theorem**: `schwinger_two_point_decay_bound`

**Step 6: Local integrability in 4D.**
In $d$ dimensions, $\|x\|^{-\alpha}$ is locally integrable if and only if $\alpha < d$. For $d = 4$ and $\alpha = 2$, the function $\|x\|^{-2}$ is locally integrable:

$$\int_{\|x\| < R} \|x\|^{-2}\  dx = |S^3| \cdot \int_0^R r^{-2} \cdot r^3\  dr = 2\pi^2 \cdot R^2/2 < \infty$$

Combined with the decay bound and measurability (`schwingerTwoPoint_measurable`), this establishes `TwoPointIntegrable`.

**Step 7: Final assembly.**
`gaussianFreeField_satisfies_OS1_revised` witnesses the existential with $p = 2$, $c = 1/(2m^2)$, verifies $1 \le 2$, $2 \le 2$, $c > 0$, and provides both the exponential bound and the conditional two-point integrability.

### Axioms Used

The proof has 0 project-specific axioms. The decay bound and measurability, which were formerly axioms, are now proved theorems. The decay bound is derived from Bessel function analysis in `Covariance/Momentum.lean`. Measurability follows from the agreement with the free covariance kernel (which is integrable, hence AE-strongly measurable).

## References

- J. Glimm and A. Jaffe, *Quantum Physics*, Springer, 2nd ed., Ch. 6.
- M. E. Peskin and D. V. Schroeder, *An Introduction to Quantum Field Theory*, Addison-Wesley, 1995, Appendix (propagator in position space).
- G. N. Watson, *A Treatise on the Theory of Bessel Functions*, Cambridge, 2nd ed., 1944 (Bessel function asymptotics).
- E. M. Stein and G. Weiss, *Introduction to Fourier Analysis on Euclidean Spaces*, Princeton, 1971 (Plancherel theorem).
