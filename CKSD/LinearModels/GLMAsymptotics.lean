module

public import CKSD.LinearModels.GLMAsymptotics.Basic
public import CKSD.LinearModels.GLMAsymptotics.Asymptotics

/-!
# Asymptotics of the generalised linear model with canonical link

An exponential dispersion law with cumulant function `b` and dispersion `φ > 0` has density
`exp((yθ - b θ) / φ)` with respect to a dominating measure `ν` on `ℝ` (the factor `exp c(y, φ)`
is absorbed into `ν`). In the canonical-link model the natural parameter of the response is the
linear predictor `θ = ⟪x, β⟫`, so the mean is `b'(⟪x, β⟫)`, the variance is `φ b''(⟪x, β⟫)`,
the weight is `w(x) = b''(⟪x, β⟫)`, and the likelihood equations are
`∑ᵢ xᵢ (Yᵢ - b'(⟪xᵢ, β⟫)) = 0`.

The deviance proof whitens the information matrix and applies the convex minimum-value
and Gaussian projection results in `CKSD.LinearModels.ConvexLikelihood`.

The pairs `(xᵢ, Yᵢ)` are independent and identically distributed; the conditional law of the
response given the covariate is supplied by a Markov kernel.

## Main definitions

* `CKSD.exponentialDispersionLaw`: the law `exp((yθ - b θ) / φ) ν(dy)`.
* `CKSD.canonicalGLMInformation`: `J = E[x xᵀ b''(⟪x, β⟫)]`.
* `CKSD.canonicalGLMLogLikelihood`, `CKSD.IsCanonicalGLMRoot`: the log likelihood and the
  likelihood equations of the first `n` observations.

## Main results

* `CKSD.tendsto_in_distribution_canonical_glm_root`: asymptotic normality
  `√n (β̂ - β) ⇒ N(0, φ J⁻¹)` of roots of the likelihood equations, and its studentized form.
* `CKSD.tendsto_in_distribution_canonical_glm_deviance`: the deviance difference of nested
  models is asymptotically chi-squared.

## References

* P. McCullagh and J. A. Nelder, *Generalized Linear Models*, 2nd ed., Chapman and Hall, 1989.
* L. Fahrmeir and H. Kaufmann, *Consistency and asymptotic normality of the maximum likelihood
  estimator in generalized linear models*, Ann. Statist. 13 (1985).
-/
