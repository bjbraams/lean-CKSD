# Synopsis: Asymptotic statistics

Part of the [mathematical synopsis series](SYNOPSIS.md).
[Bibliographical scope and references](CKSD-bib.md#cks-103).

This synopsis follows Section 103. Subdivision 103A is the first-order
asymptotic theory of parametric experiments. Subdivision 103B is the
higher-order, resampling, and information-geometric refinement that recurs
in the same sources. Weak convergence, Slutsky's theorem, the
continuous-mapping theorem, and the empirical distribution function are
[CKMA SYNOPSIS06](../lean-CKMA/SYNOPSIS06.md), items 15, 16, 58, and 59.
Uniform entropy and bracketing criteria for Donsker classes are
[CKMA SYNOPSIS07](../lean-CKMA/SYNOPSIS07.md), items 40 and 41. The
Berry–Esseen bound is CKMA SYNOPSIS06, item 36. Semiparametric efficiency
and nonparametric rates are in Section 104.

Observations $X_1,\ldots,X_n$ are independent with common law $P_\theta$ unless
a statement says otherwise. Write $\ell_n$ for the log-likelihood and
$I(\theta)$ for the Fisher information matrix of one observation, as in
SYNOPSIS101. A sequence of estimators $\hat\theta_n$ is **consistent** when
$\hat\theta_n\to\theta$ in $P_\theta$-probability, and **asymptotically
normal** when $\sqrt n\,(\hat\theta_n-\theta)$ converges in distribution under
$P_\theta$.

Numbered definitions and results have stable identifiers. Additions take the
next free number and are placed beside related material; numbers need not
increase in reading order. Proofs are outside the scope of this synopsis.

<a id="synopsis-103a"></a>

## 103A. First-Order Asymptotics, Statistical Experiments, and Empirical Processes

### Parametric estimators and tests

* **1. Delta method.** Let $T_n$ be a random vector in $\mathbb R^k$ with
  $\sqrt n\,(T_n-\theta)\Rightarrow N(0,\Sigma)$, and let
  $g:\mathbb R^k\to\mathbb R^m$ be differentiable at $\theta$. Then
  $$\sqrt n\,\bigl(g(T_n)-g(\theta)\bigr)
  \Rightarrow N\bigl(0,\,Dg(\theta)\,\Sigma\,Dg(\theta)^\top\bigr).$$
  The same expansion holds with convergence in probability of the linear
  approximation when $g$ is continuously differentiable in a neighborhood
  of $\theta$.

* **2. Consistency of maximum likelihood.** Let $\Theta$ be a compact metric
  space and let $\theta\mapsto\log f(x\mid\theta)$ be continuous for almost
  every $x$. Suppose $\theta_0$ is the unique maximizer of
  $\theta\mapsto\mathbb E_{\theta_0}\log f(X\mid\theta)$, the expectation
  being allowed to take the value $-\infty$, and suppose the supremum of the
  log-likelihood over each closed set not containing $\theta_0$ satisfies a
  uniform strong law. Then every approximate maximizer $\hat\theta_n$ of the
  likelihood converges to $\theta_0$ almost surely under $P_{\theta_0}$.
  Identifiability and a $\theta_0$-integrable envelope of
  $|\log f(X\mid\theta)|$ give the unique-maximum and uniform-law
  hypotheses for a dominated model with a common support.

* **3. Asymptotic normality of maximum likelihood.** Let $\theta$ lie in the
  interior of an open subset of $\mathbb R^k$. Assume a dominated model with
  support free of $\theta$, nonsingular and continuous information $I(\theta)$,
  and enough domination of the second or third derivatives of the
  log-density to expand the score in a neighborhood of $\theta$. If
  $\hat\theta_n$ is a consistent root of the score equation
  $\nabla\ell_n(\theta)=0$, then
  $$\sqrt n\,(\hat\theta_n-\theta)\Rightarrow N\bigl(0,I(\theta)^{-1}\bigr)$$
  under $P_\theta$. When $\theta$ is interior, the differentiability hypotheses
  hold, and a global maximizer is consistent, that maximizer is such a root
  with probability tending to one. A single Newton step from any
  $\sqrt n$-consistent preliminary estimator has the same limit.

* **4. Z-estimators.** Let $\psi_\theta(x)$ take values in $\mathbb R^k$, write
  $\Psi(\theta)=\mathbb E_{\theta_0}\psi_\theta(X)$ and
  $\Psi_n(\theta)=n^{-1}\sum_{i=1}^n\psi_\theta(X_i)$, and suppose
  $\Psi(\theta_0)=0$. If $\Psi$ is differentiable at $\theta_0$ with
  nonsingular derivative $V$, a Lipschitz or stochastic-equicontinuity
  condition holds in a neighborhood of $\theta_0$, and $\hat\theta_n$ is a
  consistent solution of $\Psi_n(\hat\theta_n)=0$, then
  $$\sqrt n\,(\hat\theta_n-\theta_0)
  =-V^{-1}\sqrt n\,\Psi_n(\theta_0)+o_P(1).$$
  When $\psi_{\theta_0}(X)$ has finite covariance $\Sigma$, the limit law is
  $N(0,V^{-1}\Sigma(V^{-1})^\top)$. Maximum likelihood is the case
  $\psi_\theta=\nabla_\theta\log f(\cdot\mid\theta)$, for which $V=-I(\theta_0)$
  and $\Sigma=I(\theta_0)$.

* **36. One-step estimators.** Let $\Psi_n$ be random estimating functions
  with $\sqrt n\,\Psi_n(\theta_0)\Rightarrow Z$, and suppose that for a
  nonsingular matrix $V$ and every $M<\infty$
  $$\sup_{\sqrt n\|\theta-\theta_0\|\le M}
  \bigl\|\sqrt n\bigl(\Psi_n(\theta)-\Psi_n(\theta_0)\bigr)
  -V\sqrt n(\theta-\theta_0)\bigr\|\to_P0.$$
  Let $\tilde\theta_n$ be **$\sqrt n$-consistent**, meaning that
  $\sqrt n(\tilde\theta_n-\theta_0)$ is uniformly tight, and let $\hat V_n$ be
  nonsingular random matrices with $\hat V_n\to_P V$. Then the one-step
  estimator $\hat\theta_n=\tilde\theta_n-\hat V_n^{-1}\Psi_n(\tilde\theta_n)$
  satisfies
  $$\sqrt n(\hat\theta_n-\theta_0)
  =-V^{-1}\sqrt n\,\Psi_n(\theta_0)+o_P(1)\Rightarrow -V^{-1}Z.$$
  The displayed uniformity holds under the conditions of item 4 for
  $\Psi_n=n^{-1}\sum_i\psi_\theta(X_i)$. With the likelihood score and
  $\hat V_n$ the negative observed or estimated Fisher information, the
  one-step estimator has the efficient limit of item 3 even where the
  likelihood equation has several roots or its global maximizer is
  inconsistent; further Newton steps do not change the limit law. If the
  preliminary estimator is discretized to the grid $n^{-1/2}\mathbb Z^k$,
  it suffices that the displayed approximation hold along every
  deterministic sequence $\theta_n=\theta_0+O(n^{-1/2})$; for a model
  differentiable in quadratic mean this reduces to an $L^2$-continuity
  condition on $\psi_\theta\sqrt{p_\theta}$.

* **5. Sample quantiles.** Let $F$ be differentiable at its quantile
  $q=F^{-1}(p)$, with $0<p<1$ and density $f(q)>0$, and let $F$ be strictly
  increasing in a neighborhood of $q$. If $F_n^{-1}(p)$ is a sample
  $p$-quantile, then
  $$\sqrt n\,\bigl(F_n^{-1}(p)-q\bigr)
  \Rightarrow N\Bigl(0,\frac{p(1-p)}{f(q)^2}\Bigr).$$

* **33. Bahadur representation of sample quantiles.** Let $0<p<1$, let
  $F_n^{-1}(p)=\inf\{x:F_n(x)\ge p\}$, and let $F$ be differentiable at
  $\xi_p=F^{-1}(p)$ with $f(\xi_p)=F'(\xi_p)>0$. Then
  $$F_n^{-1}(p)=\xi_p+\frac{p-F_n(\xi_p)}{f(\xi_p)}+R_n,
  \qquad \sqrt n\,R_n\to_P0.$$
  Hence finitely many sample quantiles are jointly asymptotically normal,
  with asymptotic covariance
  $(p\wedge p'-pp')/\bigl(f(\xi_p)f(\xi_{p'})\bigr)$ between the
  $p$- and $p'$-quantiles. If $F$ is moreover twice differentiable at
  $\xi_p$, the Bahadur–Kiefer theorem gives the exact almost-sure order of
  the remainder:
  $$\limsup_{n\to\infty}\frac{n^{3/4}|R_n|}{(\log\log n)^{3/4}}
  =\frac{\bigl(32\,p(1-p)/27\bigr)^{1/4}}{f(\xi_p)}
  \quad\text{almost surely.}$$
  Thus the linearization error is of order $n^{-3/4}$ up to a logarithmic
  factor, not merely $o(n^{-1/2})$.

* **6. Nondegenerate U-statistics.** Let $h$ be a symmetric kernel of order
  $m\ge 1$ with $\mathbb E h(X_1,\ldots,X_m)^2<\infty$, and let $U_n$ be the
  average of $h$ over the $\binom{n}{m}$ subsamples. Set
  $\theta=\mathbb E h$ and
  $g(x)=\mathbb E[h(x,X_2,\ldots,X_m)]-\theta$. If
  $\zeta_1=\mathop{\mathrm{Var}} g(X_1)>0$, then
  $$\sqrt n\,(U_n-\theta)\Rightarrow N(0,m^2\zeta_1).$$
  The projection $n^{-1}\sum_{i=1}^n m g(X_i)$ is the Hájek projection of
  $U_n-\theta$ and accounts for the limit.

Let $X_1,\ldots,X_n$ be independent and let $T$ be a square-integrable
statistic. The **Hájek projection** of $T$ is its $L^2$-projection onto the
linear space of sums $\sum_{i=1}^n g_i(X_i)$ with square-integrable
$g_i(X_i)$; it equals
$$\hat T=\sum_{i=1}^n\mathbb E(T\mid X_i)-(n-1)\,\mathbb ET.$$

* **35. Hájek projection.** Let $T_n$ be square-integrable statistics of
  independent observations, with Hájek projections $\hat T_n$. If
  $\mathop{\mathrm{Var}}T_n/\mathop{\mathrm{Var}}\hat T_n\to1$, then
  $$\frac{T_n-\mathbb ET_n}{(\mathop{\mathrm{Var}}T_n)^{1/2}}
  -\frac{\hat T_n-\mathbb E\hat T_n}{(\mathop{\mathrm{Var}}\hat T_n)^{1/2}}
  \to0$$
  in $L^2$, hence in probability. Because $\hat T_n$ is a sum of independent
  terms, the Lindeberg–Feller theorem (CKMA SYNOPSIS06, item 34) then gives
  the asymptotic normality of $T_n$. The same conclusion holds for the
  projection onto any closed linear space containing the constants. Items 6
  and 34 and the linear rank statistics of SYNOPSIS104, item 2, are
  obtained this way.

An **$L$-statistic** is a linear combination of the order statistics
$X_{n(1)}\le\cdots\le X_{n(n)}$. For $0<\alpha<1/2$ the **$\alpha$-trimmed
mean** $T_n$ is the average of the $X_{n(i)}$ with
$\lfloor\alpha n\rfloor<i\le n-\lfloor\alpha n\rfloor$.

* **34. Asymptotic normality of $L$-statistics.** Let $\mathbb EX_1^2<\infty$,
  let $\phi$ be a bounded function on $(0,1)$ that is continuous at $F(y)$ for
  Lebesgue-almost every $y$, and let
  $L_n=n^{-1}\sum_{i=1}^n\phi\bigl(i/(n+1)\bigr)X_{n(i)}$. Then
  $\sqrt n\,(L_n-\mathbb EL_n)\Rightarrow N\bigl(0,\sigma^2(\phi,F)\bigr)$,
  where
  $$\sigma^2(\phi,F)=\iint\phi\bigl(F(x)\bigr)\phi\bigl(F(y)\bigr)
  \bigl(F(x\wedge y)-F(x)F(y)\bigr)\,dx\,dy.$$
  For the $\alpha$-trimmed mean no moment condition is needed: if the set
  $\{x:F(x)\in\{\alpha,1-\alpha\}\}$ has Lebesgue measure zero, then with
  $\mu_\alpha=(1-2\alpha)^{-1}\int_\alpha^{1-\alpha}F^{-1}(u)\,du$, $a=F^{-1}(\alpha)$,
  and $b=F^{-1}(1-\alpha)$,
  $$\sqrt n\,(T_n-\mu_\alpha)\Rightarrow
  N\Bigl(0,\frac1{(1-2\alpha)^2}\int_a^b\!\!\int_a^b
  \bigl(F(x\wedge y)-F(x)F(y)\bigr)\,dx\,dy\Bigr).$$
  The double integral is the variance of $X_1$ clipped to $[a,b]$; for $F$
  symmetric about $0$ the asymptotic variance is
  $(1-2\alpha)^{-2}\bigl(\int_{-b}^{b}x^2\,dF(x)+2\alpha b^2\bigr)$. The robustness
  interpretation of trimming is in SYNOPSIS104C.

* **7. Likelihood-ratio, Wald, and score tests.** Consider testing a smooth
  hypothesis of codimension $q$ in a regular parametric model of dimension
  $k$, with the null value an interior point at which $I(\theta)$ is
  nonsingular and the null can be written locally as $q$ independent
  constraints. Let $\lambda_n$ be twice the difference of the maximized
  log-likelihoods, let $W_n$ be the Wald quadratic form in the unconstrained
  estimator and its information, and let $S_n$ be the quadratic form in the
  score at the restricted estimator. Under the null,
  $\lambda_n$, $W_n$, and $S_n$ each converge in distribution to $\chi^2_q$,
  and the three statistics differ by $o_P(1)$. Under the local alternatives
  of item 9 the common limit is noncentral chi-squared, with noncentrality
  parameter determined by the Fisher information on the local parameter.

### Limits of experiments

A sequence of probability measures $Q_n$ is **contiguous** to $P_n$ when
$P_n(A_n)\to 0$ implies $Q_n(A_n)\to 0$. The sequence of experiments is
**locally asymptotically normal** at $\theta$, with nonsingular information
$I(\theta)$ and central sequence $\Delta_n$, when for every local parameter
$h$
$$\log\frac{dP_{\theta+h/\sqrt n}^{\,n}}{dP_\theta^{\,n}}
=h\cdot\Delta_n-\tfrac12 h^\top I(\theta)\,h+o_{P_\theta}(1)$$
and $\Delta_n\Rightarrow N(0,I(\theta))$ under $P_\theta$. An estimator
sequence $T_n$ is **regular** at $\theta$ when, for every $h$, the law of
$\sqrt n\,(T_n-\theta-h/\sqrt n)$ under $P_{\theta+h/\sqrt n}$ converges to a
limit that does not depend on $h$.

* **8. Contiguity.** If the log-likelihood ratio $\Lambda_n$ of $Q_n$ with
  respect to $P_n$ converges in distribution under $P_n$ to a random
  variable $\Lambda$ with $\mathbb E e^{\Lambda}=1$, then $Q_n$ is
  contiguous to $P_n$. In particular, local alternatives in a locally
  asymptotically normal experiment are mutually contiguous.

* **9. Local asymptotic normality of smooth models.** Assume independent
  sampling from a dominated model that is differentiable in quadratic mean
  at an interior point $\theta$, with nonsingular Fisher information
  $I(\theta)$. Then the product experiments are locally asymptotically normal
  with central sequence equal to the normalized score
  $n^{-1/2}\sum_{i=1}^n\nabla\log f(X_i\mid\theta)$.
  Quadratic-mean differentiability means that for a score
  $\dot\ell_\theta\in L^2(P_\theta)$,
  $$\int\left(\sqrt{p_{\theta+h}}-\sqrt{p_\theta}
  -\tfrac12h^\top\dot\ell_\theta\sqrt{p_\theta}\right)^2d\mu
  =o(\|h\|^2).$$
  It is a square-root-density condition and need not imply a KL expansion.
  If the support is common and the first two $h$-derivatives of
  $p_{\theta+h}\log(p_{\theta+h}/p_\theta)$ admit a common integrable
  bound locally, differentiation under the integral also gives
  $$D(P_{\theta+h}\|P_\theta)=\tfrac12 h^\top I(\theta)h+o(\|h\|^2).$$

* **10. Le Cam's third lemma.** Suppose that under $P_n$ the pair
  $(S_n,\Lambda_n)$ converges to a normal law whose second margin is
  $N(-\sigma^2/2,\sigma^2)$ and whose cross-covariance is $\tau$. If $Q_n$
  has log-likelihood ratio $\Lambda_n$ against $P_n$, then under $Q_n$ the
  sequence $S_n$ converges to the normal law with the same covariance and
  with mean shifted by $\tau$. In a locally asymptotically normal
  experiment the central sequence itself shifts by $I(\theta)h$ under the
  local alternative $\theta+h/\sqrt n$.

A **randomized statistic** in an experiment with observation $X$ is a
measurable function $T(X,U)$, where $U$ is uniform on $[0,1]$ and independent
of $X$.

* **37. Asymptotic representation theorem.** Let the model be
  differentiable in quadratic mean at an interior point $\theta$ with
  nonsingular information $I(\theta)$, and let $T_n$ be statistics based on
  $n$ observations such that, for every $h\in\mathbb R^k$, $T_n$ converges in
  distribution under $P_{\theta+h/\sqrt n}^{\,n}$ to a law $L_h$. Then there is
  a randomized statistic $T$ in the Gaussian shift experiment of observing
  a single $X\sim N\bigl(h,I(\theta)^{-1}\bigr)$, $h\in\mathbb R^k$, such that
  $T$ has law $L_h$ for every $h$. For estimators of a differentiable
  $\psi(\theta)$ with $\sqrt n\bigl(T_n-\psi(\theta+h/\sqrt n)\bigr)$
  converging to $L_{\theta,h}$ under every $h$, there is such a $T$ with
  $T-\dot\psi_\theta h$ distributed as $L_{\theta,h}$. Thus every attainable
  local limit behavior is that of a procedure in the limiting Gaussian
  experiment, and items 11 and 12 follow from the corresponding exact
  statements for that experiment, Anderson's lemma among them.

* **11. Convolution theorem.** In a locally asymptotically normal experiment
  with information $I(\theta)$, the limit law $L$ of a regular estimator
  sequence is the convolution of $N(0,I(\theta)^{-1})$ with some probability
  measure on $\mathbb R^k$. If the limiting law has finite covariance,
  that covariance is at least $I(\theta)^{-1}$ in the Loewner order.
  Convergence of scaled finite-sample covariances requires additional
  moment control. The maximum likelihood estimator of item 3 is regular
  and has the normal factor as its
  limit law.

* **12. Local asymptotic minimax theorem.** Let $\ell$ be a nonnegative
  lower-semicontinuous bowl-shaped loss on $\mathbb R^k$: its sublevel
  sets are convex and symmetric about zero. For any estimator sequence $T_n$ in a locally
  asymptotically normal experiment,
  $$\lim_{c\to\infty}\liminf_{n\to\infty}
  \sup_{\|h\|\le c}
  \mathbb E_{\theta+h/\sqrt n}\,
  \ell\bigl(\sqrt n\,(T_n-\theta-h/\sqrt n)\bigr)
  \ge\int\ell\,dN\bigl(0,I(\theta)^{-1}\bigr).$$
  The maximum likelihood estimator attains the bound for bounded continuous
  bowl-shaped losses, and for squared error under uniform integrability.

* **13. Superefficiency.** Let $X_1,\ldots,X_n$ be independent
  $N(\theta,1)$ and set $\hat\theta_n=\bar X$ when $|\bar X|\ge n^{-1/4}$ and
  $\hat\theta_n=0$ otherwise. Then $\sqrt n\,(\hat\theta_n-\theta)$ converges
  to $N(0,1)$ for $\theta\neq 0$ and converges to $0$ for $\theta=0$, so the
  asymptotic variance at $0$ is smaller than the information bound. The
  estimator is not regular at $0$, and the convergence of risks is not
  uniform in shrinking neighborhoods of $0$. In a regular parametric model
  the set of parameter points at which any given estimator sequence is
  superefficient has Lebesgue measure zero.

### Local tests and asymptotic relative efficiency

For a test $\phi_n$ based on $n$ observations the **power function** is
$\pi_n(\theta)=\mathbb E_\theta\phi_n$. Write $z_\alpha$ for the upper
$\alpha$-quantile of the standard normal law, $1-\Phi(z_\alpha)=\alpha$.

* **40. Asymptotic power envelope.** Let the model be differentiable in
  quadratic mean at an interior point $\theta_0$ with nonsingular
  information $I=I(\theta_0)$, and let $\psi:\Theta\to\mathbb R$ be
  differentiable at $\theta_0$ with $\psi(\theta_0)=0$ and nonzero gradient
  $\dot\psi$. For every sequence of level-$\alpha$ tests of
  $H_0:\psi(\theta)\le0$ against $H_1:\psi(\theta)>0$ and every $h$ with
  $\dot\psi h>0$,
  $$\limsup_{n\to\infty}\pi_n(\theta_0+h/\sqrt n)\le
  1-\Phi\Bigl(z_\alpha-\frac{\dot\psi h}
  {(\dot\psi I^{-1}\dot\psi^\top)^{1/2}}\Bigr).$$
  The bound is attained for every $h$ by the tests that reject when
  $T_n\ge z_\alpha$, whenever under $P_{\theta_0}$
  $$T_n=\frac{\dot\psi I^{-1}\Delta_n}{(\dot\psi I^{-1}\dot\psi^\top)^{1/2}}
  +o_P(1),$$
  with $\Delta_n$ the normalized score of item 9. The Wald statistic
  $\sqrt n\,\psi(\hat\theta_n)/(\dot\psi I^{-1}\dot\psi^\top)^{1/2}$ built on an
  efficient estimator satisfies this, and so, under the regularity of
  item 7, do the corresponding score and signed likelihood-ratio
  statistics. For a scalar parameter and
  $\psi(\theta)=\theta-\theta_0$ the envelope is
  $1-\Phi\bigl(z_\alpha-hI^{1/2}\bigr)$.

The local parameter sets at a null point $\theta\in\Theta_0$ are
$H_n=\sqrt n(\Theta-\theta)$ and $H_{n,0}=\sqrt n(\Theta_0-\theta)$. They
**converge** to $H$ and $H_0$ when $H$ is the set of limits of convergent
sequences $h_n\in H_n$ and also contains every limit of a convergent
subsequence $h_{n_i}\in H_{n_i}$, and likewise for $H_0$.

* **41. Likelihood ratio on general local parameter sets.** Let the model be
  differentiable in quadratic mean at $\theta\in\Theta_0$ with nonsingular
  information $I$, and let
  $|\log p_{\theta_1}(x)-\log p_{\theta_2}(x)|\le\dot\ell(x)\|\theta_1-\theta_2\|$
  for $\theta_1,\theta_2$ near $\theta$ with $P_\theta\dot\ell^2<\infty$.
  Suppose the maximum likelihood estimators over $\Theta_0$ and over
  $\Theta$ are consistent and $H_n\to H$, $H_{n,0}\to H_0$. Then, under
  $P_{\theta+h/\sqrt n}$, the likelihood-ratio statistic $\lambda_n$ of
  item 7 converges in distribution to
  $$\inf_{g\in H_0}\|I^{1/2}(X-g)\|^2-\inf_{g\in H}\|I^{1/2}(X-g)\|^2,
  \qquad X\sim N(h,I^{-1}).$$
  If $\theta$ is interior and $H_0$ is a linear subspace of dimension $l$,
  the null limit is $\chi^2_{k-l}$, as in item 7. If the local sets are
  polyhedral cones, the null limit is the chi-bar-squared law of
  SYNOPSIS104, item 12. For a scalar parameter with $\Theta=[0,\infty)$ and
  $H_0:\theta=0$ the null limit is the mixture
  $\tfrac12\delta_0+\tfrac12\chi^2_1$, as in tests that a variance
  component vanishes.

Consider tests of $H_0:\theta=0$ against $\theta>0$. Given
$0<\alpha<\gamma<1$ and alternatives $\theta_\nu\downarrow0$, let
$n_{\nu,i}$ be the least sample size for which the $i$th sequence of tests
has level at most $\alpha$ and power at least $\gamma$ at $\theta_\nu$. When
it exists, $\lim_\nu n_{\nu,2}/n_{\nu,1}$ is the **Pitman asymptotic
relative efficiency** of the first sequence with respect to the second.
Test statistics $T_n$ are **locally uniformly asymptotically normal** with
functions $\mu$ and $\sigma$ if
$\sqrt n\bigl(T_n-\mu(\theta_n)\bigr)/\sigma(\theta_n)\Rightarrow N(0,1)$
under $\theta_n$ for every sequence $\theta_n\downarrow0$. The **slope** of the
tests that reject for large $T_n$ is $\mu'(0)/\sigma(0)$, and its square is the
**efficacy**.

* **42. Pitman efficiency and Noether's theorem.** Suppose that, for each
  $n$, $P_{n,\theta}\to P_{n,0}$ in total variation as $\theta\to0$. Let
  $T_{n,1}$ and $T_{n,2}$ be locally uniformly asymptotically normal with
  $\mu_i$ differentiable at $0$, $\mu_i'(0)>0$, and $\sigma_i$ continuous at
  $0$ with $\sigma_i(0)>0$. The tests rejecting when
  $\sqrt n\bigl(T_{n,i}-\mu_i(0)\bigr)>\sigma_i(0)z_\alpha$ have asymptotic
  level $\alpha$ and local power
  $$\pi_{n,i}(h/\sqrt n)\to1-\Phi\bigl(z_\alpha-h\,\mu_i'(0)/\sigma_i(0)\bigr),$$
  and their Pitman relative efficiency is the ratio of efficacies
  $$\frac{\bigl(\mu_1'(0)/\sigma_1(0)\bigr)^2}{\bigl(\mu_2'(0)/\sigma_2(0)\bigr)^2},$$
  for every $\alpha$, $\gamma$, and sequence $\theta_\nu\downarrow0$. If the
  power functions are nondecreasing, asymptotic normality along
  sequences $\theta_n=O(n^{-1/2})$ suffices. In location problems the
  efficacy of a test is often the reciprocal asymptotic variance of an
  associated estimator: the sign test and the median, the Wilcoxon
  signed-rank test and the Hodges–Lehmann estimator of SYNOPSIS104,
  item 3.

* **43. Efficiencies of the sign, Wilcoxon, and $t$ tests.** Let the
  observations have density $f(x-\theta)$ with $f$ symmetric about $0$,
  finite variance $\sigma^2$, $f$ continuous at $0$ with $f(0)>0$, and
  $\int f^2<\infty$. For $H_0:\theta=0$ against $\theta>0$ the efficacies of
  the $t$ test, the sign test, and the Wilcoxon signed-rank test are
  $1/\sigma^2$, $4f(0)^2$, and $12\bigl(\int f^2\bigr)^2$, so
  $$e_{S,t}=4\sigma^2f(0)^2,\qquad
  e_{W,t}=12\sigma^2\Bigl(\int f^2\Bigr)^2,\qquad
  e_{S,W}=\frac{f(0)^2}{3\bigl(\int f^2\bigr)^2}.$$
  At the normal law $e_{S,t}=2/\pi\approx0.637$ and
  $e_{W,t}=3/\pi\approx0.955$; at the Laplace law they are $2$ and $3/2$;
  at the uniform law $1/3$ and $1$; at the logistic law $\pi^2/12$ and
  $\pi^2/9$. Over all such $f$,
  $$e_{W,t}\ge\frac{108}{125}=0.864,$$
  the minimum being attained by the scale family of the density
  proportional to $(1-x^2)\vee0$, while $e_{W,t}$ is unbounded above. Among symmetric
  unimodal $f$, $e_{S,t}\ge1/3$, with equality for the uniform law. In the
  two-sample shift model $G(x)=F(x-\theta)$ the efficiency of the
  Wilcoxon–Mann–Whitney test relative to the two-sample $t$ test is given by
  the same formula for $e_{W,t}$, without symmetry of $f$, and obeys the same
  bound. The tests themselves are SYNOPSIS104, items 2, 22, and 23;
  optimal rank scores are SYNOPSIS104, items 32 and 33.

### General criteria, moment methods, and nonlinear limits

For a measurable criterion $m_\theta$, an **$M$-estimator** approximately
maximizes $P_nm_\theta=n^{-1}\sum_i m_\theta(X_i)$. The law $P$ in this
paragraph need not belong to a parametric model.

* **23. Consistency of $M$-estimators.** Suppose
  $\sup_{\theta\in\Theta}|P_nm_\theta-Pm_\theta|\to_P0$ and the population
  maximum is separated: for every $\varepsilon>0$,
  $$\sup_{d(\theta,\theta_0)\ge\varepsilon}Pm_\theta<Pm_{\theta_0}.$$
  If $P_nm_{\hat\theta_n}\ge\sup_\theta P_nm_\theta-o_P(1)$, then
  $\hat\theta_n\to_P\theta_0$. Compactness, almost-sure continuity in
  $\theta$, and an integrable envelope are a useful sufficient condition
  for the uniform law. The separation condition also applies on
  noncompact spaces.

* **38. Asymptotic normality of $M$-estimators.** Let $\Theta$ be open in
  $\mathbb R^k$. Suppose $\theta\mapsto m_\theta(x)$ is differentiable at
  $\theta_0$ for $P$-almost every $x$, with derivative $\dot m_{\theta_0}(x)$,
  and that there is a function $\dot m$ with $P\dot m^2<\infty$ such that
  $$|m_{\theta_1}(x)-m_{\theta_2}(x)|\le\dot m(x)\,\|\theta_1-\theta_2\|$$
  for all $\theta_1,\theta_2$ in a neighborhood of $\theta_0$. Suppose
  $\theta\mapsto Pm_\theta$ has a second-order Taylor expansion at a point of
  maximum $\theta_0$ with nonsingular symmetric second derivative $V$. If
  $P_nm_{\hat\theta_n}\ge\sup_\theta P_nm_\theta-o_P(n^{-1})$ and
  $\hat\theta_n\to_P\theta_0$, then
  $$\sqrt n(\hat\theta_n-\theta_0)
  =-V^{-1}\frac1{\sqrt n}\sum_{i=1}^n\dot m_{\theta_0}(X_i)+o_P(1)
  \Rightarrow N\bigl(0,V^{-1}P[\dot m_{\theta_0}\dot m_{\theta_0}^{\top}]V^{-1}\bigr).$$
  Only the population criterion needs two derivatives. For the median,
  $m_\theta(x)=|x|-|x-\theta|$ gives $V=-2f(\theta_0)$ and recovers item 5 at
  $p=1/2$. Items 3 and 24 are the case $m_\theta=\log p_\theta$.

Let $M_n$ be random criterion functions and $M$ a deterministic function on
a semimetric space $(\Theta,d)$, with $\theta_0$ a point of maximum of $M$.
In the next item $\mathbb E^*$ is outer expectation, which avoids
measurability questions for suprema.

* **39. Rate of convergence of $M$-estimators.** Suppose
  $M(\theta)-M(\theta_0)\le-c\,d(\theta,\theta_0)^2$ for $\theta$ near
  $\theta_0$, with $c>0$. Suppose that for every $n$ and all sufficiently
  small $\delta>0$
  $$\mathbb E^*\sup_{d(\theta,\theta_0)<\delta}
  \bigl|(M_n-M)(\theta)-(M_n-M)(\theta_0)\bigr|\le C\,\frac{\phi_n(\delta)}{\sqrt n},$$
  where $\delta\mapsto\phi_n(\delta)/\delta^a$ is decreasing for some $a<2$
  not depending on $n$. Let $r_n^2\,\phi_n(1/r_n)\le\sqrt n$ for every $n$. If
  $M_n(\hat\theta_n)\ge M_n(\theta_0)-O_P(r_n^{-2})$ and $\hat\theta_n\to\theta_0$
  in outer probability, then $r_n\,d(\hat\theta_n,\theta_0)=O_P(1)$. For
  $M_n=P_nm_\theta$ the modulus bound is a maximal inequality for the
  empirical process over $\{m_\theta-m_{\theta_0}:d(\theta,\theta_0)<\delta\}$,
  obtained from bracketing or uniform entropy (CKMA SYNOPSIS07, items 40
  and 41). The modulus $\phi_n(\delta)=\delta$, as under the Lipschitz
  condition of item 38, gives $r_n=\sqrt n$. The modulus
  $\phi_n(\delta)=\delta^{1/2}$, typical of indicator criteria, gives the
  cube-root rate $r_n=n^{1/3}$: for example the center of the interval of
  fixed length containing the most observations, when $\theta\mapsto
  P[\theta-1,\theta+1]$ is twice differentiable with a proper maximum.
  Cube-root rates also hold for the Grenander estimator of SYNOPSIS104,
  item 11. The rescaled limit then follows from the argmax theorem,
  item 31, and is the location of the maximum of a Gaussian process with
  quadratic drift.

* **24. Misspecified maximum likelihood.** Suppose a consistent likelihood
  maximizer converges to the unique interior maximizer $\theta^\star$ of
  $P\log p_\theta$. Under the score expansion and moment hypotheses of
  item 4, with
  $$A=-P D^2\log p_{\theta^\star},\qquad
  B=P[\nabla\log p_{\theta^\star}\nabla\log p_{\theta^\star}^{\top}],$$
  and $A$ nonsingular,
  $$\sqrt n(\hat\theta_n-\theta^\star)
  \Rightarrow N(0,A^{-1}BA^{-\top}).$$
  When finite, $D(P\|P_\theta)$ is minimized at $\theta^\star$.
  The equality $A=B$ follows from correct specification and regularity;
  it is not a general property of likelihood fitting.

* **25. Second-order delta method.** If
  $\sqrt n(T_n-\theta)\Rightarrow Z$, $g$ is twice differentiable at
  $\theta$, and $Dg(\theta)=0$, then
  $$n(g(T_n)-g(\theta))\Rightarrow
  \tfrac12 Z^\top D^2g(\theta)Z.$$
  Even for Gaussian $Z$ the limit need not be normal. In particular,
  $\sqrt n\,\bar X\Rightarrow N(0,\sigma^2)$ implies
  $n\bar X^2\Rightarrow\sigma^2\chi^2_1$.

A map $\Phi$ between subsets of normed spaces is **Hadamard differentiable**
at $\theta$, tangentially to a linear space $D_0$, if there is a continuous
linear map $\Phi'_\theta$ such that
$[\Phi(\theta+t_nh_n)-\Phi(\theta)]/t_n\to\Phi'_\theta h$ whenever
$t_n\downarrow0$, $h_n\to h\in D_0$, and the arguments are in the domain.

* **26. Functional delta method.** If
  $r_n(T_n-\theta)\Rightarrow G$ in the relevant normed space,
  $r_n\to\infty$, $G$ is tight and supported on $D_0$, and $\Phi$ is
  Hadamard differentiable tangentially to $D_0$, then
  $$r_n(\Phi(T_n)-\Phi(\theta))\Rightarrow\Phi'_\theta G.$$
  For inversion of a distribution function at a fixed quantile with
  positive continuous density, the derivative sends $h$ to $-h(q_p)/f(q_p)$,
  recovering item 5.

* **27. Hoeffding decomposition.** For the square-integrable kernel of
  item 6 there are symmetric canonical kernels $h_j$ of orders $1\le j\le m$
  with zero conditional expectation in each argument, such that
  $$U_n-\theta=\sum_{j=1}^m\binom mj U_{n,j},\qquad
  \mathop{\mathrm{Var}}U_n
  =\sum_{j=1}^m\frac{\binom mj^2}{\binom nj}\mathbb E h_j^2.$$
  The terms are orthogonal in $L^2$, and $h_1=g$ of item 6.
  Among unbiased estimators of $\mathbb E h$ in the unrestricted
  independent-sampling model, $U_n$ has minimum variance whenever the
  competing estimators have finite variance throughout that model.

* **28. Degenerate quadratic $U$-statistics.** Let $h\in L^2(P\otimes P)$
  be symmetric and satisfy $\mathbb E[h(X_1,X_2)\mid X_1]=0$. Let
  $(\lambda_j)$ be the eigenvalues, with multiplicity, of the integral
  operator $a\mapsto\int h(\cdot,y)a(y)\,P(dy)$. Then
  $$nU_n\Rightarrow\sum_j\lambda_j(Z_j^2-1),$$
  where the $Z_j$ are independent standard normals and the series converges
  in $L^2$. This gives a basic nonnormal null limit for quadratic
  goodness-of-fit and independence statistics.

* **29. Pearson's multinomial tests.** If
  $(N_1,\ldots,N_k)\sim\mathop{\mathrm{Mult}}(n;p_1,\ldots,p_k)$ with
  fixed $k$ and all $p_i>0$, then
  $$\sum_{i=1}^k\frac{(N_i-np_i)^2}{np_i}\Rightarrow\chi^2_{k-1}.$$
  Fitting a regular $d$-dimensional multinomial submodel by maximum
  likelihood gives $k-1-d$ degrees of freedom. For an $r\times c$ table
  under independence, fitted counts $N_{i+}N_{+j}/n$ give
  $(r-1)(c-1)$ degrees of freedom. The likelihood-ratio statistic
  $2\sum N_{ij}\log(N_{ij}/\hat N_{ij})$, with $0\log0=0$, has the same
  limit and differs from Pearson's statistic by $o_P(1)$.

* **30. Generalized method of moments.** Let $m(X,\theta)\in\mathbb R^q$
  have expectation zero at $\theta_0\in\mathbb R^k$, $q\ge k$, and let
  $G=P D_\theta m(X,\theta_0)$ have full column rank. Suppose the sample
  moments obey a local uniform derivative law and a central limit theorem
  with positive definite covariance $\Omega$. A consistent minimizer of
  $\bar m_n(\theta)^\top W_n\bar m_n(\theta)$, where $W_n\to_P W>0$, has
  limiting covariance
  $$(G^\top WG)^{-1}G^\top W\Omega WG(G^\top WG)^{-1}.$$
  The choice $W=\Omega^{-1}$ minimizes this covariance in the Loewner
  order. With a consistent estimate of that weight, the minimized criterion
  multiplied by $n$ converges to $\chi^2_{q-k}$.

* **31. Argmax theorem.** Let $M_n$ converge weakly, uniformly on compact
  subsets of a metric space, to a continuous process $M$. Suppose $M$ has
  an almost surely unique maximizer $T$, separated from the rest of each
  compact set. If approximate maximizers $T_n$ are tight and their criterion
  errors are $o_P(1)$, then $T_n\Rightarrow T$. Applied to rescaled local
  criteria, this also yields nonnormal limits such as the Chernoff law in
  SYNOPSIS104, item 11.

<a id="synopsis-103b"></a>

## 103B. Higher-Order Asymptotics, Resampling, and Information Geometry

* **14. One-term Edgeworth expansion.** Let $X_i$ be independent and
  identically distributed, with mean $0$, variance $1$, and finite third
  moment $\rho=\mathbb E X_1^3$, and assume the law is nonlattice. Then
  $$P\bigl(\sqrt n\,\bar X\le x\bigr)
  =\Phi(x)-\varphi(x)\,(x^2-1)\frac{\rho}{6\sqrt n}+o(n^{-1/2}),$$
  uniformly in $x$. The lattice case adds a periodic continuity correction
  of the same order. The Berry–Esseen bound of CKMA SYNOPSIS06, item 36,
  is the corresponding uniform estimate of order $n^{-1/2}$ without an
  explicit skewness term.

* **44. Edgeworth expansion for smooth functions of means.** Let $X_i$ be
  independent copies of a random vector $X$ in $\mathbb R^d$ with mean $\mu$
  and covariance $\Sigma$, and let $j\ge1$. Let $A:\mathbb R^d\to\mathbb R$
  have $j+2$ continuous derivatives in a neighborhood of $\mu$, with
  $A(\mu)=0$ and $\sigma^2=\nabla A(\mu)^\top\Sigma\,\nabla A(\mu)>0$. Assume
  $\mathbb E\|X\|^{j+2}<\infty$ and **Cramér's condition**
  $\limsup_{\|t\|\to\infty}|\mathbb E e^{it^\top X}|<1$. Then, uniformly in $x$,
  $$P\bigl(\sqrt n\,A(\bar X)/\sigma\le x\bigr)
  =\Phi(x)+\sum_{r=1}^{j}n^{-r/2}p_r(x)\varphi(x)+o(n^{-j/2}),$$
  where $p_r$ is a polynomial of degree at most $3r-1$, odd for even $r$ and
  even for odd $r$, with coefficients determined by the moments of $X$ of
  order at most $r+2$ and the derivatives of $A$ at $\mu$. Studentized
  statistics are included by adjoining products of coordinates to $X$: for
  $\theta=g(\mu)$ with variance estimate $h(\bar X)^2$, take
  $A(x)=\bigl(g(x)-g(\mu)\bigr)/h(x)$, which covers Student's $t$
  statistic. Cramér's condition holds when the law of $X$ has a nonzero
  absolutely continuous component, or when $X=(W,W^2,\ldots,W^d)$ with $W$
  of that kind; it makes atoms of the law of $\bar X$ exponentially small.
  Item 14 is the one-dimensional mean with $j=1$, where the nonlattice
  condition replaces Cramér's condition.

* **15. Bootstrap of the mean.** Let $X_i$ be independent and identically
  distributed real random variables and let $P_n^\star$ be the conditional
  law of the bootstrap sample mean $\bar X^\star$ given the sample. The
  Kolmogorov distance between the conditional law of
  $\sqrt n\,(\bar X^\star-\bar X)$ and the law of $\sqrt n\,(\bar X-\mu)$
  tends to $0$ in probability if the observations have finite variance
  $\sigma^2$. The conditional limit is then $N(0,\sigma^2)$.
  Infinite-variance cases need separate normalization and assumptions;
  this is a sufficient finite-variance theorem, not an equivalence.

* **16. Bootstrap of the empirical distribution function.** For independent
  real observations with distribution function $F$, the conditional law of
  the bootstrap empirical process $\sqrt n\,(F_n^\star-F_n)$ converges in
  probability to the law of the $F$-Brownian bridge, in the same sense as
  the unconditional limit of $\sqrt n\,(F_n-F)$ in CKMA SYNOPSIS06,
  item 59.

* **17. Jackknife variance of a smooth function of means.** Let
  $\theta=g(\mu)$ with $g$ continuously differentiable at the mean $\mu$ of
  a square-integrable random vector, and let $\hat\theta_{(i)}$ be $g$
  evaluated at the sample mean with the $i$th observation removed. The
  delete-one jackknife variance
  $$v_n=\frac{n-1}{n}\sum_{i=1}^n
  \bigl(\hat\theta_{(i)}-\hat\theta_{(\cdot)}\bigr)^2$$
  satisfies $n v_n\to_p \nabla g(\mu)^\top\Sigma\nabla g(\mu)$, where
  $\Sigma$ is the covariance of one observation and $\hat\theta_{(\cdot)}$
  is the average of the delete-one values.

* **18. Bartlett correction.** Under the regularity used for the chi-squared
  limit of the likelihood-ratio statistic $\lambda_n$ in item 7, strengthened
  by the smoothness that yields an Edgeworth expansion of $\lambda_n$,
  $$\mathbb E_\theta\lambda_n=q\bigl(1+b(\theta)/n\bigr)+O(n^{-2})$$
  and
  $$P_\theta\bigl(\lambda_n/(1+b(\theta)/n)\le x\bigr)
  =P(\chi^2_q\le x)+O(n^{-2}).$$
  The uncorrected approximation has error of order $n^{-1}$. Replacing
  $b(\theta)$ by an estimator requires a separate expansion to retain
  that error order; consistency alone is insufficient.

* **19. Saddlepoint approximation.** Let the cumulant generating function
  $K(s)=\log\mathbb E e^{s X}$ be finite in an open neighborhood of the
  origin, and let $\hat s$ solve $K'(\hat s)=x$ for $x$ in the interior of
  the range of $K'$. Assume absolute continuity and sufficient Fourier
  integrability of the exponentially tilted laws, uniformly on compact
  saddlepoint sets, so that density inversion and its expansion are valid.
  For independent copies of $X$, the density of the sample mean then
  admits the approximation
  $$f_{\bar X}(x)
  =\Bigl(\frac{n}{2\pi K''(\hat s)}\Bigr)^{1/2}
  \exp\bigl(n\bigl(K(\hat s)-\hat s\, x\bigr)\bigr)
  \bigl(1+O(n^{-1})\bigr),$$
  uniformly for $x$ in compact subsets of that interior. The formula is the
  leading term of an expansion in powers of $n^{-1}$.

* **20. Empirical likelihood.** Let $X_i$ be independent and identically
  distributed in $\mathbb R^d$ with mean $\mu_0$ and nonsingular finite
  covariance. The empirical likelihood ratio $R(\mu_0)$ is the maximum, over
  probability weights on the sample with weighted mean $\mu_0$, of
  $n^n\prod_{i=1}^n w_i$. Then
  $-2\log R(\mu_0)\Rightarrow\chi^2_d$. For a just-identified smooth moment
  condition $\mathbb E m(X,\theta_0)=0$ of dimension $q$, with nonsingular
  Jacobian and finite nonsingular covariance of $m(X,\theta_0)$, the
  empirical likelihood ratio statistic at $\theta_0$ has the same limit with
  $d$ replaced by $q$.

* **21. Subsampling.** Let $\hat\theta_n$ be computed from an independent
  sample of size $n$, and let $b\to\infty$ with $b/n\to0$.
  Suppose $\tau_n\to\infty$, $\tau_b/\tau_n\to0$, and
  $\tau_n(\hat\theta_n-\theta)$ converges to a law with continuous
  distribution function. Over all subsamples of size $b$, form the
  empirical distribution of $\tau_b(\hat\theta_{b,I}-\hat\theta_n)$.
  Its distribution function converges uniformly in probability to that
  limiting distribution function. The construction uses no estimate
  of an asymptotic variance and does not require the limit to be normal.

On the simplex of strictly positive probability vectors
$(p_1,\ldots,p_m)$, $m\ge 2$, the **Fisher–Rao metric** is
$\sum_{i=1}^m dp_i^2/p_i$. A **congruent embedding** is a Markov kernel that
carries this simplex into the simplex of another finite sample space and is
a sufficient statistic for the image model.

* **22. Čencov's theorem.** Up to a positive constant factor, the Fisher–Rao
  metric is the unique Riemannian metric on the positive simplex that is
  invariant under congruent embeddings. The Amari–Chentsov tensor is, up to
  a constant factor, the unique symmetric covariant $3$-tensor with the same
  invariance. These two objects determine the one-parameter family of
  $\alpha$-connections used to compare exponential and mixture geometries
  on a parametric model.

### Bootstrap for smooth functionals

* **32. Bootstrap delta method.** Suppose both
  $r_n(T_n-\theta)\Rightarrow G$ and, conditionally on the observations,
  $r_n(T_n^\star-T_n)\Rightarrow G$ in probability, with a tight limit
  supported on $D_0$. For a map Hadamard differentiable as in item 26,
  the conditional law of
  $r_n(\Phi(T_n^\star)-\Phi(T_n))$ converges to that of $\Phi'_\theta G$.
  This justifies resampling smooth distributional functionals and quantiles
  with positive density. If the first derivative vanishes, this theorem
  only gives a degenerate limit; it does not justify the second-order
  bootstrap. For a zero-mean normal sample, the conditional law of
  $n((\bar X^\star)^2-\bar X^2)$ does not consistently estimate the law
  of $n\bar X^2$.

### Accuracy and failure of the bootstrap

A statistic is **asymptotically pivotal** when its limit law does not depend
on unknown quantities.

* **45. Second-order accuracy of the studentized bootstrap.** In the
  setting of item 44 let $\hat\theta=g(\bar X)$ estimate $\theta=g(\mu)$, let
  $\hat\sigma^2=h(\bar X)^2$ be a smooth consistent estimator of the
  asymptotic variance of $\sqrt n\,\hat\theta$, and let
  $T=\sqrt n(\hat\theta-\theta)/\hat\sigma$. Let
  $T^\star=\sqrt n(\hat\theta^\star-\hat\theta)/\hat\sigma^\star$ be computed from
  a resample drawn from the empirical distribution. Assume $g$ and $h$
  smooth, enough moments, and Cramér's condition, so that $T$ and, with
  probability tending to one, $T^\star$ admit the expansions of item 44 to
  order $n^{-1}$, the bootstrap polynomials being the population ones with
  moments replaced by sample moments. Then
  $$\sup_x\bigl|P(T^\star\le x\mid X_1,\ldots,X_n)-P(T\le x)\bigr|
  =O_P(n^{-1}),$$
  whereas the normal approximation to the law of $T$ has error of order
  $n^{-1/2}$ unless $p_1$ vanishes. For the nonpivotal
  $\sqrt n(\hat\theta-\theta)$ the bootstrap error is generally of exact
  order $n^{-1/2}$, because $\hat\sigma-\sigma$ is of that order. Let
  $\hat v_\alpha$ be the $\alpha$-quantile of the conditional law of
  $T^\star$. The one-sided percentile-$t$ interval
  $(-\infty,\hat\theta-n^{-1/2}\hat\sigma\hat v_\alpha]$ has coverage
  $1-\alpha+O(n^{-1})$, while the one-sided normal-theory and percentile
  intervals have coverage error of order $n^{-1/2}$ in general. In two-sided
  equal-tailed intervals the terms of order $n^{-1/2}$ cancel by parity, so
  all three have coverage error $O(n^{-1})$; the symmetric two-sided
  percentile-$t$ interval has coverage error $O(n^{-2})$.

* **46. Inconsistency of the bootstrap for the sample maximum.** Let $F$
  be continuous with right endpoint $\theta<\infty$, so $F(\theta)=1$ and
  $F(x)<1$ for $x<\theta$, and suppose that $b_n(\theta-X_{n(n)})$ has a
  continuous nondegenerate limit law for constants $b_n\to\infty$; for the
  uniform law on $[0,\theta]$, $n(\theta-X_{n(n)})/\theta\Rightarrow$ the
  standard exponential law. The bootstrap maximum $X^\star_{n(n)}$ equals
  $X_{n(n)}$ with conditional probability
  $$1-(1-1/n)^n\to1-e^{-1},$$
  so the conditional law of $b_n(X_{n(n)}-X^\star_{n(n)})$ keeps an atom of
  mass near $1-e^{-1}$ at $0$ and does not converge to the continuous limit:
  the bootstrap is inconsistent. With resample size $m\to\infty$ and
  $m/n\to0$, the $m$-out-of-$n$ bootstrap of $b_m(X_{n(n)}-X^\star_{m(m)})$ is
  consistent when $b_n=n^{1/\delta}$ for some $\delta>0$, as is subsampling,
  item 21.

## Reference guide

### Correspondence with the subdivisions

- **[103A](#synopsis-103a)**: Lehmann's large-sample course, Serfling,
  Ibragimov and Has'minskii, Le Cam and Yang, Borovkov, Pfanzagl, and the
  asymptotic chapters of Casella–Berger, Cox–Hinkley, Schervish, and
  Bickel–Doksum carry consistency, asymptotic normality, the classical
  tests, contiguity, local asymptotic normality, the convolution and
  minimax theorems, projections and $L$-statistics, rates of
  $M$-estimators, and the asymptotic power and relative efficiency of
  tests.
- **[103B](#synopsis-103b)**: Bhattacharya and Ranga Rao, Hall, Efron, Shao
  and Tu, Davison and Hinkley, Barndorff-Nielsen and Cox, Owen, Politis,
  Romano, and Wolf, and the information-geometry monographs of Amari and of
  Amari and Nagaoka carry the expansions, the resampling theorems, and
  Čencov's invariance theorem.

### Source comparisons and local copies

Van der Vaart's local full text was consulted for this expansion:
Theorem 5.7 for general consistency; Theorem 5.23 and Example 5.25 for
criterion expansions and misspecification; Theorem 5.56 for argmax limits;
Chapters 11–12 for projections and degenerate $U$-statistics; and
Theorem 20.8 and Chapter 23 for the functional and bootstrap delta methods.
The definitions of quadratic-mean differentiability and bowl-shaped loss
were checked against Chapters 7 and 8. Pearson tests and generalized
moment estimation are recorded as quadratic normal-limit applications,
with fitting and overidentification degrees of freedom stated explicitly.
The KL expansion, density saddlepoint approximation, Bartlett plug-in
correction, and subsampling centering have hypotheses beyond a bare
first-order weak limit; these are made explicit in items 9, 18, 19, and 21.

Pfanzagl, Chapters 6–8, is the local theorem-proof source for consistency of
maximum likelihood, asymptotic normality, the convolution theorem, and
superefficiency. Le Cam and Yang develop local asymptotic normality and the
limits of experiments; their Chapter 6 is the LAN chapter. Ibragimov and
Has'minskii is the monograph on asymptotic estimation from which the
convolution and local minimax statements entered the subject. Borovkov
develops the same first-order theory from empirical distributions and
$M$-estimators. Lehmann, *Elements of Large-Sample Theory*, and the
asymptotic chapters of Casella–Berger, Cox–Hinkley, Schervish, and
Bickel–Doksum give the delta method, quantiles, the three classical test
statistics, and the first asymptotic normality proofs.

Van der Vaart, *Asymptotic Statistics*, is present locally and supplies a
modern organizing treatment of both subdivisions. The other local texts
above give overlapping first-order formulations.

For 103B, Bhattacharya and Ranga Rao supply the Edgeworth expansion, Efron
and Shao and Tu the bootstrap and jackknife consistency theorems, Owen the
empirical likelihood limit, and Politis, Romano, and Wolf the subsampling
theorem. The saddlepoint formula is the one developed in Barndorff-Nielsen
and Cox and in Butler; those two monographs are not local, and the formula
was checked against the expansion literature cited in the bibliography.
Amari and Nagaoka is the local source for the invariant characterization of
the Fisher–Rao metric. Čencov's monograph is not local.

Hall, *The Bootstrap and Edgeworth Expansion*, is present in
`ReferencesSuppl`. In the third expansion it was used for items 44 and 45:
Theorem 2.2 and the discussion of Cramér's condition after it for the
smooth-function Edgeworth expansion; Section 3.1, equations (3.1)–(3.4), for
the pivotal and nonpivotal bootstrap errors; Section 3.5, Proposition 3.1
and subsections 3.5.4–3.5.5, for one- and two-sided coverage errors; and
Theorems 5.1–5.2 for the regularity behind bootstrap Edgeworth and
Cornish–Fisher expansions. Serfling's scan did not yield extractable
text in the first pass. Items 14–21 are the forms shared by the extractable local sources and
by the monographs named in the bibliography.

The third expansion added items 33–46 after reading the following passages.
Van der Vaart: Section 5.7, Theorems 5.45 and 5.48 with Addenda 5.46 and
5.49, for one-step estimators (item 36); Theorem 5.23 for $M$-estimators
with Lipschitz criteria (item 38); Theorem 5.52, Corollary 5.53, and
Example 5.54 for rates and the cube-root modal interval (item 39);
Theorem 7.10 and Theorem 8.3 for the representation theorem (item 37);
Theorems 11.1–11.2 and Lemma 11.10 for the Hájek projection (item 35);
Examples 14.9–14.13, Tables 14.1–14.2, and Theorems 14.7 and 14.19 for
slopes and Pitman efficiency (items 42–43); Theorem 15.4 and Addendum 15.5
for the power envelope (item 40); Section 16.3, display (16.5) and
Theorem 16.7, for likelihood ratios with converging local parameter sets
(item 41); Corollary 21.5 and the Bahadur–Kiefer discussion after it
(item 33); and Theorem 22.3 with Examples 22.1 and 22.11 for $L$-statistics
and trimmed means (item 34). Van der Vaart and Wellner, Theorem 3.2.5, is
the form of the rate theorem stated in item 39. Lehmann, *Elements of
Large-Sample Theory*, Section 3.4, Examples 3.4.1–3.4.3 and Theorem 3.4.1,
gives the sign, Wilcoxon, and $t$ efficiencies and the bound
$e_{W,t}\ge0.864$ for one and two samples. Shao and Tu, Example 3.9 and
Theorem 3.15 in Section 3.6, give the failure of the bootstrap for the
sample maximum and the consistency of the $m$-out-of-$n$ bootstrap
(item 46). Local asymptotic mixed normality was not added; it is not part
of the recurring independent-sampling core of these texts.

Local texts directly consulted for this selection:

- [van der Vaart, *Asymptotic Statistics*](../lean-CKMA/References/VanDerVaart1998AsymptoticStatistics-CambridgeSerStatProbMath03.pdf).
- [Pfanzagl, *Parametric Statistical Theory*](../lean-CKMA/References/Pfanzagl1994ParametricStatisticalTheory-DeGruyter.Textbook.pdf).
- [Le Cam and Yang, *Asymptotics in Statistics*](../lean-CKMA/References/LeCamYang2000AsymptoticsStatisticsBasicConcepts2ndEd-Springer.SSS.pdf).
- [Ibragimov and Has'minskii, *Statistical Estimation: Asymptotic Theory*](../lean-CKMA/References/IbragimovHasminskii1981StatisticalEstimationAsymptoticTheory-Springer.pdf).
- [Borovkov, *Mathematical Statistics*](../lean-CKMA/References/Borovkov1998MathematicalStatistics-GordonBreach.pdf).
- [Lehmann, *Elements of Large-Sample Theory*](../lean-CKMA/References/Lehmann1999ElementsLargeSampleTheory-Springer.STS.pdf).
- [Casella and Berger, *Statistical Inference*](../lean-CKMA/References/CasellaBerger2024StatisticalInference2ndEd-ChapmanHallCRC.TextsStatSci.pdf).
- [Cox and Hinkley, *Theoretical Statistics*](../lean-CKMA/References/CoxHinkley1974TheoreticalStatistics-ChapmanHallCRC.pdf).
- [Schervish, *Theory of Statistics*](../lean-CKMA/References/Schervish1995TheoryStatistics-Springer.SSS.pdf).
- [Bickel and Doksum, *Mathematical Statistics*, Volume I](../lean-CKMA/References/BickelDoksum2015MathematicalStatisticsBasicIdeasSelectedTopics2ndEdVol1-ChapmanHallCRC.TextsStatSci.pdf).
- [Bhattacharya and Ranga Rao, *Normal Approximation and Asymptotic Expansions*](../lean-CKMA/References/BhattacharyaRangaRao2010NormalApproximationAsymptoticExpansions-SIAM.CAM64.pdf).
- [Efron, *The Jackknife, the Bootstrap, and Other Resampling Plans*](../lean-CKMA/References/Efron1982JackknifeBootstrapOtherResamplingPlans-SIAM.CBMS38.pdf).
- [Efron and Tibshirani, *An Introduction to the Bootstrap*](../lean-CKMA/References/EfronTibshirani1994IntroductionBootstrap-ChapmanHallCRC.MSAP57.pdf).
- [Shao and Tu, *The Jackknife and Bootstrap*](../lean-CKMA/References/ShaoTu1995JackknifeBootstrap-Springer.SSS.pdf).
- [Davison and Hinkley, *Bootstrap Methods and their Application*](../lean-CKMA/References/DavisonHinkley1997BootstrapMethodsApplication-Cambridge.SerStatProbMath.pdf).
- [Owen, *Empirical Likelihood*](../lean-CKMA/References/Owen2001EmpiricalLikelihood-ChapmanHallCRC.MSAP99.pdf).
- [Politis, Romano, and Wolf, *Subsampling*](../lean-CKMA/References/PolitisRomanoWolf1999Subsampling-Springer.SSS.pdf).
- [Amari, *Differential-Geometrical Methods in Statistics*](../lean-CKMA/References/Amari1985DifferentialGeometricalMethodsStatistics-Springer.LNS28.pdf).
- [Amari and Nagaoka, *Methods of Information Geometry*](../lean-CKMA/References/AmariNagaoka2000MethodsInformationGeometry-AMS.TMM191.pdf).
- [van der Vaart and Wellner, *Weak Convergence and Empirical Processes*, 2nd ed.](../lean-CKMA/References/VanDerVaartWellner2023WeakConvergenceEmpiricalProcessesApplicationsStatistics2ndEd-SpringerSSS.pdf).
- [Hall, *The Bootstrap and Edgeworth Expansion*](../lean-CKMA/ReferencesSuppl/Hall1992BootstrapEdgeworthExpansion-SpringerSerStat.pdf).
