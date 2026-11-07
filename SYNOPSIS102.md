# Synopsis: Asymptotic, semiparametric, and robust statistics

Part of the [mathematical synopsis series](SYNOPSIS.md).
[Bibliographical scope and references](CKSD-bib.md#cks-102).

This synopsis follows Section 102. Subdivision 102A is first-order
asymptotic theory: estimators and tests, limits of experiments, local tests
and relative efficiency, $M$- and $Z$-estimation, semiparametric efficiency
and missing data, and robust estimation. Subdivision 102B is the
higher-order, resampling, and information-geometric refinement that recurs
in the same sources. Weak convergence, Slutsky's theorem, the
continuous-mapping theorem, and the empirical distribution function are
[CKMA SYNOPSIS06](../lean-CKMA/SYNOPSIS06.md), items 15, 16, 58, and 59.
Uniform entropy and bracketing criteria for Donsker classes are
[CKMA SYNOPSIS07](../lean-CKMA/SYNOPSIS07.md), items 40 and 41. The
Berry–Esseen bound is CKMA SYNOPSIS06, item 36. Nonparametric rates and
minimax lower bounds are [SYNOPSIS103](SYNOPSIS103.md), and Bayesian
asymptotics are [SYNOPSIS104](SYNOPSIS104.md).

Numbered definitions and results have stable identifiers. Additions take the
next free number and are placed beside related material; numbers need not
increase in reading order. Proofs are outside the scope of this synopsis.

<a id="synopsis-102a"></a>

## 102A. First-Order Asymptotics, Statistical Experiments, and Semiparametric and Robust Inference

The first-order theory of parametric experiments comes first; semiparametric efficiency, missing data, and robust estimation extend it to infinite-dimensional nuisance parameters and to contamination.

### Parametric estimators and tests

Observations $X_1,\ldots,X_n$ are independent with common law $P_\theta$ unless
a statement says otherwise. Write $\ell_n$ for the log-likelihood and
$I(\theta)$ for the Fisher information matrix of one observation, as in
SYNOPSIS101. A sequence of estimators $\hat\theta_n$ is **consistent** when
$\hat\theta_n\to\theta$ in $P_\theta$-probability, and **asymptotically
normal** when $\sqrt n\,(\hat\theta_n-\theta)$ converges in distribution under
$P_\theta$.

* **1. Delta method.** Let $T_n$ be a random vector in $\mathbb R^k$ with
  $\sqrt n\,(T_n-\theta)\Rightarrow N(0,\Sigma)$, and let
  $g:\mathbb R^k\to\mathbb R^m$ be Borel measurable and differentiable at
  $\theta$. Then
  $$\sqrt n\,\bigl(g(T_n)-g(\theta)\bigr)
  \Rightarrow N\bigl(0,\,Dg(\theta)\,\Sigma\,Dg(\theta)^\top\bigr).$$
  Moreover
  $\sqrt n\,\bigl(g(T_n)-g(\theta)\bigr)-Dg(\theta)\sqrt n\,(T_n-\theta)\to0$
  in probability.

* **2. Consistency of maximum likelihood.** Let $\Theta$ be a compact metric
  space, let the model be dominated with densities $p_\theta$, and let
  $\theta\mapsto\log p_\theta(x)$ be upper semicontinuous for almost every
  $x$. Suppose the model is identifiable, $P_\theta\neq P_{\theta_0}$ for
  $\theta\neq\theta_0$, and every point of $\Theta$ has an open ball $U$
  around it for which $x\mapsto\sup_{\theta\in U}\log(p_\theta/p_{\theta_0})(x)$
  is measurable with
  $$\mathbb E_{\theta_0}\sup_{\theta\in U}\log\frac{p_\theta}{p_{\theta_0}}(X)
  <\infty.$$
  If $\ell_n(\hat\theta_n)\ge\ell_n(\theta_0)-o_P(n)$ under $P_{\theta_0}$,
  then $\hat\theta_n\to\theta_0$ in $P_{\theta_0}$-probability.

* **3. Asymptotic normality of maximum likelihood.** Let $\Theta$ be open in
  $\mathbb R^k$ and $\theta\in\Theta$. Assume a dominated model in which, for
  every $x$, $\vartheta\mapsto\log p_\vartheta(x)$ is three times continuously
  differentiable on a neighborhood $U$ of $\theta$, with all third partial
  derivatives bounded in absolute value on $U$ by a $P_\theta$-integrable
  function of $x$. Assume that the score $\dot\ell_\theta=\nabla\log p_\theta$
  has $\mathbb E_\theta\dot\ell_\theta=0$ and finite nonsingular covariance
  $I(\theta)$, and that $\mathbb E_\theta D^2\log p_\theta=-I(\theta)$. If
  $\hat\theta_n$ is a consistent root of the score equation
  $\nabla\ell_n(\theta)=0$, then
  $$\sqrt n\,(\hat\theta_n-\theta)
  =I(\theta)^{-1}\frac1{\sqrt n}\sum_{i=1}^n\dot\ell_\theta(X_i)+o_P(1)
  \Rightarrow N\bigl(0,I(\theta)^{-1}\bigr)$$
  under $P_\theta$. A consistent sequence of maximizers of $\ell_n$ is such a
  root with probability tending to one.

* **4. Z-estimators.** Let $\Theta$ be open in $\mathbb R^k$, let
  $\psi_\theta(x)$ take values in $\mathbb R^k$, write
  $\Psi(\theta)=\mathbb E_{\theta_0}\psi_\theta(X)$ and
  $\Psi_n(\theta)=n^{-1}\sum_{i=1}^n\psi_\theta(X_i)$, and suppose
  $\Psi(\theta_0)=0$ and $\mathbb E_{\theta_0}\|\psi_{\theta_0}(X)\|^2<\infty$.
  Suppose there is a function $\dot\psi$ with
  $\mathbb E_{\theta_0}\dot\psi(X)^2<\infty$ such that
  $\|\psi_{\theta_1}(x)-\psi_{\theta_2}(x)\|\le\dot\psi(x)\|\theta_1-\theta_2\|$
  for all $\theta_1,\theta_2$ in a neighborhood of $\theta_0$. If $\Psi$ is
  differentiable at $\theta_0$ with nonsingular derivative $V$ and
  $\hat\theta_n$ is a consistent sequence with
  $\Psi_n(\hat\theta_n)=o_P(n^{-1/2})$, then
  $$\sqrt n\,(\hat\theta_n-\theta_0)
  =-V^{-1}\sqrt n\,\Psi_n(\theta_0)+o_P(1)
  \Rightarrow N\bigl(0,V^{-1}\Sigma(V^{-1})^\top\bigr),$$
  where $\Sigma$ is the covariance of $\psi_{\theta_0}(X)$. Maximum likelihood
  is the case $\psi_\theta=\nabla_\theta\log p_\theta$; under the hypotheses
  of item 3, $V=-I(\theta_0)$ and $\Sigma=I(\theta_0)$.

* **5. One-step estimators.** Let $\Psi_n$ be random estimating functions
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
  The displayed uniformity holds under the hypotheses of item 4 for
  $\Psi_n=n^{-1}\sum_i\psi_\theta(X_i)$. Under the hypotheses of item 3, with
  $\Psi_n=n^{-1}\nabla\ell_n$ and $\hat V_n=n^{-1}D^2\ell_n(\tilde\theta_n)$,
  the one-step estimator satisfies
  $\sqrt n(\hat\theta_n-\theta_0)\Rightarrow N\bigl(0,I(\theta_0)^{-1}\bigr)$;
  no root of the likelihood equation is required. If the preliminary
  estimator takes values in the grid $n^{-1/2}\mathbb Z^k$, it suffices that
  $\sqrt n\bigl(\Psi_n(\theta_n)-\Psi_n(\theta_0)\bigr)-V\sqrt n(\theta_n-\theta_0)
  \to_P0$ for every deterministic sequence $\theta_n=\theta_0+O(n^{-1/2})$.

* **6. Sample quantiles.** Let $F$ be differentiable at its quantile
  $q=F^{-1}(p)$, with $0<p<1$ and density $f(q)>0$, and let $F$ be strictly
  increasing in a neighborhood of $q$. If $F_n^{-1}(p)$ is a sample
  $p$-quantile, then
  $$\sqrt n\,\bigl(F_n^{-1}(p)-q\bigr)
  \Rightarrow N\Bigl(0,\frac{p(1-p)}{f(q)^2}\Bigr).$$

* **7. Bahadur representation of sample quantiles.** Let $0<p<1$, let
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

* **8. Nondegenerate U-statistics.** Let $h$ be a symmetric kernel of order
  $m\ge 1$ with $\mathbb E h(X_1,\ldots,X_m)^2<\infty$, and let $U_n$ be the
  average of $h$ over the $\binom{n}{m}$ subsamples. Set
  $\theta=\mathbb E h$ and
  $g(x)=\mathbb E[h(x,X_2,\ldots,X_m)]-\theta$. If
  $\zeta_1=\mathop{\mathrm{Var}} g(X_1)>0$, then
  $$\sqrt n\,(U_n-\theta)\Rightarrow N(0,m^2\zeta_1).$$
  The Hájek projection of $U_n-\theta$, defined below, is
  $\hat U_n=n^{-1}\sum_{i=1}^n m g(X_i)$, and
  $\sqrt n\,(U_n-\theta-\hat U_n)\to0$ in $L^2$.

Let $X_1,\ldots,X_n$ be independent and let $T$ be a square-integrable
statistic. The **Hájek projection** of $T$ is its $L^2$-projection onto the
linear space of sums $\sum_{i=1}^n g_i(X_i)$ with square-integrable
$g_i(X_i)$; it equals
$$\hat T=\sum_{i=1}^n\mathbb E(T\mid X_i)-(n-1)\,\mathbb ET.$$

* **9. Hájek projection.** Let $T_n$ be square-integrable statistics of
  independent observations, with Hájek projections $\hat T_n$. If
  $\mathop{\mathrm{Var}}T_n/\mathop{\mathrm{Var}}\hat T_n\to1$, then
  $$\frac{T_n-\mathbb ET_n}{(\mathop{\mathrm{Var}}T_n)^{1/2}}
  -\frac{\hat T_n-\mathbb E\hat T_n}{(\mathop{\mathrm{Var}}\hat T_n)^{1/2}}
  \to0$$
  in $L^2$, hence in probability. Consequently, if the summands of
  $\hat T_n$ satisfy the Lindeberg condition (CKMA SYNOPSIS06, item 34),
  then $(T_n-\mathbb ET_n)/(\mathop{\mathrm{Var}}T_n)^{1/2}\Rightarrow N(0,1)$.
  The displayed convergence also holds with $\hat T_n$ the projection onto
  any closed linear space containing the constants.

An **$L$-statistic** is a linear combination of the order statistics
$X_{n(1)}\le\cdots\le X_{n(n)}$. For $0<\alpha<1/2$ the **$\alpha$-trimmed
mean** $T_n$ is the average of the $X_{n(i)}$ with
$\lfloor\alpha n\rfloor<i\le n-\lfloor\alpha n\rfloor$.

* **10. Asymptotic normality of $L$-statistics.** Let $\mathbb EX_1^2<\infty$,
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
  $(1-2\alpha)^{-2}\bigl(\int_{-b}^{b}x^2\,dF(x)+2\alpha b^2\bigr)$.

* **11. Likelihood-ratio, Wald, and score tests.** Let $\Theta$ be open in
  $\mathbb R^k$ and let the null hypothesis be
  $\Theta_0=\{\theta\in\Theta:c(\theta)=0\}$ for a continuously
  differentiable $c:\Theta\to\mathbb R^q$. Let $\theta_0\in\Theta_0$, let the
  hypotheses of item 3 hold at $\theta_0$ with $I$ continuous at $\theta_0$,
  let $C=Dc(\theta_0)$ have rank $q$, and let $\hat\theta_n$ and
  $\tilde\theta_n$ be consistent maximizers of $\ell_n$ over $\Theta$ and
  over $\Theta_0$. Put
  $\lambda_n=2\bigl(\ell_n(\hat\theta_n)-\ell_n(\tilde\theta_n)\bigr)$,
  $$W_n=n\,c(\hat\theta_n)^\top\bigl[Dc(\hat\theta_n)I(\hat\theta_n)^{-1}
  Dc(\hat\theta_n)^\top\bigr]^{-1}c(\hat\theta_n),\qquad
  S_n=\tfrac1n\nabla\ell_n(\tilde\theta_n)^\top I(\tilde\theta_n)^{-1}
  \nabla\ell_n(\tilde\theta_n).$$
  Under $P_{\theta_0}$, $\lambda_n$, $W_n$, and $S_n$ each converge in
  distribution to $\chi^2_q$, and the three statistics differ by $o_P(1)$.
  If moreover the model is differentiable in quadratic mean at $\theta_0$
  (item 13), then under $P_{\theta_0+h/\sqrt n}$ the common limit is the
  noncentral chi-squared law with $q$ degrees of freedom and noncentrality
  parameter $(Ch)^\top\bigl[CI(\theta_0)^{-1}C^\top\bigr]^{-1}Ch$.

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

* **12. Contiguity.** Let $L_n=dQ_n^{\mathrm a}/dP_n$, where
  $Q_n^{\mathrm a}$ is the part of $Q_n$ absolutely continuous with respect
  to $P_n$, so that $\Lambda_n=\log L_n$, with values in
  $[-\infty,\infty)$, is the log-likelihood ratio. If $L_n$ converges in
  distribution under $P_n$ to $e^{\Lambda}$ for a real random variable
  $\Lambda$ with $\mathbb E e^{\Lambda}=1$, then $Q_n$ is contiguous to
  $P_n$. In particular, local alternatives in a locally
  asymptotically normal experiment are mutually contiguous.

* **13. Local asymptotic normality of smooth models.** Assume independent
  sampling from a dominated model that is differentiable in quadratic mean
  at an interior point $\theta$, with nonsingular Fisher information
  $I(\theta)$. Then the product experiments are locally asymptotically normal
  with central sequence equal to the normalized score
  $\Delta_n=n^{-1/2}\sum_{i=1}^n\dot\ell_\theta(X_i)$ and
  $I(\theta)=\mathbb E_\theta\dot\ell_\theta\dot\ell_\theta^\top$.
  Quadratic-mean differentiability means that for a score
  $\dot\ell_\theta\in L^2(P_\theta)$,
  $$\int\left(\sqrt{p_{\theta+h}}-\sqrt{p_\theta}
  -\tfrac12h^\top\dot\ell_\theta\sqrt{p_\theta}\right)^2d\mu
  =o(\|h\|^2).$$
  Suppose in addition that the densities $p_{\theta+h}$ for $h$ near $0$
  are positive on a common set $A$ and vanish outside it, and that, for $x\in A$, the maps $h\mapsto p_{\theta+h}(x)$ and
  $h\mapsto p_{\theta+h}(x)\log\bigl(p_{\theta+h}(x)/p_\theta(x)\bigr)$ are
  twice continuously differentiable near $0$, with first and second
  derivatives bounded in absolute value, for $h$ in a neighborhood of $0$,
  by a $\mu$-integrable function of $x$. Then
  $$D(P_{\theta+h}\|P_\theta)=\tfrac12 h^\top I(\theta)h+o(\|h\|^2).$$

* **14. Le Cam's third lemma.** Suppose that under $P_n$ the pair
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

* **15. Asymptotic representation theorem.** Let the model be
  differentiable in quadratic mean at an interior point $\theta$ with
  nonsingular information $I(\theta)$, and let $T_n$ be statistics based on
  $n$ observations such that, for every $h\in\mathbb R^k$, $T_n$ converges in
  distribution under $P_{\theta+h/\sqrt n}^{\,n}$ to a law $L_h$. Then there is
  a randomized statistic $T$ in the Gaussian shift experiment of observing
  a single $X\sim N\bigl(h,I(\theta)^{-1}\bigr)$, $h\in\mathbb R^k$, such that
  $T$ has law $L_h$ for every $h$. For estimators of a differentiable
  $\psi(\theta)$ with $\sqrt n\bigl(T_n-\psi(\theta+h/\sqrt n)\bigr)$
  converging to $L_{\theta,h}$ under every $h$, there is such a $T$ with
  $T-\dot\psi_\theta h$ distributed as $L_{\theta,h}$ for every $h$.

* **16. Convolution theorem.** In a locally asymptotically normal experiment
  with information $I(\theta)$, the limit law $L$ of a regular estimator
  sequence is the convolution of $N(0,I(\theta)^{-1})$ with some probability
  measure on $\mathbb R^k$. If the limiting law has finite covariance,
  that covariance is at least $I(\theta)^{-1}$ in the Loewner order. An
  estimator sequence with
  $\sqrt n(T_n-\theta)=I(\theta)^{-1}\Delta_n+o_{P_\theta}(1)$ is regular with
  limit law $N(0,I(\theta)^{-1})$. By items 3 and 13 this applies to a
  consistent root of the likelihood equation when the hypotheses of both
  items hold.

* **17. Local asymptotic minimax theorem.** Let $\ell$ be a nonnegative
  lower-semicontinuous bowl-shaped loss on $\mathbb R^k$: its sublevel
  sets are convex and symmetric about zero. For any estimator sequence $T_n$ in a locally
  asymptotically normal experiment,
  $$\lim_{c\to\infty}\liminf_{n\to\infty}
  \sup_{\|h\|\le c}
  \mathbb E_{\theta+h/\sqrt n}\,
  \ell\bigl(\sqrt n\,(T_n-\theta-h/\sqrt n)\bigr)
  \ge\int\ell\,dN\bigl(0,I(\theta)^{-1}\bigr).$$
  If the experiments are those of item 13 and
  $\sqrt n(T_n-\theta)=I(\theta)^{-1}\Delta_n+o_{P_\theta}(1)$, as in
  item 16, equality holds for every bounded continuous bowl-shaped $\ell$.

* **18. Superefficiency.** Let $X_1,\ldots,X_n$ be independent
  $N(\theta,1)$ and set $\hat\theta_n=\bar X$ when $|\bar X|\ge n^{-1/4}$ and
  $\hat\theta_n=0$ otherwise. Then $\sqrt n\,(\hat\theta_n-\theta)$ converges
  to $N(0,1)$ for $\theta\neq 0$ and converges to $0$ for $\theta=0$, so the
  asymptotic variance at $0$ is smaller than the information bound. Under
  $\theta_n=h/\sqrt n$, $\sqrt n\,(\hat\theta_n-\theta_n)\to-h$ in probability,
  so the estimator is not regular at $0$. In general, let the model be
  differentiable in quadratic mean at every point of an open
  $\Theta\subset\mathbb R^k$ with nonsingular information, and let
  $\sqrt n(T_n-\theta)$ converge in distribution under every $\theta$ to a
  law $L_\theta$ with covariance $\Sigma_\theta$. Then
  $\Sigma_\theta-I(\theta)^{-1}$ is positive semidefinite for Lebesgue-almost
  every $\theta$.

### Local tests and asymptotic relative efficiency

For a test $\phi_n$ based on $n$ observations the **power function** is
$\pi_n(\theta)=\mathbb E_\theta\phi_n$. Write $z_\alpha$ for the upper
$\alpha$-quantile of the standard normal law, $1-\Phi(z_\alpha)=\alpha$.

* **19. Asymptotic power envelope.** Let the model be differentiable in
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
  with $\Delta_n$ the normalized score of item 13. The Wald statistic
  $\sqrt n\,\psi(\hat\theta_n)/(\dot\psi I^{-1}\dot\psi^\top)^{1/2}$ built on an
  estimator with $\sqrt n(\hat\theta_n-\theta_0)=I^{-1}\Delta_n+o_P(1)$
  satisfies this. For a scalar parameter and
  $\psi(\theta)=\theta-\theta_0$ the envelope is
  $1-\Phi\bigl(z_\alpha-hI^{1/2}\bigr)$.

The local parameter sets at a null point $\theta\in\Theta_0$ are
$H_n=\sqrt n(\Theta-\theta)$ and $H_{n,0}=\sqrt n(\Theta_0-\theta)$. They
**converge** to $H$ and $H_0$ when $H$ is the set of limits of convergent
sequences $h_n\in H_n$ and also contains every limit of a convergent
subsequence $h_{n_i}\in H_{n_i}$, and likewise for $H_0$.

* **20. Likelihood ratio on general local parameter sets.** Let the model be
  differentiable in quadratic mean at $\theta\in\Theta_0$ with nonsingular
  information $I$, and let
  $|\log p_{\theta_1}(x)-\log p_{\theta_2}(x)|\le\dot\ell(x)\|\theta_1-\theta_2\|$
  for $\theta_1,\theta_2$ near $\theta$ with $P_\theta\dot\ell^2<\infty$.
  Suppose the maximum likelihood estimators over $\Theta_0$ and over
  $\Theta$ are consistent and $H_n\to H$, $H_{n,0}\to H_0$. Then, under
  $P_{\theta+h/\sqrt n}$, the likelihood-ratio statistic $\lambda_n$ of
  item 11 converges in distribution to
  $$\inf_{g\in H_0}\|I^{1/2}(X-g)\|^2-\inf_{g\in H}\|I^{1/2}(X-g)\|^2,
  \qquad X\sim N(h,I^{-1}).$$
  If $\theta$ is interior and $H_0$ is a linear subspace of dimension $l$,
  the null limit is $\chi^2_{k-l}$, as in item 11. If the local sets are
  polyhedral cones, the null limit is the chi-bar-squared law of
  SYNOPSIS103, item 12. For a scalar parameter with $\Theta=[0,\infty)$ and
  $H_0:\theta=0$ the null limit is the mixture
  $\tfrac12\delta_0+\tfrac12\chi^2_1$.

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

* **21. Pitman efficiency and Noether's theorem.** Suppose that, for each
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
  sequences $\theta_n=O(n^{-1/2})$ suffices.

* **22. Efficiencies of the sign, Wilcoxon, and $t$ tests.** Let the
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
  bound. The tests themselves are SYNOPSIS103, items 2, 18, and 19;
  optimal rank scores are SYNOPSIS103, items 14 and 15.

### General criteria, moment methods, and nonlinear limits

For a measurable criterion $m_\theta$, an **$M$-estimator** approximately
maximizes $P_nm_\theta=n^{-1}\sum_i m_\theta(X_i)$. The law $P$ in this
paragraph need not belong to a parametric model.

* **23. Consistency of $M$-estimators.** Suppose
  $\sup_{\theta\in\Theta}|P_nm_\theta-Pm_\theta|\to_P0$ and the population
  maximum is separated: for every $\varepsilon>0$,
  $$\sup_{d(\theta,\theta_0)\ge\varepsilon}Pm_\theta<Pm_{\theta_0}.$$
  If $P_nm_{\hat\theta_n}\ge\sup_\theta P_nm_\theta-o_P(1)$, then
  $\hat\theta_n\to_P\theta_0$. The uniform convergence holds when $\Theta$
  is a compact metric space, $\theta\mapsto m_\theta(x)$ is continuous for
  every $x$, and $P\sup_\theta|m_\theta|<\infty$.

* **24. Asymptotic normality of $M$-estimators.** Let $\Theta$ be open in
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
  For the median $\theta_0$ of a distribution function $F$ that is
  differentiable at $\theta_0$ with $f(\theta_0)>0$, the criterion
  $m_\theta(x)=|x|-|x-\theta|$ gives $V=-2f(\theta_0)$ and recovers item 6 at
  $p=1/2$.

Let $M_n$ be random criterion functions and $M$ a deterministic function on
a semimetric space $(\Theta,d)$, with $\theta_0$ a point of maximum of $M$.
In the next item $\mathbb E^*$ is outer expectation, which avoids
measurability questions for suprema.

* **25. Rate of convergence of $M$-estimators.** Suppose
  $M(\theta)-M(\theta_0)\le-c\,d(\theta,\theta_0)^2$ for $\theta$ near
  $\theta_0$, with $c>0$. Suppose that for every $n$ and all sufficiently
  small $\delta>0$
  $$\mathbb E^*\sup_{d(\theta,\theta_0)<\delta}
  \bigl|(M_n-M)(\theta)-(M_n-M)(\theta_0)\bigr|\le C\,\frac{\phi_n(\delta)}{\sqrt n},$$
  where $C\ge0$ does not depend on $n$ or $\delta$ and
  $\delta\mapsto\phi_n(\delta)/\delta^a$ is decreasing for some $a<2$
  not depending on $n$. Let $r_n^2\,\phi_n(1/r_n)\le\sqrt n$ for every $n$. If
  $M_n(\hat\theta_n)\ge M_n(\theta_0)-O_P(r_n^{-2})$ and $\hat\theta_n\to\theta_0$
  in outer probability, then $r_n\,d(\hat\theta_n,\theta_0)=O_P(1)$. The
  modulus $\phi_n(\delta)=\delta$ gives $r_n=\sqrt n$, and the modulus
  $\phi_n(\delta)=\delta^{1/2}$ gives $r_n=n^{1/3}$. The latter applies to the
  center $\hat\theta_n$ of an interval of length $2$ containing the most
  observations, $m_\theta=1_{[\theta-1,\theta+1]}$, when $P$ has a bounded
  density, $\theta\mapsto P[\theta-1,\theta+1]$ has a unique maximizer
  $\theta_0$ at which it is twice differentiable with negative second
  derivative, and $\hat\theta_n\to_P\theta_0$: then
  $n^{1/3}(\hat\theta_n-\theta_0)=O_P(1)$.

* **26. Misspecified maximum likelihood.** Let $\Theta$ be open in
  $\mathbb R^k$, let the observations have law $P$, not necessarily in the
  model, and let $\theta^\star\in\Theta$ be the unique maximizer of
  $\theta\mapsto P\log p_\theta$. Suppose $\theta\mapsto\log p_\theta(x)$ is
  differentiable near $\theta^\star$ for every $x$, that
  $\psi_\theta=\nabla\log p_\theta$ satisfies the hypotheses of item 4 with
  $P$ in place of $P_{\theta_0}$ and $\theta^\star$ in place of $\theta_0$,
  and that the derivative of $\theta\mapsto P\psi_\theta$ at $\theta^\star$ is
  $-A$ with $A$ nonsingular. Put
  $B=P[\nabla\log p_{\theta^\star}\nabla\log p_{\theta^\star}^{\top}]$. If
  $\hat\theta_n$ is a sequence of maximizers of $\ell_n$ with
  $\hat\theta_n\to_P\theta^\star$, then
  $$\sqrt n(\hat\theta_n-\theta^\star)
  \Rightarrow N(0,A^{-1}BA^{-\top}).$$
  When $P\log p$ is finite for the density $p$ of $P$, $\theta^\star$ is the
  minimizer of $\theta\mapsto D(P\|P_\theta)$. When $P=P_{\theta^\star}$ and
  the hypotheses of item 3 hold, $A=B=I(\theta^\star)$.

* **27. Second-order delta method.** If
  $\sqrt n(T_n-\theta)\Rightarrow Z$, $g$ is twice differentiable at
  $\theta$, and $Dg(\theta)=0$, then
  $$n(g(T_n)-g(\theta))\Rightarrow
  \tfrac12 Z^\top D^2g(\theta)Z.$$
  In particular,
  $\sqrt n\,\bar X\Rightarrow N(0,\sigma^2)$ implies
  $n\bar X^2\Rightarrow\sigma^2\chi^2_1$.

A map $\Phi$ between subsets of normed spaces is **Hadamard differentiable**
at $\theta$, tangentially to a linear space $D_0$, if there is a continuous
linear map $\Phi'_\theta$ such that
$[\Phi(\theta+t_nh_n)-\Phi(\theta)]/t_n\to\Phi'_\theta h$ whenever
$t_n\downarrow0$, $h_n\to h\in D_0$, and the arguments are in the domain.

* **28. Functional delta method.** If
  $r_n(T_n-\theta)\Rightarrow G$ in the relevant normed space,
  $r_n\to\infty$, $G$ is tight and supported on $D_0$, and $\Phi$ is
  Hadamard differentiable tangentially to $D_0$, then
  $$r_n(\Phi(T_n)-\Phi(\theta))\Rightarrow\Phi'_\theta G.$$
  For inversion of a distribution function at a fixed quantile with
  positive continuous density, the derivative sends $h$ to $-h(q_p)/f(q_p)$,
  recovering item 6.

* **29. Hoeffding decomposition.** For the square-integrable kernel of
  item 8 there are symmetric canonical kernels $h_j$ of orders $1\le j\le m$
  with zero conditional expectation in each argument, such that, with
  $U_{n,j}$ the $U$-statistic of order $j$ with kernel $h_j$,
  $$U_n-\theta=\sum_{j=1}^m\binom mj U_{n,j},\qquad
  \mathop{\mathrm{Var}}U_n
  =\sum_{j=1}^m\frac{\binom mj^2}{\binom nj}\mathbb E h_j^2.$$
  The terms are orthogonal in $L^2$, and $h_1=g$ of item 8.
  Let $\mathcal P$ be the family of all laws $P$ with
  $\mathbb E_Ph(X_1,\ldots,X_m)^2<\infty$. Among estimators that are unbiased
  for $\mathbb E_Ph$ and have finite variance at every $P\in\mathcal P$,
  $U_n$ has the smallest variance at every $P\in\mathcal P$.

* **30. Degenerate quadratic $U$-statistics.** Let $h\in L^2(P\otimes P)$
  be symmetric and satisfy $\mathbb E[h(X_1,X_2)\mid X_1]=0$. Let
  $(\lambda_j)$ be the eigenvalues, with multiplicity, of the integral
  operator $a\mapsto\int h(\cdot,y)a(y)\,P(dy)$. Then
  $$nU_n\Rightarrow\sum_j\lambda_j(Z_j^2-1),$$
  where the $Z_j$ are independent standard normals and the series converges
  in $L^2$.

* **31. Pearson's multinomial tests.** If
  $(N_1,\ldots,N_k)\sim\mathop{\mathrm{Mult}}(n;p_1,\ldots,p_k)$ with
  fixed $k$ and all $p_i>0$, then
  $$\sum_{i=1}^k\frac{(N_i-np_i)^2}{np_i}\Rightarrow\chi^2_{k-1}.$$
  Let $p=p(\vartheta_0)$ for a map $\vartheta\mapsto p(\vartheta)$ from an
  open set in $\mathbb R^d$ into the open simplex that is continuously
  differentiable with derivative of rank $d$ at $\vartheta_0$. If
  $\hat\vartheta_n$ is a consistent maximum likelihood estimator of
  $\vartheta_0$, the statistic with $p(\hat\vartheta_n)$ in place of $p$
  converges in distribution to $\chi^2_{k-1-d}$. For an $r\times c$ table
  under independence, fitted counts $N_{i+}N_{+j}/n$ give
  $(r-1)(c-1)$ degrees of freedom. The likelihood-ratio statistic
  $2\sum N_{ij}\log(N_{ij}/\hat N_{ij})$, with $0\log0=0$, has the same
  limit and differs from Pearson's statistic by $o_P(1)$.

* **32. Generalized method of moments.** Let $\Theta$ be open in
  $\mathbb R^k$, let $m(X,\theta)\in\mathbb R^q$, $q\ge k$, have
  $Pm(X,\theta_0)=0$ and finite positive definite covariance
  $\Omega=P[m(X,\theta_0)m(X,\theta_0)^\top]$. Suppose that on a neighborhood
  $N$ of $\theta_0$ the map $\theta\mapsto m(x,\theta)$ is continuously
  differentiable for every $x$, with
  $P\sup_{\theta\in N}\|D_\theta m(X,\theta)\|<\infty$,
  and that $G=P D_\theta m(X,\theta_0)$ has rank $k$. Let
  $\bar m_n(\theta)=n^{-1}\sum_i m(X_i,\theta)$, let $W_n\to_P W$ with $W$
  positive definite, and let $\hat\theta_n\to_P\theta_0$ minimize
  $\bar m_n(\theta)^\top W_n\bar m_n(\theta)$. Then
  $\sqrt n(\hat\theta_n-\theta_0)$ converges in distribution to the centered
  normal law with covariance
  $$(G^\top WG)^{-1}G^\top W\Omega WG(G^\top WG)^{-1}.$$
  The choice $W=\Omega^{-1}$ minimizes this covariance in the Loewner
  order. If $W_n=\hat\Omega_n^{-1}$ with $\hat\Omega_n\to_P\Omega$, then
  $n\,\bar m_n(\hat\theta_n)^\top W_n\bar m_n(\hat\theta_n)\Rightarrow\chi^2_{q-k}$.

* **33. Argmax theorem.** Let $M_n$ and $M$ be stochastic processes indexed
  by a metric space $H$ such that $M_n\Rightarrow M$ in the space of bounded
  functions on $K$ with the supremum norm, for every compact $K\subset H$.
  Suppose almost every sample path of $M$ is upper semicontinuous and has a
  unique maximizer $T$, and $T$ is a tight random element of $H$. If $T_n$ is
  uniformly tight and $M_n(T_n)\ge\sup_hM_n(h)-o_P(1)$, then
  $T_n\Rightarrow T$ in $H$.

### Semiparametric models and missing data

A **semiparametric model** is a family $\{P_{\theta,\eta}\}$ in which $\theta$
is a Euclidean parameter and the nuisance parameter $\eta$ ranges over an
infinite-dimensional set. A parametric submodel $t\mapsto P_{\theta,\eta_t}$
that varies only the nuisance parameter has a nuisance score. The
**nuisance tangent space** is the closed linear span of the nuisance scores
of smooth finite-dimensional submodels. The **efficient score** $\tilde\ell_\theta$
is the residual of the ordinary score for $\theta$ after orthogonal projection
onto that tangent space, and the **efficient information** is
$\tilde I(\theta)=\mathbb E[\tilde\ell_\theta\tilde\ell_\theta^\top]$.

* **34. Semiparametric convolution bound.** Fix $P=P_{\theta,\eta}$. Suppose
  that for every $a\in\mathbb R^k$ and every nuisance submodel $\eta_t$ in a
  given class, the submodel $t\mapsto P_{\theta+ta,\eta_t}$ is differentiable
  in quadratic mean at $t=0$ with score $a^\top\dot\ell_\theta+g$, where the
  nuisance scores $g$ form a linear space whose closure is the nuisance
  tangent space, and that $\tilde I(\theta)$ is nonsingular. Call an
  estimator sequence regular if it is regular, in the sense defined above,
  along every such submodel. Every regular estimator sequence of $\theta$
  has a limit law equal to the convolution of $N(0,\tilde I(\theta)^{-1})$
  with some probability measure on $\mathbb R^k$. An estimator sequence is
  regular with limit law $N(0,\tilde I(\theta)^{-1})$ if and only if
  $$\sqrt n(T_n-\theta)=\frac1{\sqrt n}\sum_{i=1}^n
  \tilde I(\theta)^{-1}\tilde\ell_\theta(X_i)+o_P(1).$$
  Item 16 is the case without nuisance parameter.

Let $Y$ be a response, let $X$ be covariates that are always observed, and
let $R$ indicate whether $Y$ is observed. The observations are independent
copies of $(R,X,RY)$. The response is **missing at random** when
$P(R=1\mid X,Y)=P(R=1\mid X)$. It is **missing completely at random** when
$R$ is independent of $(X,Y)$. Write $\pi(x)=P(R=1\mid X=x)$ and
$m(x)=\mathbb E[Y\mid R=1,X=x]$.

* **35. Ignorability.** Let $(X,Y)$ have density $f_\theta(x,y)$ and let
  $P(R=1\mid X=x,Y=y)=\pi_\phi(x)$, so that the response is missing at
  random, with $(\theta,\phi)$ ranging over a product set
  $\Theta\times\Phi$. Then the observed-data likelihood of one observation
  is
  $$\pi_\phi(x)^r\bigl(1-\pi_\phi(x)\bigr)^{1-r}\cdot
  \begin{cases}f_\theta(x,y),&r=1,\\ \int f_\theta(x,y')\,dy',&r=0,\end{cases}$$
  a function of $\phi$ times a function of $\theta$. Hence the set of
  maximizers in $\theta$ of the observed-data likelihood does not depend on
  $\phi$, and equals the set of maximizers of the second factor.

For a complete-data density $f(x\mid\theta)$ and observed data $Y=t(X)$, the
**EM iteration** from $\theta'$ maximizes
$Q(\theta\mid\theta')=\mathbb E_{\theta'}[\log f(X\mid\theta)\mid Y]$ and
sets the next value equal to that maximizer.

* **36. Monotonicity of EM.** Let $L(\theta)$ be the observed-data
  log-likelihood and suppose $Q(\cdot\mid\theta')$ is finite. If $\theta''$
  maximizes $Q(\cdot\mid\theta')$, then $L(\theta'')\ge L(\theta')$. Let
  $\theta^*$ be an interior point that maximizes $Q(\cdot\mid\theta^*)$, and
  suppose $L$ and $Q(\cdot\mid\theta^*)$ are differentiable at $\theta^*$ with
  $\nabla L(\theta^*)=\nabla_\theta Q(\theta\mid\theta^*)\big|_{\theta=\theta^*}$
  (Fisher's identity). Then $\nabla L(\theta^*)=0$.

* **37. Double robustness for a missing mean.** Assume
  $\mathbb E|Y|<\infty$, missingness at random, and that the true response
  probability $\pi_0(x)=P(R=1\mid X=x)$ satisfies $\pi_0(X)\ge\delta>0$.
  Write $m_0(x)=\mathbb E[Y\mid X=x]$. The estimating function
  $$\varphi_{m,\pi}(R,X,Y)
  =\frac{RY}{\pi(X)}-\frac{R-\pi(X)}{\pi(X)}m(X)$$
  has expectation $\mathbb E Y$ as soon as either $\pi=\pi_0$, with $m$ any
  square-integrable function, or $m=m_0$, with $\pi$ any
  measurable function bounded away from zero. If $\mathbb EY^2<\infty$, the
  efficient influence function of $\mathbb EY$ in the model of all laws of
  $(R,X,RY)$ arising from a law of $(X,Y)$ and a response mechanism that is
  missing at random with $\pi_0\ge\delta$ is $\varphi_{m_0,\pi_0}-\mathbb EY$.

### Pathwise derivatives and orthogonal estimation

For a scalar parameter $\psi(P)$, let $\mathcal T\subset L^2_0(P)$ be the
closed tangent space of scores of differentiable submodels. The parameter
is **pathwise differentiable** if its derivative along every score $s$ is
$\dot\psi_P(s)=P(\phi s)$ for some $\phi\in L^2_0(P)$. The unique such
representative in $\mathcal T$ is the **canonical gradient**.

* **38. Canonical gradient and efficiency.** If a regular asymptotically
  linear estimator has influence function $\phi$, its projection onto
  $\mathcal T$ is the canonical gradient $\phi_{\mathrm{eff}}$. Hence
  $$P\phi^2=P\phi_{\mathrm{eff}}^2
  +P(\phi-\phi_{\mathrm{eff}})^2.$$
  The efficient variance bound is $P\phi_{\mathrm{eff}}^2$. In the
  unrestricted model, the mean has canonical gradient $x-PX$, and the
  $p$-quantile with positive density has gradient
  $(p-1_{\{x\le q_p\}})/f(q_p)$.

* **39. Cross-fitted estimation of a missing mean.** Split the sample into
  a fixed finite number of folds of sizes proportional to $n$. On each fold,
  evaluate the estimating function $\varphi_{\hat m,\hat\pi}$ of item 37 with
  nuisance estimates $\hat m,\hat\pi$ computed from the other folds, and let
  $\hat\mu$ be the average of these values over all observations. Suppose
  $Y\in L^2$, the true and fitted response probabilities are bounded below
  by $\delta>0$, and for each fold, with norms in $L^2$ of the law of $X$,
  $\|\hat m-m_0\|_2\to_P0$, $\|\hat\pi-\pi_0\|_2\to_P0$,
  $$\|\hat m-m_0\|_2\,\|\hat\pi-\pi_0\|_2=o_P(n^{-1/2}),$$
  and $\|\varphi_{\hat m,\hat\pi}-\varphi_{m_0,\pi_0}\|_{L^2(P)}\to_P0$, the
  norm being taken with the nuisance estimates held fixed. Then
  $$\sqrt n(\hat\mu-\mu)
  =n^{-1/2}\sum_{i=1}^n
  \left[m_0(X_i)+\frac{R_i(Y_i-m_0(X_i))}{\pi_0(X_i)}-\mu\right]+o_P(1).$$
  The summand is the efficient influence function of item 37, so the
  limiting variance is the efficient bound of item 38.

* **40. Partially linear regression.** Suppose
  $Y=D^\top\beta+g(X)+\varepsilon$, $\mathbb E[\varepsilon\mid D,X]=0$,
  and $\mathbb E[\varepsilon^2\mid D,X]=\sigma^2\in(0,\infty)$. Write
  $V=D-\mathbb E[D\mid X]$ and assume $Q=\mathbb E[VV^\top]$ is positive
  definite. Then
  $$\beta=Q^{-1}\mathbb E[V(Y-\mathbb E[Y\mid X])].$$
  In the model imposing the conditional mean restriction, with conditional
  variance unrestricted away from the true law, the efficient influence
  function at this homoscedastic law is $Q^{-1}V\varepsilon$, with
  covariance $\sigma^2Q^{-1}$.

### Adaptation, missing information, and multiple imputation

An estimator is **adaptive** in a semiparametric model if it attains, at
every law of the model, the information bound of the parametric submodel in
which the nuisance parameter is known. Adaptation requires that the score for
$\theta$ be orthogonal to the nuisance tangent space, so that the efficient
score of item 34 equals the ordinary score.

* **41. Adaptive estimation of a center of symmetry.** Let the observations
  have density $\eta(x-\theta)$, where $\eta$ ranges over all densities
  symmetric about zero that are absolutely continuous with finite Fisher
  information $I_\eta=\int(\eta'/\eta)^2\eta$. Nuisance scores are functions
  of $|x-\theta|$, while the location score $-(\eta'/\eta)(x-\theta)$ is odd
  about $\theta$. Thus the efficient score is the ordinary score and the
  efficient information is $I_\eta$. There are estimators $\hat\theta_n$, not
  depending on $\eta$, such that
  $$\sqrt n(\hat\theta_n-\theta)\Rightarrow N(0,I_\eta^{-1})$$
  regularly at every such $\eta$. If $\eta$ is only required to have median zero,
  with a positive continuous density there, the information bound drops
  to $4\eta(0)^2$, the bound for the median in items 38 and 46.

For the EM iteration of item 36, let $\theta^*$ be an interior limit point
at which the observed-data likelihood is twice differentiable and
differentiation may be passed under the conditional expectations. Define
the **complete information** $i_{\mathrm{com}}=-D^{20}Q(\theta^*\mid\theta^*)$,
the **observed information** $i_{\mathrm{obs}}$ (minus the Hessian of the
observed-data log-likelihood at $\theta^*$), and the **missing
information** $i_{\mathrm{mis}}=i_{\mathrm{com}}-i_{\mathrm{obs}}$.

* **42. Missing information and the rate of EM.** The missing information is
  the conditional covariance of the complete-data score given the observed
  data, at $\theta^*$; hence $i_{\mathrm{mis}}$ is positive semidefinite. At a
  stationary point, Louis's formula reads
  $$i_{\mathrm{obs}}=i_{\mathrm{com}}
  -\mathbb E_{\theta^*}\bigl[S_c(\theta^*)S_c(\theta^*)^\top\bigm|Y_{\mathrm{obs}}\bigr],$$
  where $S_c$ is the complete-data score. If $i_{\mathrm{com}}$ and
  $i_{\mathrm{obs}}$ are positive definite and the EM map $M$ has
  $M(\theta^*)=\theta^*$ and is differentiable at $\theta^*$, then
  $$DM(\theta^*)=i_{\mathrm{com}}^{-1}i_{\mathrm{mis}}
  =I-i_{\mathrm{com}}^{-1}i_{\mathrm{obs}}.$$
  Its eigenvalues, the **fractions of missing information**, lie in $[0,1)$.
  If $\lambda_{\max}$ is the largest of them, there is a neighborhood of
  $\theta^*$ such that EM iterates $\theta_t$ started in it converge to
  $\theta^*$ with $\limsup_{t\to\infty}\|\theta_t-\theta^*\|^{1/t}\le\lambda_{\max}$.

Let $Y_{\mathrm{mis}}^{(1)},\ldots,Y_{\mathrm{mis}}^{(D)}$ be independent draws
from the posterior predictive law of the missing values given the observed
data. For a scalar estimand, let $\hat\theta_d$ and $V_d$ be the
complete-data posterior mean and variance computed from the $d$th completed
data set. Put
$\bar\theta=D^{-1}\sum_d\hat\theta_d$, $\bar V=D^{-1}\sum_dV_d$, and
$B=(D-1)^{-1}\sum_d(\hat\theta_d-\bar\theta)^2$.

* **43. Multiple-imputation combining rules.** The identities
  $$\mathbb E(\theta\mid Y_{\mathrm{obs}})
  =\mathbb E\bigl[\mathbb E(\theta\mid Y_{\mathrm{obs}},Y_{\mathrm{mis}})
  \bigm|Y_{\mathrm{obs}}\bigr],$$
  $$\mathop{\mathrm{Var}}(\theta\mid Y_{\mathrm{obs}})
  =\mathbb E\bigl[\mathop{\mathrm{Var}}(\theta\mid Y_{\mathrm{obs}},Y_{\mathrm{mis}})
  \bigm|Y_{\mathrm{obs}}\bigr]
  +\mathop{\mathrm{Var}}\bigl[\mathbb E(\theta\mid Y_{\mathrm{obs}},Y_{\mathrm{mis}})
  \bigm|Y_{\mathrm{obs}}\bigr]$$
  hold in the joint Bayesian model. Suppose $D\ge2$, $\theta$ has finite
  posterior variance and, given $Y_{\mathrm{obs}}$, the imputations are independent of
  $\theta$. Write $B_\infty$ for the last term of the second identity. Then,
  conditionally on $Y_{\mathrm{obs}}$, $\bar\theta$ has mean
  $\mathbb E(\theta\mid Y_{\mathrm{obs}})$, and the total variance
  $T=\bar V+(1+D^{-1})B$ has mean
  $$\mathop{\mathrm{Var}}(\theta-\bar\theta\mid Y_{\mathrm{obs}})
  =\mathop{\mathrm{Var}}(\theta\mid Y_{\mathrm{obs}})+D^{-1}B_\infty.$$
  For a vector estimand the same holds with squared deviations replaced
  by outer products.

### Robust statistics

For a functional $T$ defined on a neighborhood of a distribution $F$, the
**influence function** at $x$ is
$$\mathop{\mathrm{IF}}(x;T,F)
=\lim_{\varepsilon\downarrow0}
\frac{T((1-\varepsilon)F+\varepsilon\delta_x)-T(F)}{\varepsilon},$$
when the limit exists. The **gross-error sensitivity** is the supremum of
$|\mathop{\mathrm{IF}}(x;T,F)|$ over $x$. The finite-sample **breakdown
point** of an estimator at a sample is the smallest fraction of the sample
that can be replaced so that the estimator becomes arbitrarily large or
otherwise leaves every compact set of the parameter space.

* **44. M-estimators and the Huber minimax property.** Let $\psi$ be odd
  and continuous, let $T$ be an $M$-functional of location, defined on a
  set of laws containing the contaminations $(1-\varepsilon)F+\varepsilon\delta_x$
  by $\int\psi(x-T(G))\,dG(x)=0$, and put $\theta_0=T(F)$ and
  $\lambda(\theta)=\int\psi(x-\theta)\,dF(x)$. If $\lambda$ is differentiable
  at $\theta_0$ with $\gamma=-\lambda'(\theta_0)\neq0$ and
  $\varepsilon\mapsto T((1-\varepsilon)F+\varepsilon\delta_x)$ is
  differentiable at $0$, then
  $\mathop{\mathrm{IF}}(x;T,F)=\psi(x-\theta_0)/\gamma$. If moreover $\psi$
  is Lipschitz and $\mathbb E\psi(X-\theta_0)^2<\infty$, a consistent
  sequence $\hat\theta_n$ with
  $\sum_i\psi(X_i-\hat\theta_n)=o_P(n^{1/2})$ satisfies, by item 4,
  $$\sqrt n(\hat\theta_n-\theta_0)\Rightarrow
  N\bigl(0,\mathbb E\psi(X-\theta_0)^2/\gamma^2\bigr).$$
  Let $\Phi$ and $\varphi$ be the standard normal distribution function and
  density and $\psi_k(u)=\max(-k,\min(k,u))$. Hampel's optimality: for
  $c>\sqrt{\pi/2}$, among functions $\phi$ with $\int\phi\,d\Phi=0$,
  $\int x\phi(x)\,d\Phi(x)=1$, and $\sup|\phi|\le c$, the integral
  $\int\phi^2\,d\Phi$ is uniquely minimized by
  $\phi=\psi_k/(2\Phi(k)-1)$, where $k>0$ solves $k/(2\Phi(k)-1)=c$.
  Huber's minimax property: for $0<\varepsilon<1$ let $k>0$ solve
  $2\varphi(k)/k-2\Phi(-k)=\varepsilon/(1-\varepsilon)$, and let $G_0$ have
  density $(1-\varepsilon)\varphi(x)$ for $|x|\le k$ and
  $(1-\varepsilon)\varphi(k)e^{k^2-k|x|}$ for $|x|>k$. Then
  $G_0=(1-\varepsilon)\Phi+\varepsilon H_0$ for a law $H_0$ symmetric about
  $0$, $\psi_k=-g_0'/g_0$, and with
  $V(\psi_k,G)=\int\psi_k^2\,dG/G\bigl((-k,k)\bigr)^2$,
  $$V(\psi_k,G)\le V(\psi_k,G_0)=1/I(G_0)$$
  for every $G=(1-\varepsilon)\Phi+\varepsilon H$ with $H$ symmetric about
  $0$, while
  $\int\psi^2\,dG_0/\bigl(\int\psi'\,dG_0\bigr)^2\ge1/I(G_0)$ for every
  bounded absolutely continuous $\psi$ with $\int\psi'\,dG_0\neq0$.

* **45. Breakdown points.** The sample mean has replacement breakdown
  point $1/n$ at a sample of size $n$, tending to zero as $n\to\infty$. The
  sample median of a one-dimensional sample of size $n=2m+1$ has breakdown
  point $(m+1)/n$, which tends to $1/2$. Ordinary least squares has
  breakdown point $1/n$. For a regression sample with $p\ge2$ coefficients
  whose observations are in general position, the least-median-of-squares
  estimator has breakdown point $(\lfloor n/2\rfloor-p+2)/n$.

* **46. Influence of a median and a contamination bound.** If $F$ has
  unique median $m$ and a positive continuous density there, the median
  functional has influence function
  $$\frac{1/2-1_{\{x\le m\}}}{f(m)},\qquad x\ne m.$$
  Its asymptotic variance is $1/(4f(m)^2)$ and its gross-error sensitivity
  is $1/(2f(m))$. For $G=(1-\varepsilon)F+\varepsilon H$,
  $0\le\varepsilon<1/2$, with continuous strictly increasing $F$, every
  median of $G$ lies between
  $$F^{-1}\left(\frac{1/2-\varepsilon}{1-\varepsilon}\right)
  \quad\hbox{and}\quad
  F^{-1}\left(\frac{1/2}{1-\varepsilon}\right).$$
  The bounds are attained by $H=\delta_y$ for $y$ sufficiently far to the
  left and to the right, respectively.

### Von Mises expansions and regression $M$-estimators

* **47. Influence function and asymptotic variance.** Let $T$ be defined on
  distribution functions on $\mathbb R$. Suppose $T$ is Hadamard
  differentiable at $F$ for the supremum norm, with a derivative $T_F'$ that
  is a continuous linear map on all bounded functions. Then the influence
  function is $\mathop{\mathrm{IF}}(x;T,F)=T_F'(1_{[x,\infty)}-F)$. If
  $\int\mathop{\mathrm{IF}}(x;T,F)^2\,dF(x)<\infty$, then the influence
  function has mean zero under $F$ and, by item 28 and linearity of $T_F'$,
  $$\sqrt n\bigl(T(F_n)-T(F)\bigr)
  =\frac1{\sqrt n}\sum_{i=1}^n\mathop{\mathrm{IF}}(X_i;T,F)+o_P(1)
  \Rightarrow N\Bigl(0,\int\mathop{\mathrm{IF}}(x;T,F)^2\,dF(x)\Bigr).$$
  If $T$ is Hadamard differentiable only tangentially to a closed subspace
  carrying the limit $B^0\circ F$ of $\sqrt n(F_n-F)$, as for quantiles,
  then $\sqrt n\bigl(T(F_n)-T(F)\bigr)\Rightarrow T_F'(B^0\circ F)$, a
  centered normal law.

Consider the linear model $Y_i=x_i^\top\beta+\varepsilon_i$ with fixed design
rows $x_i\in\mathbb R^p$, the first coordinate equal to one, and independent
errors with distribution function $F$. A **regression $M$-estimator** with
score $\psi=\rho'$ minimizes $\sum_i\rho(Y_i-x_i^\top t)$.

* **48. Asymptotics of regression $M$-estimators.** Let $\rho$ be convex and
  let $\psi$ be its right derivative. Assume that
  $n^{-1}\sum_ix_ix_i^\top\to Q$ positive definite and
  $\max_{i\le n}\|x_i\|/\sqrt n\to0$. Assume $\mathbb E\psi(\varepsilon)=0$,
  $\mathbb E\psi(\varepsilon)^2<\infty$,
  $\mathbb E\bigl(\psi(\varepsilon-t)-\psi(\varepsilon)\bigr)^2\to0$ as
  $t\to0$, and that $t\mapsto\mathbb E\psi(\varepsilon-t)$ is differentiable
  at $0$ with
  $\gamma=-\frac d{dt}\mathbb E\psi(\varepsilon-t)\big|_{t=0}>0$. Then every
  sequence of minimizers $\hat\beta_n$ satisfies
  $$\sqrt n(\hat\beta_n-\beta)
  =\frac{Q^{-1}}{\gamma\sqrt n}\sum_{i=1}^nx_i\psi(\varepsilon_i)+o_P(1)
  \Rightarrow N\Bigl(0,\frac{\mathbb E\psi(\varepsilon)^2}{\gamma^2}Q^{-1}\Bigr).$$
  The scalar factor is the location variance of item 44. Least squares is
  the case $\rho(u)=u^2/2$, with $\mathbb E\varepsilon^2<\infty$, and least
  absolute deviations the case $\rho(u)=|u|$, when $F$ has median $0$ and
  is differentiable there with $F'(0)>0$, so that $\gamma=2F'(0)$. When
  whole pairs $(x_i,Y_i)$ may be replaced, the least-absolute-deviation
  estimator has breakdown point $1/n$, in contrast with the
  least-median-of-squares estimator of item 45.

<a id="synopsis-102b"></a>

## 102B. Higher-Order Asymptotics, Resampling, and Information Geometry

* **49. One-term Edgeworth expansion.** Let $X_i$ be independent and
  identically distributed, with mean $0$, variance $1$, and finite third
  moment $\rho=\mathbb E X_1^3$, and assume the law is nonlattice. Then
  $$P\bigl(\sqrt n\,\bar X\le x\bigr)
  =\Phi(x)-\varphi(x)\,(x^2-1)\frac{\rho}{6\sqrt n}+o(n^{-1/2}),$$
  uniformly in $x$.

* **50. Edgeworth expansion for smooth functions of means.** Let $X_i$ be
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
  of that kind.
  Item 49 is the one-dimensional mean with $j=1$, where the nonlattice
  condition replaces Cramér's condition.

* **51. Bootstrap of the mean.** Let $X_i$ be independent and identically
  distributed real random variables and let $P_n^\star$ be the conditional
  law of the bootstrap sample mean $\bar X^\star$ given the sample. The
  Kolmogorov distance between the conditional law of
  $\sqrt n\,(\bar X^\star-\bar X)$ and the law of $\sqrt n\,(\bar X-\mu)$
  tends to $0$ in probability if the observations have finite variance
  $\sigma^2$. The conditional limit is then $N(0,\sigma^2)$.

* **52. Bootstrap of the empirical distribution function.** For independent
  real observations with distribution function $F$, the conditional law of
  the bootstrap empirical process $\sqrt n\,(F_n^\star-F_n)$ converges in
  outer probability to the law of the $F$-Brownian bridge $B^0\circ F$ of
  CKMA SYNOPSIS06, item 59, in the bounded Lipschitz metric on the space of
  bounded functions on $\mathbb R$ with the supremum norm:
  $$\sup_{h}\bigl|\mathbb E\bigl[h\bigl(\sqrt n(F_n^\star-F_n)\bigr)\bigm|X_1,\ldots,X_n\bigr]
  -\mathbb Eh(B^0\circ F)\bigr|\to0,$$
  the supremum being over functions $h$ bounded by $1$ and $1$-Lipschitz
  for the supremum norm.

* **53. Jackknife variance of a smooth function of means.** Let
  $\theta=g(\mu)$ with $g$ continuously differentiable at the mean $\mu$ of
  a square-integrable random vector, and let $\hat\theta_{(i)}$ be $g$
  evaluated at the sample mean with the $i$th observation removed. The
  delete-one jackknife variance
  $$v_n=\frac{n-1}{n}\sum_{i=1}^n
  \bigl(\hat\theta_{(i)}-\hat\theta_{(\cdot)}\bigr)^2$$
  satisfies $n v_n\to_p \nabla g(\mu)^\top\Sigma\nabla g(\mu)$, where
  $\Sigma$ is the covariance of one observation and $\hat\theta_{(\cdot)}$
  is the average of the delete-one values.

* **55. Saddlepoint approximation.** Let the cumulant generating function
  $K(s)=\log\mathbb E e^{s X}$ be finite in an open neighborhood of the
  origin, and let $\hat s$ solve $K'(\hat s)=x$ for $x$ in the interior of
  the range of $K'$ on the interior of the domain of $K$. Assume that $X$
  has a density and that there is $\nu\ge1$ such that
  $\int_{\mathbb R}\bigl|\mathbb E e^{(\hat s+it)X}/\mathbb Ee^{\hat sX}
  \bigr|^\nu\,dt<\infty$. For independent copies of $X$ and $n>\nu$, the
  sample mean $\bar X$ of $n$ copies has a continuous density
  $f_{\bar X}$, which is bounded if also
  $\int_{\mathbb R}|\mathbb E e^{itX}|^\nu\,dt<\infty$, and for this fixed
  $x$, as $n\to\infty$,
  $$f_{\bar X}(x)
  =\Bigl(\frac{n}{2\pi K''(\hat s)}\Bigr)^{1/2}
  \exp\bigl(n\bigl(K(\hat s)-\hat s\, x\bigr)\bigr)
  \bigl(1+O(n^{-1})\bigr).$$

* **56. Empirical likelihood.** Let $X_i$ be independent and identically
  distributed in $\mathbb R^d$ with mean $\mu_0$ and nonsingular finite
  covariance. The empirical likelihood ratio $R(\mu_0)$ is the maximum, over
  probability weights on the sample with weighted mean $\mu_0$, of
  $n^n\prod_{i=1}^n w_i$. Then
  $-2\log R(\mu_0)\Rightarrow\chi^2_d$. For a just-identified smooth moment
  condition $\mathbb E m(X,\theta_0)=0$ of dimension $q$, with nonsingular
  Jacobian and finite nonsingular covariance of $m(X,\theta_0)$, the
  empirical likelihood ratio statistic at $\theta_0$ has the same limit with
  $d$ replaced by $q$.

* **57. Subsampling.** Let $\hat\theta_n$ be computed from an independent
  sample of size $n$, and let $b\to\infty$ with $b/n\to0$.
  Suppose $\tau_n\to\infty$, $\tau_b/\tau_n\to0$, and
  $\tau_n(\hat\theta_n-\theta)$ converges to a law with continuous
  distribution function. Over all subsamples of size $b$, form the
  empirical distribution of $\tau_b(\hat\theta_{b,I}-\hat\theta_n)$.
  Its distribution function converges uniformly in probability to that
  limiting distribution function.

Let $S_m$ be the simplex of strictly positive probability vectors
$(p_1,\ldots,p_m)$, $m\ge 2$, with tangent vectors $u\in\mathbb R^m$,
$\sum_iu_i=0$. The **Fisher–Rao metric** is
$g_p(u,v)=\sum_{i=1}^m u_iv_i/p_i$, and the **Amari–Chentsov tensor** is
$T_p(u,v,w)=\sum_{i=1}^m u_iv_iw_i/p_i^2$. For $2\le m\le n$, a
**congruent embedding** $f:S_m\to S_n$ is given by a partition of
$\{1,\ldots,n\}$ into nonempty blocks $A_1,\ldots,A_m$ and probability
vectors $q^{(i)}$ with positive entries on $A_i$, by
$f(p)_j=p_iq^{(i)}_j$ for $j\in A_i$.

* **58. Čencov's theorem.** Let $(h_m)_{m\ge2}$ be Riemannian metrics on
  the simplices $S_m$ such that $f^*h_n=h_m$ for every congruent embedding
  $f:S_m\to S_n$. Then there is a constant $c>0$ with $h_m=c\,g$ on every
  $S_m$. Likewise, a family of symmetric covariant $3$-tensors on the $S_m$
  that is invariant under all congruent embeddings is a constant multiple
  of the Amari–Chentsov tensor.

### Bootstrap for smooth functionals

* **59. Bootstrap delta method.** Suppose both
  $r_n(T_n-\theta)\Rightarrow G$ and, conditionally on the observations,
  $r_n(T_n^\star-T_n)\Rightarrow G$ in probability in the bounded Lipschitz
  metric (as in item 52), with a tight limit
  supported on $D_0$. For a map Hadamard differentiable as in item 28,
  the conditional law of
  $r_n(\Phi(T_n^\star)-\Phi(T_n))$ converges in probability to that of
  $\Phi'_\theta G$, in the same metric. The theorem
  does not extend to a vanishing first derivative: for an independent
  $N(0,\sigma^2)$ sample, $\sigma>0$, the bounded Lipschitz distance between
  the conditional law of $n((\bar X^\star)^2-\bar X^2)$ and the law of
  $n\bar X^2$ does not converge to $0$ in probability.

### Accuracy and failure of the bootstrap

A statistic is **asymptotically pivotal** when its limit law does not depend
on unknown quantities.

* **60. Second-order accuracy of the studentized bootstrap.** Let $X$ be a
  random vector in $\mathbb R^d$ with mean $\mu$, covariance $\Sigma$, and
  finite moments of every order. Assume Cramér's condition of item 50 for
  the augmented vector $Z=(X,(X_jX_k)_{1\le j\le k\le d})$. Let $g$ be
  infinitely differentiable near $\mu$, with
  $\sigma^2=\nabla g(\mu)^\top\Sigma\nabla g(\mu)>0$. Put
  $$\hat\theta=g(\bar X),\qquad\theta=g(\mu),\qquad
  \hat\Sigma=\frac1n\sum_i(X_i-\bar X)(X_i-\bar X)^\top,\qquad
  \hat\sigma^2=\nabla g(\bar X)^\top\hat\Sigma\nabla g(\bar X).$$
  For a resample of size $n$, recompute the mean, covariance, and the
  entire variance estimate to obtain $\hat\theta^\star$ and
  $\hat\sigma^\star$. Define
  $T=\sqrt n(\hat\theta-\theta)/\hat\sigma$ and
  $T^\star=\sqrt n(\hat\theta^\star-\hat\theta)/\hat\sigma^\star$;
  use arbitrary finite definitions of the estimates outside the smooth
  neighborhood, and set the statistics to zero when their denominators
  vanish or their means lie outside that neighborhood. Under the joint
  sample-and-resample law these exceptional events have probability
  smaller than every fixed inverse power of $n$.
  Then
  $$\sup_x\bigl|P(T^\star\le x\mid X_1,\ldots,X_n)-P(T\le x)\bigr|
  =O_P(n^{-1}),$$
  whereas
  $$\sup_x|P(T\le x)-\Phi(x)|=n^{-1/2}\sup_x|p_1(x)\varphi(x)|+o(n^{-1/2}),$$
  with $p_1$ the polynomial of item 50 applied to the smooth function of
  the augmented sample mean defining $T$. Fix $0<\alpha<1/2$. Let
  $\hat v_\beta$ be the $\beta$-quantile of the conditional law of $T^\star$ and $\hat x_\beta$ that
  of $\hat\theta^\star$. The one-sided percentile-$t$ interval
  $(-\infty,\hat\theta-n^{-1/2}\hat\sigma\hat v_\alpha]$ has coverage
  $1-\alpha+O(n^{-1})$, while the one-sided normal-theory interval
  $(-\infty,\hat\theta+n^{-1/2}\hat\sigma z_\alpha]$ and the one-sided
  percentile interval $(-\infty,\hat x_{1-\alpha}]$ have coverage
  $1-\alpha+O(n^{-1/2})$. The corresponding two-sided equal-tailed intervals
  of nominal coverage $1-2\alpha$ all have coverage $1-2\alpha+O(n^{-1})$,
  and the symmetric percentile-$t$ interval
  $[\hat\theta-n^{-1/2}\hat\sigma\hat w,\hat\theta+n^{-1/2}\hat\sigma\hat w]$,
  with $\hat w$ the $(1-2\alpha)$-quantile of the conditional law of
  $|T^\star|$, has coverage $1-2\alpha+O(n^{-2})$.

* **61. Inconsistency of the bootstrap for the sample maximum.** Let $F$
  be continuous with right endpoint $\theta<\infty$, so $F(\theta)=1$ and
  $F(x)<1$ for $x<\theta$, and suppose that $b_n(\theta-X_{n(n)})$ has a
  continuous nondegenerate limit law for constants $b_n\to\infty$; for the
  uniform law on $[0,\theta]$, $n(\theta-X_{n(n)})/\theta\Rightarrow$ the
  standard exponential law. The bootstrap maximum $X^\star_{n(n)}$ equals
  $X_{n(n)}$ with conditional probability
  $$1-(1-1/n)^n\to1-e^{-1},$$
  so the conditional law of $b_n(X_{n(n)}-X^\star_{n(n)})$ has an atom of
  mass $1-(1-1/n)^n$ at $0$, and its Kolmogorov distance to the continuous
  limit law of $b_n(\theta-X_{n(n)})$ is at least $\bigl(1-(1-1/n)^n\bigr)/2$,
  which does not tend to $0$. With resample size $m\to\infty$ and
  $m/n\to0$, and $b_n=n^{1/\delta}$ for some $\delta>0$, the Kolmogorov
  distance between the conditional law of $b_m(X_{n(n)}-X^\star_{m(m)})$ and
  that limit law tends to $0$ in probability; subsampling, item 57, is
  likewise consistent.

## Reference guide

### Correspondence with the subdivisions

- **[102A](#synopsis-102a)**: Lehmann's large-sample course, Serfling,
  Ibragimov and Has'minskii, Le Cam and Yang, Borovkov, Pfanzagl, and the
  asymptotic chapters of Casella–Berger, Cox–Hinkley, Schervish, and
  Bickel–Doksum carry consistency, asymptotic normality, the classical tests,
  contiguity, local asymptotic normality, the convolution and minimax
  theorems, projections and $L$-statistics, rates of $M$-estimators, and the
  asymptotic power and relative efficiency of tests. Bickel, Klaassen, Ritov,
  and Wellner, Kosorok, Little and Rubin, and van der Laan and Robins carry
  efficiency bounds, ignorability, EM, and double robustness. Jurečková and
  Sen develop the asymptotics of $M$-estimators. Huber and Ronchetti, and
  Hampel, Ronchetti, Rousseeuw, and Stahel, are the organizing monographs for
  influence functions and breakdown.
- **[102B](#synopsis-102b)**: Bhattacharya and Ranga Rao, Hall, Efron, Shao
  and Tu, Davison and Hinkley, Barndorff-Nielsen and Cox, Owen, Politis,
  Romano, and Wolf, and the information-geometry monographs of Amari and of
  Amari and Nagaoka carry the expansions, the resampling theorems, and
  Čencov's invariance theorem.

### Source comparisons and local copies

#### Asymptotic statistics

Van der Vaart's local full text supplies the following source basis:
Theorem 5.7 for general consistency; Theorem 5.23 and Example 5.25 for
criterion expansions and misspecification; Theorem 5.56 for argmax limits;
Chapters 11–12 for projections and degenerate $U$-statistics; and
Theorem 20.8 and Chapter 23 for the functional and bootstrap delta methods.
The definitions of quadratic-mean differentiability and bowl-shaped loss
were checked against Chapters 7 and 8. Pearson tests and generalized
moment estimation are recorded as quadratic normal-limit applications,
with fitting and overidentification degrees of freedom stated explicitly.
The KL expansion, density saddlepoint approximation, and subsampling
centering have hypotheses beyond a bare first-order weak limit; these are
made explicit in items 13, 55, and 57. Item 55 is stated pointwise in $x$:
it follows by exponential tilting at $\hat s$, as in Severini, *Elements of
Distribution Theory*, Theorem 14.4 and its proof, combined with the local
expansion of Bhattacharya and Ranga Rao, Theorem 19.2 with $s=4$, whose
hypothesis is the $\nu$-th power integrability of the tilted
characteristic function; the odd term vanishes at the mean. Tilting writes
$f_{\bar X}(y)$ as $(\mathbb Ee^{\hat sX})^ne^{-n\hat sy}$ times the density
of the tilted mean, so the tilted condition gives continuity but not
boundedness; boundedness uses the condition at $s=0$, as in Daniels (1954).
The uniform
relative error over compact sets of $x$ asserted by Daniels (1954) and
Jensen (1995) was not checked against those sources, which are not local,
and is not stated.

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

For 102B, Bhattacharya and Ranga Rao supply the Edgeworth expansion, Efron
and Shao and Tu the bootstrap and jackknife consistency theorems, Owen the
empirical likelihood limit, and Politis, Romano, and Wolf the subsampling
theorem. The saddlepoint formula is the one developed in Barndorff-Nielsen
and Cox and in Butler; those two monographs are not local, and the formula
was checked against the expansion literature cited in the bibliography.
Amari and Nagaoka is the local source for the invariant characterization of
the Fisher–Rao metric. Čencov's monograph is not local.

Hall, *The Bootstrap and Edgeworth Expansion*, is present in
`ReferencesSuppl`. It supplies items 50 and 60:
Theorem 2.2 and the discussion of Cramér's condition after it for the
smooth-function Edgeworth expansion; Section 3.1, equations (3.1)–(3.4), for
the pivotal and nonpivotal bootstrap errors; Section 3.5, Proposition 3.1
and subsections 3.5.4–3.5.5, for one- and two-sided coverage errors; and
Theorems 5.1–5.2 for the regularity behind bootstrap Edgeworth and
Cornish–Fisher expansions. Item 60 uses the plug-in delta-method variance
computed from first and second sample moments, recomputed in every
resample. Matching the variance at the true mean alone is insufficient:
even for a standard normal sample, a fixed denominator of one leaves
the bootstrap variance fluctuations of order $n^{-1/2}$. The symmetric
interval refinement is Hall, Section 3.6. Serfling's scan did not yield extractable
text. Items 49, 51–53, and 55–57 are the forms shared by the extractable local sources and
by the monographs named in the bibliography.

Items 5, 7, 9, 10, 15, 19–22, 24, 25, 50, 60, and 61 have the following
source basis.
Van der Vaart: Section 5.7, Theorems 5.45 and 5.48 with Addenda 5.46 and
5.49, for one-step estimators (item 5); Theorem 5.23 for $M$-estimators
with Lipschitz criteria (item 24); Theorem 5.52, Corollary 5.53, and
Example 5.54 for rates and the cube-root modal interval (item 25);
Theorem 7.10 and Theorem 8.3 for the representation theorem (item 15);
Theorems 11.1–11.2 and Lemma 11.10 for the Hájek projection (item 9);
Examples 14.9–14.13, Tables 14.1–14.2, and Theorems 14.7 and 14.19 for
slopes and Pitman efficiency (items 21 and 22); Theorem 15.4 and Addendum 15.5
for the power envelope (item 19); Section 16.3, display (16.5) and
Theorem 16.7, for likelihood ratios with converging local parameter sets
(item 20); Corollary 21.5 and the Bahadur–Kiefer discussion after it
(item 7); and Theorem 22.3 with Examples 22.1 and 22.11 for $L$-statistics
and trimmed means (item 10). Van der Vaart and Wellner, Theorem 3.2.5, is
the form of the rate theorem stated in item 25. Lehmann, *Elements of
Large-Sample Theory*, Section 3.4, Examples 3.4.1–3.4.3 and Theorem 3.4.1,
gives the sign, Wilcoxon, and $t$ efficiencies and the bound
$e_{W,t}\ge0.864$ for one and two samples. Shao and Tu, Example 3.9 and
Theorem 3.15 in Section 3.6, give the failure of the bootstrap for the
sample maximum and the consistency of the $m$-out-of-$n$ bootstrap
(item 61). Local asymptotic mixed normality is outside the recurring
independent-sampling core of these texts.

#### Nonparametric, semiparametric, and robust inference

Items 38–40 make the semiparametric geometry operational: representing
derivatives in $L^2$, projecting out nuisance regressions, and controlling
the product remainder after sample splitting. They give explicit conditions
for the efficiency claims in items 34 and 37, rather than treating
consistency of fitted nuisances alone as sufficient for a central limit
theorem.

Huber and Ronchetti, and Hampel, Ronchetti, Rousseeuw, and Stahel, are
absent locally; items 44 and 45
are the forms used by Jurečková and Sen and by the robust chapters of the
general inference texts. Huber's saddle point in item 44 was checked
against Jurečková and Sen, Section 2.4, displays (2.4.9)–(2.4.16), which
restate Huber (1964, *Ann. Math. Statist.* 35) for the symmetrically
contaminated normal model: the score $\psi_k$, the equation for $k$, which
is (2.4.15) rewritten, and the inequality chain (2.4.16). The explicit
density of $G_0$, its decomposition with $H_0$ carried by $|x|>k$, and the
identity $V(\psi_k,G_0)=1/I(G_0)$ were verified directly; Huber's paper
itself was not accessible. The breakdown point of least median of squares
in item 45 is Rousseeuw (1984, *J. Amer. Statist. Assoc.* 79, 871–880),
Theorem 1, for the replacement breakdown point of Donoho and Huber, his
display (2.1), with general position meaning that any $p$ observations
determine the coefficient vector uniquely. Tsiatis's missing-data monograph is absent locally;
item 37 is the augmented inverse-probability function of that book and of
van der Laan and Robins.

Item 41 is van der Vaart, Example 25.27 and Section 25.8.1. Items 42 and 43
are Little and Rubin, Sections 8.4.3 and 10.2, including equations
(8.27)–(8.30) and (10.13)–(10.15). Item 47 follows van der Vaart, Section
20.1. Item 48 is the convex-criterion case of the regression theory of
Jurečková and Sen, Section 5.5, with the breakdown remarks of their
Section 4.8; their Theorems 5.5.1–5.5.3 also cover nonconvex criteria and
studentized versions. The statement of item 48 is an application of Hjort
and Pollard, *Asymptotics for minimisers of convex processes* (1993,
arXiv:1107.3806), Theorem 2.2, with $g_i(y,t)=\rho(y-x_i^\top t)$,
$D_i=-\psi(\varepsilon_i)x_i$, $A_i=\gamma x_ix_i^\top$, $J=\gamma Q$, and
$K=\mathbb E\psi(\varepsilon)^2\,Q$; the stated moment, continuity, and
design conditions give their remainder conditions and the Lindeberg
condition. This is the convexity argument of Pollard (1991) for least
absolute deviations, which Jurečková and Sen cite in Section 5.7.

Hampel's general optimal bounded-influence estimator is not stated, because
the Hampel–Ronchetti–Rousseeuw–Stahel monograph is not available locally;
item 44 records its location case.

Local texts directly consulted or identified for this selection:

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
- [Severini, *Elements of Distribution Theory*](../lean-CKMA/ReferencesSuppl/Severini2005ElementsDistributionTheory-Cambridge.SerStatProbMat.pdf).
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
- [Bickel, Klaassen, Ritov, and Wellner, *Efficient and Adaptive Estimation for Semiparametric Models*](../lean-CKMA/References/BickelKlaassenRitovWellner1993EfficientAdaptiveEstimationSemiparametricModels-JohnsHopkins.MathSci.pdf).
- [Kosorok, *Introduction to Empirical Processes and Semiparametric Inference*](../lean-CKMA/References/Kosorok2008IntroductionEmpiricalProcessesSemiparametricInference-Springer.SSS.pdf).
- [Little and Rubin, *Statistical Analysis with Missing Data*](../lean-CKMA/References/LittleRubin2020StatisticalAnalysisMissingData3rdEd-Wiley.SerProbStat.pdf).
- [van der Laan and Robins, *Unified Methods for Censored Longitudinal Data and Causality*](../lean-CKMA/References/VanDerLaanRobins2003UnifiedMethodsCensoredLongitudinalDataCausality-Springer.SSS.pdf).
- [Jurečková and Sen, *Robust Statistical Procedures*](../lean-CKMA/References/JurečkováSen1996RobustStatisticalProceduresAsymptoticsInterrelations-Wiley.SerProbStat.pdf).
- [Hájek, Šidák, and Sen, *Theory of Rank Tests*](../lean-CKMA/References/HájekŠidákSen1999TheoryRankTests2ndEd-AcademicPress.djvu).
