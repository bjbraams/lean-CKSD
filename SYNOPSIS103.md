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

* **5. Sample quantiles.** Let $F$ be differentiable at its quantile
  $q=F^{-1}(p)$, with $0<p<1$ and density $f(q)>0$, and let $F$ be strictly
  increasing in a neighborhood of $q$. If $F_n^{-1}(p)$ is a sample
  $p$-quantile, then
  $$\sqrt n\,\bigl(F_n^{-1}(p)-q\bigr)
  \Rightarrow N\Bigl(0,\frac{p(1-p)}{f(q)^2}\Bigr).$$

* **6. Nondegenerate U-statistics.** Let $h$ be a symmetric kernel of order
  $m\ge 1$ with $\mathbb E h(X_1,\ldots,X_m)^2<\infty$, and let $U_n$ be the
  average of $h$ over the $\binom{n}{m}$ subsamples. Set
  $\theta=\mathbb E h$ and
  $g(x)=\mathbb E[h(x,X_2,\ldots,X_m)]-\theta$. If
  $\zeta_1=\mathop{\mathrm{Var}} g(X_1)>0$, then
  $$\sqrt n\,(U_n-\theta)\Rightarrow N(0,m^2\zeta_1).$$
  The projection $n^{-1}\sum_{i=1}^n m g(X_i)$ is the Hájek projection of
  $U_n-\theta$ and accounts for the limit.

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

## Reference guide

### Correspondence with the subdivisions

- **[103A](#synopsis-103a)**: Lehmann's large-sample course, Serfling,
  Ibragimov and Has'minskii, Le Cam and Yang, Borovkov, Pfanzagl, and the
  asymptotic chapters of Casella–Berger, Cox–Hinkley, Schervish, and
  Bickel–Doksum carry consistency, asymptotic normality, the classical
  tests, contiguity, local asymptotic normality, and the convolution and
  minimax theorems.
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
`ReferencesSuppl`; that copy was located but not used for theorem
verification in this expansion. Serfling's scan did not yield extractable
text in the first pass. Items 14–21 are the forms shared by the extractable local sources and
by the monographs named in the bibliography.

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
