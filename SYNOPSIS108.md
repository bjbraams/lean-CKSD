# Synopsis: Dependent data and stochastic models

Part of the [mathematical synopsis series](SYNOPSIS.md).
[Bibliographical scope and references](CKSD-bib.md#cks-108).

This synopsis follows Section 108. Subdivision 108A is time series and
inference for stochastic processes. Subdivision 108B is survival and counting
processes. Subdivision 108C is sequential analysis and anytime-valid
inference. Subdivision 108D is spatial prediction and point patterns.
Subdivision 108E is extreme values. The martingale convergence and maximal
inequalities are [CKMA SYNOPSIS06](../lean-CKMA/SYNOPSIS06.md), items 42 and
43. Poisson point processes are CKMA SYNOPSIS06, items 53 and 70. Equivalence
of Gaussian measures is [CKMA SYNOPSIS09](../lean-CKMA/SYNOPSIS09.md),
item 65. Semiparametric efficiency is [SYNOPSIS104](SYNOPSIS104.md),
item 14. Subsampling is [SYNOPSIS103](SYNOPSIS103.md), item 21. Local
asymptotic normality is SYNOPSIS103, item 9.

Numbered definitions and results have stable identifiers. Additions take the
next free number and are placed beside related material; numbers need not
increase in reading order. Proofs are outside the scope of this synopsis.

<a id="synopsis-108a"></a>

## 108A. Time Series and Inference for Stochastic Processes

* **1. Martingale central limit theorem.** Let $X_{n,k}$, $1\le k\le k_n$, be
  a triangular array of square-integrable martingale differences relative to
  filtrations $\mathcal F_{n,k}$. If
  $$\sum_{k=1}^{k_n}\mathbb E[X_{n,k}^2\mid\mathcal F_{n,k-1}]
  \to_P\sigma^2$$
  and, for every $\varepsilon>0$,
  $$\sum_{k=1}^{k_n}
  \mathbb E[X_{n,k}^2\,1_{\{|X_{n,k}|>\varepsilon\}}\mid\mathcal F_{n,k-1}]
  \to_P0,$$
  then $\sum_{k=1}^{k_n}X_{n,k}\Rightarrow N(0,\sigma^2)$.

Let $(X_t)_{t\in\mathbb Z}$ be a real, weakly stationary, mean-zero process
with $\mathbb EX_t^2<\infty$. Write $P_{t-1}$ for orthogonal projection onto
the closed linear span of $\{X_s:s\le t-1\}$, and write $\varepsilon_t=X_t-P_{t-1}X_t$
for the innovation.

* **2. Wold decomposition and causal autoregression.** There exist
  coefficients $\psi_j$ with $\psi_0=1$ and $\sum_{j\ge0}\psi_j^2<\infty$, and a
  process $(V_t)$ orthogonal to every innovation, such that
  $$X_t=\sum_{j=0}^\infty\psi_j\varepsilon_{t-j}+V_t,$$
  with convergence in $L^2$. The process $(V_t)$ is deterministic, in the
  sense that $V_t$ lies in the remote-past subspace
  $\bigcap_m\overline{\mathop{\mathrm{span}}}\{X_s:s\le m\}$. The process is
  purely nondeterministic when $V_t=0$. An autoregression
  $X_t=\varphi_1X_{t-1}+\cdots+\varphi_pX_{t-p}+\varepsilon_t$ has a unique
  causal stationary solution, and that solution is an absolutely summable
  moving average of its innovations, when the polynomial
  $1-\varphi_1z-\cdots-\varphi_pz^p$ has no zero in the closed unit disk.

Let $\gamma(h)=\mathop{\mathrm{Cov}}(X_{t+h},X_t)$ and
$\rho(h)=\gamma(h)/\gamma(0)$. For an autoregression of order $p$, the
Yule–Walker equation is $\Gamma_p\varphi=\gamma_p$, where $\Gamma_p$ is the
Toeplitz matrix $(\gamma(i-j))_{1\le i,j\le p}$ and
$\gamma_p=(\gamma(1),\ldots,\gamma(p))^\top$.

* **3. Yule–Walker estimator.** For a causal autoregression of order $p$ with
  independent innovations of finite variance, the estimator obtained by
  substituting the sample autocovariances in the Yule–Walker equation is
  asymptotically normal. It is asymptotically equivalent to the conditional
  least-squares estimator and to the Gaussian maximum likelihood estimator.
  For Gaussian innovations the common asymptotic covariance is the inverse of
  the Fisher information.

* **4. Bartlett's theorem.** Let $X_t=\sum_{j=0}^\infty\psi_j\varepsilon_{t-j}$
  with $\sum_j|\psi_j|<\infty$ and with independent innovations satisfying
  $\mathbb E\varepsilon^4<\infty$. For each fixed $h$, the vector
  $\sqrt n\,(\hat\rho(1)-\rho(1),\ldots,\hat\rho(h)-\rho(h))$ is asymptotically
  normal, with covariance given by Bartlett's formula. If the observations are
  independent with finite variance and positive variance, then for each fixed
  $h\ge1$,
  $$\sqrt n\,\hat\rho(h)\Rightarrow N(0,1),$$
  and the limits at any fixed finite set of positive lags are independent.

* **5. Gaussian ARMA likelihood.** For an identifiable causal and invertible
  Gaussian ARMA model with a fixed number of parameters, no common root
  of the autoregressive and moving-average polynomials, and an interior
  true parameter, under the usual compactness and likelihood regularity
  conditions the maximum likelihood estimator is consistent
  and asymptotically normal, and its asymptotic covariance is the inverse of
  the Fisher information of one observation. The Whittle estimator, maximizing
  the frequency-domain approximation to the Gaussian likelihood, is
  asymptotically equivalent to it.

Let the spectral density in the Brockwell–Davis normalization be
$$f(\omega)=\frac1{2\pi}\sum_{h=-\infty}^\infty\gamma(h)e^{-ih\omega},
\qquad\omega\in[-\pi,\pi],$$
and let the periodogram be
$$I_n(\omega)=\frac1{2\pi n}\Bigl|\sum_{t=1}^n X_te^{-it\omega}\Bigr|^2.$$
A lag-window estimator with truncation $r$ and even weight $w$, normalized by
$w(0)=1$, is
$$\hat f_n(\omega)=\frac1{2\pi}\sum_{|h|\le r}w(h/r)\hat\gamma(h)e^{-ih\omega}.$$

* **6. Periodogram and lag-window estimation.** Let $(X_t)$ be a linear
  process as in item 4, with spectral density continuous and positive. At any
  fixed collection of distinct Fourier frequencies in $(0,\pi)$, the variables
  $I_n(\omega_j)/f(\omega_j)$ are asymptotically independent standard
  exponential random variables. In particular $I_n(\omega)$ is an inconsistent
  estimator of $f(\omega)$. If $w$ is bounded and continuous at $0$, if
  $\int_{-1}^1 w(u)^2\,du<\infty$, and if $r\to\infty$ and $r/n\to0$ with the
  bias of $\hat f_n(\omega)$ of smaller order than $(r/n)^{1/2}$, then for
  $\omega\in(0,\pi)$
  $$\sqrt{\frac nr}\bigl(\hat f_n(\omega)-f(\omega)\bigr)
  \Rightarrow N\Bigl(0,\,f(\omega)^2\int_{-1}^1 w(u)^2\,du\Bigr).$$
  At the frequencies $0$ and $\pi$ the asymptotic variance is twice the
  displayed value.

Consider a linear state-space model $x_{t+1}=F_tx_t+w_t$ and
$y_t=H_tx_t+v_t$, with Gaussian white noises $w_t$ and $v_t$ of covariances
$Q_t$ and $R_t$, independent of each other and of a Gaussian initial state.
Write $x_{t\mid t-1}$ and $P_{t\mid t-1}$ for the conditional mean and
covariance of $x_t$ given $y_1,\ldots,y_{t-1}$.

* **7. Kalman filter.** The conditional distribution of the state remains
  Gaussian. Its update uses the gain
  $$K_t=P_{t\mid t-1}H_t^\top(H_tP_{t\mid t-1}H_t^\top+R_t)^{-1}$$
  and the correction $x_{t\mid t}=x_{t\mid t-1}+K_t(y_t-H_tx_{t\mid t-1})$,
  whenever the innovation covariance $H_tP_{t\mid t-1}H_t^\top+R_t$ is
  nonsingular. The innovations $y_t-H_tx_{t\mid t-1}$ are then independent
  and Gaussian with that covariance, and the Gaussian likelihood of
  $y_1,\ldots,y_n$ is the product of their densities.

* **8. Hidden Markov likelihood.** Let the hidden chain have a finite state
  space, an irreducible aperiodic transition matrix, and emission densities
  that are positive. The forward recursion evaluates the likelihood in a
  number of operations linear in the sample size and quadratic in the number
  of states. If the parameter lies in a compact set, the emission densities
  satisfy the standard smoothness and separation conditions, and the
  parameter is identifiable up to permutation of labels, then the maximum
  likelihood estimator is consistent and asymptotically normal.

* **9. Long memory.** Suppose $\gamma(h)\sim c\,h^{2d-1}$ as $h\to\infty$,
  with $c\neq0$ and $d\in(0,1/2)$. Then the variance of the sample mean is of
  order $n^{2d-1}$, so the fluctuations of $\bar X_n$ are of order
  $n^{d-1/2}$.

* **10. Likelihood for an ergodic diffusion.** Let
  $dX_t=b(\theta,X_t)\,dt+\sigma(X_t)\,dW_t$ be observed continuously on
  $[0,T]$, with $\sigma$ nondegenerate and with the diffusion ergodic under
  each parameter. For a scalar drift parameter whose score
  $\partial_\theta b$ satisfies the usual differentiability and ergodic
  integrability conditions, with positive information and a consistent
  likelihood maximizer, as $T\to\infty$,
  $$\sqrt T(\hat\theta_T-\theta)\Rightarrow
  N\left(0,\Bigl(\mathbb E_\theta
  [(\partial_\theta b(\theta,X))^2/\sigma(X)^2]\Bigr)^{-1}\right).$$
  This variance equals the inverse of the Fisher information in the locally
  asymptotically normal limit experiment, so the estimator attains the bound
  of SYNOPSIS103, item 11.

Let $\sigma_\infty^2=\sum_{k=-\infty}^\infty\gamma(k)$ be the long-run
variance, assumed positive and finite.

* **11. Moving-block bootstrap.** Form the bootstrap sample by concatenating
  blocks of length $b$ drawn from the observed series, with $b\to\infty$ and
  $b/n\to0$. For a weakly stationary series with absolutely summable
  autocovariances and finite fourth moments, the bootstrap law of the
  centered bootstrap mean, scaled by $\sqrt n$, converges in probability to
  $N(0,\sigma_\infty^2)$, which is the limit law of $\sqrt n\,(\bar X_n-\mu)$.

### Mean estimation and innovation likelihoods

* **25. Long-run variance of a sample mean.** For a stationary process with
  absolutely summable autocovariances $\gamma(h)$,
  $$n\mathop{\mathrm{Var}}(\bar X_n)\to
  v=\sum_{h\in\mathbb Z}\gamma(h)=2\pi f(0),$$
  where $f(\omega)=(2\pi)^{-1}\sum_h\gamma(h)e^{-ih\omega}$.
  For a linear process $X_t-\mu=\sum_{j\ge0}\psi_j\varepsilon_{t-j}$ with
  absolutely summable coefficients and independent identically distributed
  innovations of mean zero and finite variance $\sigma^2$,
  $\sqrt n(\bar X_n-\mu)\Rightarrow N(0,v)$, where
  $v=\sigma^2(\sum_j\psi_j)^2$. A consistent lag-window estimate of
  $v>0$ yields asymptotically valid mean intervals. Covariance summability
  by itself does not imply a central limit theorem for every stationary
  process.

* **26. Gaussian likelihood through innovations.** For a nondegenerate
  Gaussian observation vector, let
  $\hat X_t=\mathbb E[X_t\mid X_1,\ldots,X_{t-1}]$ and
  $v_t=\mathop{\mathrm{Var}}(X_t\mid X_1,\ldots,X_{t-1})$.
  The innovations $X_t-\hat X_t$ are independent centered normals and
  $$\ell_n=-\tfrac12\sum_{t=1}^n
  \left[\log(2\pi v_t)+\frac{(X_t-\hat X_t)^2}{v_t}\right].$$
  The innovations algorithm, or the Kalman filter in a state-space
  representation, computes these conditional means and variances. This
  gives the exact likelihood, including the initial-state contribution.

<a id="synopsis-108b"></a>

## 108B. Survival Analysis and Counting Processes

Let $T$ be a failure time, let $C$ be a censoring time, and write
$\tilde T=\min(T,C)$ and $\delta=1_{\{T\le C\}}$. Assume independent censoring:
$T$ and $C$ are independent, and the observable data are independent copies of
$(\tilde T,\delta)$. Let $N(t)=1_{\{\tilde T\le t,\,\delta=1\}}$ and
$Y(t)=1_{\{\tilde T\ge t\}}$. On the event $\{Y=1\}$ the intensity of $N$ is
the failure hazard $\lambda$. The compensator of $N$ is
$\int_0^t Y(s)\lambda(s)\,ds$. Write $y(u)=\mathbb P(\tilde T\ge u)$, and
assume $y(\tau)>0$.

* **12. Nelson–Aalen estimator.** With $d_i$ failures and $n_i$ subjects at
  risk at an observed failure time $t_i$, the Nelson–Aalen estimator of the
  cumulative hazard $\Lambda(t)=\int_0^t\lambda$ is
  $\hat\Lambda(t)=\sum_{t_i\le t}d_i/n_i$. On $[0,\tau]$,
  $$\sqrt n\,(\hat\Lambda-\Lambda)$$
  converges weakly to a centered Gaussian martingale with independent
  increments and variance function $\int_0^t d\Lambda(u)/y(u)$.

* **13. Kaplan–Meier estimator.** The product-limit estimator
  $$\hat S(t)=\prod_{t_i\le t}\Bigl(1-\frac{d_i}{n_i}\Bigr)$$
  satisfies, on $[0,\tau]$ and for a continuous failure distribution,
  $$\sqrt n\,(\hat S(t)-S(t))
  \Rightarrow G(t),$$
  where $G$ is a centered Gaussian process with
  $$\mathop{\mathrm{Var}}(G(t))
  =S(t)^2\int_0^t\frac{d\Lambda(u)}{y(u)}.$$
  Greenwood's estimator of this variance, in a sample of size $n$, is
  $$\widehat{\mathop{\mathrm{Var}}}(\hat S(t))
  =\hat S(t)^2\sum_{t_i\le t}\frac{d_i}{n_i(n_i-d_i)}.$$

In the **Cox model** the conditional hazard is
$\lambda(t\mid Z)=\lambda_0(t)\exp(\beta\cdot Z)$, with $\lambda_0$
unspecified. The partial likelihood is
$$L(\beta)=\prod_{\delta_i=1}
\frac{\exp(\beta\cdot Z_i)}{\sum_{j:\tilde T_j\ge\tilde T_i}\exp(\beta\cdot Z_j)}.$$
Write $e(\beta,t)$ for the weighted average of the covariates of subjects
still at risk at time $t$, with weights proportional to $\exp(\beta\cdot Z)$.

* **14. Cox partial likelihood.** Under the usual boundedness and
  nondegeneracy conditions on $Z$, and with $y$ bounded away from zero on the
  time interval in view, the maximizer $\hat\beta$ is consistent and
  asymptotically normal. Its asymptotic covariance is the inverse of
  $$\mathbb E\int_0^\infty\bigl(Z-e(\beta,u)\bigr)^{\otimes2}\,dN(u).$$
  This matrix is the efficient information for $\beta$ in the multiplicative
  intensity model, so $\hat\beta$ attains the convolution bound of
  SYNOPSIS104, item 14. In the two-sample problem, with $Z$ the group
  indicator, the score test of $\beta=0$ is the log-rank test.

### Censoring likelihood and competing causes

* **27. Likelihood under independent right censoring.** Let $T,C$ be
  independent nonnegative times with continuous densities. For
  $\tilde T=\min(T,C)$ and $\delta=1_{\{T\le C\}}$, the observed density
  is
  $$[f_T(t)S_C(t)]^\delta[f_C(t)S_T(t)]^{1-\delta}.$$
  If the failure and censoring parameters are distinct, the contribution
  for failure inference is $f_T(t)^\delta S_T(t)^{1-\delta}$, or
  $\lambda_T(t)^\delta\exp(-\Lambda_T(t))$.
  The failure distribution is identifiable where $P(C\ge t)>0$; its
  tail beyond the censoring support cannot in general be recovered.

* **28. Log-rank statistic.** At pooled failure times $t_j$, let $Y_{aj}$
  and $d_{aj}$ be the at-risk and failure counts in group $a=0,1$,
  and let $Y_j=Y_{0j}+Y_{1j}$, $d_j=d_{0j}+d_{1j}$. Under equal failure
  hazards and independent censoring within each group, the score statistic
  and its variance estimate are
  $$U=\sum_j\left(d_{1j}-\frac{Y_{1j}d_j}{Y_j}\right),\qquad
  \hat V=\sum_j\frac{Y_{1j}Y_{0j}d_j(Y_j-d_j)}{Y_j^2(Y_j-1)},$$
  omitting terms with $Y_j\le1$. If the at-risk fractions have positive
  limits on the interval studied and the limiting information is positive,
  $U/\sqrt{\hat V}\Rightarrow N(0,1)$. The censoring distributions may
  differ across groups. This is the binary-covariate score test of item 14.

* **29. Cumulative incidence in competing risks.** For a failure time and
  observed cause $J\in\{1,\ldots,k\}$, let $\lambda_j$ be the
  cause-specific hazard. Then
  $$S(t)=\exp\left(-\sum_j\Lambda_j(t)\right),\qquad
  F_j(t)=P(T\le t,J=j)=\int_0^t S(u)\,d\Lambda_j(u).$$
  With independent right censoring, estimating each $\Lambda_j$ by its
  cause-specific Nelson–Aalen estimator and $S$ by the all-cause
  Kaplan–Meier estimator gives
  $\hat F_j(t)=\sum_{u\le t}\hat S(u-)\,dN_j(u)/Y(u)$.
  These estimators are uniformly consistent on intervals with a positive
  at-risk limit. Treating other causes as censoring and taking one minus
  Kaplan–Meier generally does not estimate $F_j$. The observed hazards
  do not identify the joint law of hypothetical latent cause-specific
  failure times without further assumptions.

<a id="synopsis-108c"></a>

## 108C. Sequential Analysis, Change Detection, and Anytime-Valid Inference

Let $f_0$ and $f_1$ be the densities of a single observation under two simple
hypotheses, and let $\Lambda_n=\prod_{i=1}^n f_1(X_i)/f_0(X_i)$. The sequential
probability ratio test continues sampling while $A<\Lambda_n<B$ and stops at
the first exit, rejecting $H_0$ if $\Lambda_n\ge B$ and accepting $H_0$ if
$\Lambda_n\le A$, where $0<A<1<B$.

* **15. Sequential probability ratio test.** Let $\alpha=\mathbb P_0(\text{reject }H_0)$
  and $\beta=\mathbb P_1(\text{accept }H_0)$. Then
  $$B\le\frac{1-\beta}\alpha,\qquad A\ge\frac{\beta}{1-\alpha}.$$
  Replacing the inequalities by equalities determines the thresholds up to
  the overshoot at the boundary. With those approximating thresholds, and
  with $\alpha_0=\alpha$ and $\alpha_1=1-\beta$,
  $$\mathbb E_i N
  \approx\frac{\alpha_i\log B+(1-\alpha_i)\log A}{\mathbb E_i\log(f_1/f_0)}.$$
  If $0<\mathbb E_i|\log(f_1/f_0)|<\infty$ and
  $\mathbb P_i(f_1\neq f_0)>0$, the stopping time is finite almost surely
  under both hypotheses. Among all tests, sequential or of fixed sample size,
  whose type I error is at most $\alpha$ and whose type II error is at most
  $\beta$, an SPRT whose thresholds are chosen so that its two error
  probabilities attain these bounds minimizes both $\mathbb E_0N$ and
  $\mathbb E_1N$. Attainment may require randomizing the decision on the
  exit boundary.

* **16. Ville's inequality and e-values.** Let $(M_n)_{n\ge0}$ be a
  nonnegative martingale with $M_0=1$. For every $\alpha\in(0,1)$,
  $$\mathbb P\Bigl(\sup_{n\ge0}M_n\ge\frac1\alpha\Bigr)\le\alpha.$$
  An e-value for a null hypothesis is a nonnegative random variable whose
  expectation is at most $1$ under every law in the null. If $E_1,E_2,\ldots$
  are sequential e-values, each with conditional expectation at most $1$ given
  the past, then every partial product is an e-value. The test that rejects
  at the first time the product reaches $1/\alpha$ has type I error at most
  $\alpha$ at every stopping time.

* **17. CUSUM and the Brownian bridge.** Let $X_1,X_2,\ldots$ be independent
  with a common distribution, mean $\mu_0$, and variance
  $\sigma^2\in(0,\infty)$, and let
  $S_k=\sum_{t=1}^k(X_t-\mu_0)$. Under a constant mean,
  $$\frac1{\sigma\sqrt n}\max_{1\le k\le n}\Bigl|S_k-\frac kn S_n\Bigr|
  \Rightarrow\sup_{t\in[0,1]}|B^0(t)|.$$

* **30. Inversion into confidence sequences.** For each parameter value
  $\theta$, let $M_t(\theta)$ be a nonnegative supermartingale under
  $P_\theta$ with $M_0(\theta)\le1$. Then
  $$C_t=\{\theta:M_t(\theta)<1/\alpha\}$$
  satisfies $P_\theta(\theta\in C_t\text{ for every }t)\ge1-\alpha$.
  Thus $C_\tau$ covers at every finite data-dependent stopping time.
  Products of conditionally valid factors, and probability mixtures of
  such supermartingales, provide constructions. Simultaneous coverage
  in time follows from item 16, rather than from a separate fixed-time
  calibration at each look.

<a id="synopsis-108d"></a>

## 108D. Spatial Data, Point Patterns, and Gaussian Processes

Let $X$ be a centered second-order process on a domain $\mathcal D$, with
known covariance $k$. Write $K$ for the covariance matrix of the observations
$X(s_1),\ldots,X(s_n)$ and $k_0$ for the vector of covariances between
$X(s_0)$ and these observations.

* **18. Simple kriging.** The linear predictor
  $k_0^\top K^{-1}(X(s_1),\ldots,X(s_n))^\top$ minimizes the mean squared
  error among linear predictors of $X(s_0)$. The minimal mean squared error is
  $k(s_0,s_0)-k_0^\top K^{-1}k_0$. If $X$ is Gaussian, the predictor is the
  conditional expectation and the minimal error is the conditional variance.

* **19. Stein's prediction theorem.** Suppose two zero-mean Gaussian measures,
  induced by covariance functions $k_1$ and $k_0$ on a separable Banach space
  of functions, are equivalent in the sense of the Feldman–Hájek theorem.
  As the observation sites become dense in a bounded domain on which the
  process has continuous paths, the ratio of the mean squared prediction
  errors of the two simple-kriging predictors tends to $1$, when either
  predictor is scored under the true covariance. If the two Gaussian measures
  are mutually singular, a predictor computed from the wrong covariance can
  fail to be consistent for the conditional expectation.

A Gaussian Markov random field on a finite graph has conditional independence
across non-edges if and only if the corresponding entries of its precision
matrix vanish. That characterization is SYNOPSIS106, item 12.

On a window $W$ of finite positive measure, a Poisson point process of
intensity function $\lambda$ has $N(W)\sim\mathop{\mathrm{Poisson}}(\int_W\lambda)$,
and conditionally on $N(W)=n$ the points are independent with density
proportional to $\lambda$. The existence and the Laplace functional are
CKMA SYNOPSIS06, item 53, and the Palm description of the Poisson case is
item 70 of that synopsis.

* **20. Constant intensity.** For a homogeneous Poisson point process of
  intensity $\lambda$, the maximum likelihood estimator based on the
  restriction to $W$ is $N(W)/|W|$. It is unbiased and is the uniform minimum
  variance unbiased estimator of $\lambda$. As $|W|\to\infty$ through
  expanding windows, it is asymptotically normal with variance $\lambda/|W|$.

* **31. Universal kriging.** Suppose the spatial mean is
  $\mathbb E X(s)=f(s)^\top\beta$ with unknown $\beta$, known covariance
  $k$, nonsingular observation covariance $K$, and full-rank design matrix
  $F=(f(s_i)^\top)_i$. The minimum-variance linear unbiased predictor at
  $s_0$ is
  $$\hat X(s_0)=f_0^\top\hat\beta+
  k_0^\top K^{-1}(X-F\hat\beta),\qquad
  \hat\beta=(F^\top K^{-1}F)^{-1}F^\top K^{-1}X.$$
  Its mean squared error is
  $$k(s_0,s_0)-k_0^\top K^{-1}k_0+
  (f_0-F^\top K^{-1}k_0)^\top(F^\top K^{-1}F)^{-1}
  (f_0-F^\top K^{-1}k_0).$$
  A constant mean gives ordinary kriging; a known mean gives item 18.

<a id="synopsis-108e"></a>

## 108E. Extreme-Value Statistics

Let $M_n=\max(X_1,\ldots,X_n)$ for independent copies of a random variable
with distribution function $F$, and write $x_F=\sup\{x:F(x)<1\}$.

* **21. Fisher–Tippett–Gnedenko theorem.** The nondegenerate distributional
  limits of $(M_n-b_n)/a_n$, with $a_n>0$, are the generalized extreme-value
  laws
  $$G_\gamma(x)=\exp\bigl(-(1+\gamma x)^{-1/\gamma}\bigr),
  \qquad\gamma\neq0,\;1+\gamma x>0,$$
  and $G_0(x)=\exp(-e^{-x})$. The survival function of $F$ lies in the domain
  of $G_\gamma$ for $\gamma>0$ when
  $$\frac{1-F(tx)}{1-F(t)}\to x^{-1/\gamma},\qquad x>0.$$
  It lies in the domain of $G_\gamma$ for $\gamma<0$ when $x_F<\infty$ and
  $$\frac{1-F(x_F-(tx)^{-1})}{1-F(x_F-t^{-1})}\to x^{1/\gamma},
  \qquad x>0,\quad t\to\infty.$$
  A sufficient condition for the Gumbel domain $\gamma=0$ is the von Mises
  condition: $F$ has a positive density $f$ in a left neighborhood of $x_F$
  and $(d/dx)\bigl((1-F(x))/f(x)\bigr)\to0$ as $x\uparrow x_F$.

* **22. Excesses over high thresholds.** The distribution $F$ lies in the
  domain of attraction of $G_\gamma$ if and only if there is a positive scale
  $\sigma(u)$ such that
  $$\sup_y\Bigl|
  \mathbb P(X-u\le y\mid X>u)-H_{\gamma,\sigma(u)}(y)\Bigr|\to0$$
  as $u\uparrow x_F$, where the supremum runs over $0\le y<x_F-u$ and
  $$H_{\gamma,\sigma}(y)
  =1-\Bigl(1+\frac{\gamma y}\sigma\Bigr)^{-1/\gamma}$$
  for $\gamma\neq0$, while $H_{0,\sigma}(y)=1-e^{-y/\sigma}$. The support is
  the set of $y>0$ with $1+\gamma y/\sigma>0$.

For a strictly stationary sequence, let $M_n$ be the sample maximum and let
$u_n$ satisfy $n(1-F(u_n))\to\tau\in(0,\infty)$.

* **23. Extremal index.** The sequence has extremal index $\theta\in(0,1]$
  when $\mathbb P(M_n\le u_n)\to e^{-\theta\tau}$ whenever
  $n(1-F(u_n))\to\tau$. An independent sequence has extremal index $1$.
  Leadbetter's conditions $D(u_n)$ and $D'(u_n)$ are sufficient for
  $\theta=1$.

For positive observations, the **Hill estimator** based on the $k$ upper
order statistics is
$$H_{k,n}
=\frac1k\sum_{i=1}^k\log X_{(n-i+1)}-\log X_{(n-k)}.$$

* **24. Hill estimator.** Suppose $1-F$ is regularly varying of index
  $-1/\gamma$ with $\gamma>0$, and suppose a second-order regular-variation
  condition holds. If $k\to\infty$ and $k/n\to0$ slowly enough for that
  second-order condition, then
  $$\sqrt k\,(H_{k,n}-\gamma)\Rightarrow N(0,\gamma^2).$$

## Reference guide

### Correspondence with the subdivisions

- **[108A](#synopsis-108a)**: Brockwell and Davis, Brillinger, Priestley, and
  Hannan and Deistler carry the Wold decomposition, autoregressive estimation,
  Bartlett's formula, and spectral estimation. Hall and Heyde carry the
  martingale central limit theorem. Durbin and Koopman carry the Kalman
  filter. Cappé, Moulines, and Rydén carry hidden Markov likelihoods.
  Giraitis, Koul, and Surgailis carry long memory. Kutoyants and Liptser and
  Shiryaev carry likelihood theory for diffusions. Fan and Yao, and Douc,
  Moulines, and Stoffer, carry the block bootstrap for series.
- **[108B](#synopsis-108b)**: Andersen, Borgan, Gill, and Keiding, Fleming
  and Harrington, Kalbfleisch and Prentice, and Aalen, Borgan, and Gjessing
  carry the Nelson–Aalen estimator, the Kaplan–Meier estimator, and the Cox
  partial likelihood.
- **[108C](#synopsis-108c)**: Wald carries the sequential probability ratio
  test. Ghosh, Mukhopadhyay, and Sen, and Tartakovsky, Nikiforov, and
  Basseville carry sequential estimation and change detection. Csörgő and
  Horváth carry the bridge limit for the CUSUM.
- **[108D](#synopsis-108d)**: Stein carries kriging and covariance
  misspecification. Møller and Waagepetersen, and Daley and Vere-Jones, carry
  point processes. Rue and Held carry Gaussian Markov random fields.
- **[108E](#synopsis-108e)**: Leadbetter, Lindgren, and Rootzén, Embrechts,
  Klüppelberg, and Mikosch, Resnick, and de Haan and Ferreira carry domains
  of attraction, threshold excesses, the extremal index, and the Hill
  estimator. Coles is the applied companion.

### Source comparisons and local copies

Brockwell–Davis supplies the long-run variance and innovations
framework used in items 25 and 26. Kalbfleisch–Prentice, Section 1.5,
was read for the log-rank statistic and its hypergeometric variance,
and Chapter 8 for cumulative incidence, including formulas (8.5) and
(8.11). The distinction between a cause-specific hazard and a cumulative
incidence is essential when other causes compete. Independent censoring
identifies the failure distribution only over the observable time range.
Item 30 is the parameterwise inversion of Ville's inequality; item 31
combines generalized least squares with the kriging projection of item 18.
The negative-index tail ratio in item 21 now uses the same limiting
variable in numerator and denominator.

Item 6 uses the Brockwell–Davis normalization in which the spectral density
integrates to $\gamma(0)$ over $[-\pi,\pi]$ and a white-noise periodogram has
exponential mean $f(\omega)$. Item 8 is the consistency and asymptotic
normality theorem of Bickel, Ritov, and Rydén in the form developed by Cappé,
Moulines, and Rydén. Item 15 records Wald's inequalities; the approximate
expected sample size neglects overshoot. Item 19 uses equivalence of Gaussian
measures in the form already numbered in the analysis synopsis. Item 24
leaves the admissible range of $k$ to the second-order condition of the tail,
as in de Haan and Ferreira.

Siegmund, *Sequential Analysis*, Ramdas and Wang's survey of e-values, and
Chopin and Papaspiliopoulos, *An Introduction to Sequential Monte Carlo*, are
not in the local reference directory. Item 16 is Ville's inequality together
with the definition of a sequential e-value. Csörgő and Horváth is present as
a DjVu file and was not text-extracted; item 17 is the Brownian-bridge limit
for the tied-down CUSUM. Box, Jenkins, Reinsel, and Ljung is present as an
EPUB file.

Local texts directly consulted or identified for this selection:

- [Brockwell and Davis, *Time Series: Theory and Methods*](../lean-CKMA/References/BrockwellDavis1991TimeSeriesTheoryMethods2ndEd-Springer.SSS.pdf).
- [Brillinger, *Time Series: Data Analysis and Theory*](../lean-CKMA/References/Brillinger2001TimeSeriesDataAnalysisTheory-SIAM.CAM36.pdf).
- [Priestley, *Spectral Analysis and Time Series*](../lean-CKMA/References/Priestley1981SpectralAnalysisTimeSeries-AcademicPress.ProbMathStat.pdf).
- [Hannan and Deistler, *The Statistical Theory of Linear Systems*](../lean-CKMA/References/HannanDeistler2012StatisticalTheoryLinearSystems-SIAM.CAM70.pdf).
- [Hall and Heyde, *Martingale Limit Theory and Its Application*](../lean-CKMA/References/HallHeyde1980MartingaleLimitTheoryApplication-AcademicPress.ProbMathStat.pdf).
- [Durbin and Koopman, *Time Series Analysis by State Space Methods*](../lean-CKMA/References/DurbinKoopman2012TimeSeriesAnalysisStateSpaceMethods2ndEd-OxfordUP.OSSS38.pdf).
- [Cappé, Moulines, and Rydén, *Inference in Hidden Markov Models*](../lean-CKMA/References/CappéMoulinesRydén2005InferenceHiddenMarkovModels-Springer.SSS.pdf).
- [Giraitis, Koul, and Surgailis, *Large Sample Inference for Long-Memory Processes*](../lean-CKMA/References/GiraitisKoulSurgailis2012LargeSampleInferenceLongMemoryProcesses-ImperialCollegePress.pdf).
- [Kutoyants, *Statistical Inference for Ergodic Diffusion Processes*](../lean-CKMA/References/Kutoyants2004StatisticalInferenceErgodicDiffusionProcesses-Springer.SSS.pdf).
- [Liptser and Shiryaev, *Statistics of Random Processes*, Vol. I](../lean-CKMA/References/LiptserShiryaev2001StatisticsRandomProcessesVol1GeneralTheory2ndEd-Springer.SMAP5.pdf).
- [Fan and Yao, *Nonlinear Time Series*](../lean-CKMA/References/FanYao2005NonlinearTimeSeriesNonparametricParametricMethods-Springer.SSS.pdf).
- [Douc, Moulines, and Stoffer, *Nonlinear Time Series*](../lean-CKMA/References/DoucMoulinesStoffer2014NonlinearTimeSeriesTheoryMethodsApplicationsRExamples-ChapmanHallCRC.TextsStatSci.pdf).
- [Andersen, Borgan, Gill, and Keiding, *Statistical Models Based on Counting Processes*](../lean-CKMA/References/AndersenBorganGillKeiding1993StatisticalModelsBasedCountingProcesses-Springer.SSS.pdf).
- [Fleming and Harrington, *Counting Processes and Survival Analysis*](../lean-CKMA/References/FlemingHarrington1991CountingProcessesSurvivalAnalysis-Wiley.SerProbStat.pdf).
- [Kalbfleisch and Prentice, *The Statistical Analysis of Failure Time Data*](../lean-CKMA/References/KalbfleischPrentice2002StatisticalAnalysisFailureTimeData2ndEd-WileySerProbStat.pdf).
- [Aalen, Borgan, and Gjessing, *Survival and Event History Analysis*](../lean-CKMA/References/AalenBorganGjessing2008SurvivalEventHistoryAnalysisProcessPointView-SpringerStatBH.pdf).
- [Wald, *Sequential Analysis*](../lean-CKMA/References/Wald1973SequentialAnalysis-Dover.pdf).
- [Ghosh, Mukhopadhyay, and Sen, *Sequential Estimation*](../lean-CKMA/References/GhoshMukhopadhyaySen1997SequentialEstimation-Wiley.SerProbStat.pdf).
- [Tartakovsky, Nikiforov, and Basseville, *Sequential Analysis*](../lean-CKMA/References/TartakovskyNikiforovBasseville2015SequentialAnalysisHypothesisTestingChangepointDetection-ChapmanHallCRC.MSAP136.pdf).
- [Csörgő and Horváth, *Limit Theorems in Change-Point Analysis*](../lean-CKMA/References/CsörgőHorváth1997LimitTheoremsChangePointAnalysis-WileySerProbStat.djvu).
- [Stein, *Interpolation of Spatial Data*](../lean-CKMA/References/Stein1999InterpolationSpatialDataTheoryKriging-Springer.SSS.pdf).
- [Møller and Waagepetersen, *Statistical Inference and Simulation for Spatial Point Processes*](../lean-CKMA/References/MøllerWaagepetersen2004StatisticalInferenceSimulationSpatialPointProcesses-ChapmanHallCRC.pdf).
- [Daley and Vere-Jones, *An Introduction to the Theory of Point Processes*, Vol. I](../lean-CKMA/References/DaleyVereJones2003IntroductionTheoryPointProcessesVol1ElementaryTheoryMethods2ndEd-Springer.ProbApplic.pdf).
- [Rue and Held, *Gaussian Markov Random Fields*](../lean-CKMA/References/RueHeld2005GaussianMarkovRandomFieldsTheoryApplications-ChapmanHallCRC.MSAP104.pdf).
- [Leadbetter, Lindgren, and Rootzén, *Extremes and Related Properties of Random Sequences and Processes*](../lean-CKMA/References/LeadbetterLindgrenRootzén1983ExtremesRelatedPropertiesRandomSequencesProcesses-Springer.SSS.pdf).
- [Embrechts, Klüppelberg, and Mikosch, *Modelling Extremal Events*](../lean-CKMA/References/EmbrechtsKlüppelbergMikosch1997ModellingExtremalEventsInsuranceFinance-Springer.SMAP33.pdf).
- [Resnick, *Extreme Values, Regular Variation and Point Processes*](../lean-CKMA/References/Resnick2008ExtremeValuesRegularVariationPointProcesses-Springer.SSORFE.pdf).
- [de Haan and Ferreira, *Extreme Value Theory*](../lean-CKMA/References/DeHaanFerreira2006ExtremeValueTheoryIntroduction-Springer.SSORFE.pdf).
- [Coles, *An Introduction to Statistical Modeling of Extreme Values*](../lean-CKMA/References/Coles2001IntroductionStatisticalModelingExtremeValues-Springer.SSS.pdf).
