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

### Spectral representation and linear prediction

A complex function $\gamma$ on the integers is **nonnegative definite** when
$\sum_{r,s=1}^n a_r\gamma(r-s)\bar a_s\ge0$ for all $n$ and all complex
$a_1,\ldots,a_n$. An **ARMA$(p,q)$ process** is a weakly stationary solution of
$\varphi(B)X_t=\theta(B)Z_t$, where $B$ is the backward shift, $(Z_t)$ is white
noise of variance $\sigma^2$, $\varphi(z)=1-\varphi_1z-\cdots-\varphi_pz^p$, and
$\theta(z)=1+\theta_1z+\cdots+\theta_qz^q$.

* **32. Herglotz theorem and rational spectral densities.** A complex
  function $\gamma$ on the integers is the autocovariance function of a weakly
  stationary process if and only if it is Hermitian and nonnegative definite,
  and if and only if
  $$\gamma(h)=\int_{(-\pi,\pi]}e^{ih\nu}\,dF(\nu),\qquad h\in\mathbb Z,$$
  for a right-continuous, nondecreasing, bounded function $F$ on $[-\pi,\pi]$
  with $F(-\pi)=0$. This **spectral distribution function** is uniquely
  determined by $\gamma$. If $\sum_h|\gamma(h)|<\infty$, then $F$ has the
  continuous density $f$ of item 6. If $\varphi$ and $\theta$ have no common
  zeros and $\varphi$ has no zero on the unit circle, then the ARMA equation
  has a unique stationary solution, and its spectral density is
  $$f(\lambda)=\frac{\sigma^2}{2\pi}\,
  \frac{|\theta(e^{-i\lambda})|^2}{|\varphi(e^{-i\lambda})|^2},
  \qquad\lambda\in[-\pi,\pi].$$
  Causality and invertibility are not needed for this formula.

For a zero-mean weakly stationary process, write
$\hat X_{n+1}=\varphi_{n1}X_n+\cdots+\varphi_{nn}X_1$ for the best linear
predictor of $X_{n+1}$ from $X_1,\ldots,X_n$ and $v_n$ for its mean squared
error, with $v_0=\gamma(0)$. The **partial autocorrelation** at lag $n$ is
$\alpha(n)=\varphi_{nn}$.

* **33. Durbin–Levinson algorithm and partial autocorrelation.** If
  $\gamma(0)>0$ and $\gamma(h)\to0$ as $h\to\infty$, the predictor coefficients
  are uniquely determined and satisfy $\varphi_{11}=\gamma(1)/\gamma(0)$ and,
  for $n\ge2$,
  $$
  \begin{aligned}
  \varphi_{nn}&=\frac{\gamma(n)-\sum_{j=1}^{n-1}\varphi_{n-1,j}\gamma(n-j)}{v_{n-1}},\\
  \varphi_{nj}&=\varphi_{n-1,j}-\varphi_{nn}\varphi_{n-1,n-j},
  \qquad 1\le j\le n-1,\\
  v_n&=v_{n-1}\bigl(1-\varphi_{nn}^2\bigr).
  \end{aligned}
  $$
  For a causal autoregression of order $p$, $\alpha(p)=\varphi_p$ and
  $\alpha(h)=0$ for $h>p$. If, in addition, the innovations are independent
  and identically distributed with finite variance, the sample partial
  autocorrelation obtained by inserting sample autocovariances satisfies
  $\sqrt n\,\hat\alpha(h)\Rightarrow N(0,1)$ for each fixed $h>p$.

* **34. Kolmogorov's formula for the prediction error.** Let $(X_t)$ be a
  real, zero-mean, weakly stationary process with spectral distribution
  function $F$, and let $f$ be the density of the absolutely continuous part
  of $F$. The one-step mean squared prediction error from the infinite past,
  $\sigma^2=\mathbb E(X_t-P_{t-1}X_t)^2$ in the notation of item 2, is
  $$\sigma^2=2\pi\exp\Bigl\{\frac1{2\pi}\int_{-\pi}^{\pi}\log f(\lambda)
  \,d\lambda\Bigr\},$$
  read as $0$ when the integral is $-\infty$. Thus $X_t$ is linearly
  predictable without error from its past if and only if
  $\int_{-\pi}^{\pi}\log f=-\infty$. In the normalization of item 6 this is the
  Szegő infimum theorem, [CKMA SYNOPSIS42](../lean-CKMA/SYNOPSIS42.md),
  item 28.

### ARMA estimation, conditional heteroscedasticity, and Markov chains

Write $\beta=(\varphi_1,\ldots,\varphi_p,\theta_1,\ldots,\theta_q)$ and
$g(\lambda;\beta)=|\theta(e^{-i\lambda})|^2/|\varphi(e^{-i\lambda})|^2$, so that
$f=\sigma^2g/(2\pi)$. The **Whittle estimator** minimizes
$n^{-1}\sum_jI_n(\omega_j)/g(\omega_j;\beta)$ over the Fourier frequencies
$\omega_j\in(-\pi,\pi]$.

* **35. Asymptotic covariance of ARMA estimators.** Let $(X_t)$ be an
  ARMA$(p,q)$ process with innovations that are independent and identically
  distributed with mean $0$ and variance $\sigma^2>0$, not necessarily
  Gaussian. Suppose the true parameter has $\varphi(z)\theta(z)\ne0$ for
  $|z|\le1$, $\varphi$ and $\theta$ have no common zeros, and
  $(\varphi_p,\theta_q)\ne(0,0)$. Then the Gaussian maximum likelihood
  estimator, the least-squares estimator, and the Whittle estimator, each
  computed over parameters with these properties, are strongly consistent,
  the corresponding innovation-variance estimators converge almost surely to
  $\sigma^2$, and each of the three estimators $\hat\beta_n$ satisfies
  $$\sqrt n\,(\hat\beta_n-\beta)\Rightarrow N\bigl(0,W(\beta)^{-1}\bigr),\qquad
  W(\beta)=\frac1{4\pi}\int_{-\pi}^{\pi}
  \nabla_\beta\log g(\lambda;\beta)\,\nabla_\beta\log g(\lambda;\beta)^\top
  \,d\lambda.$$
  For an autoregression $W(\beta)^{-1}=\sigma^2\Gamma_p^{-1}$, the limit of the
  Yule–Walker estimator in item 3. The Gaussian likelihood thus gives valid
  inference for the ARMA coefficients without Gaussian innovations; item 5
  adds that under Gaussianity $W(\beta)$ is the Fisher information.

A **GARCH$(1,1)$ process** is a solution of $X_t=\sigma_t\varepsilon_t$ and
$\sigma_t^2=\alpha_0+\alpha_1X_{t-1}^2+\beta_1\sigma_{t-1}^2$, where
$(\varepsilon_t)_{t\in\mathbb Z}$ is independent and identically distributed
with mean $0$ and variance $1$, $\alpha_0>0$, and $\alpha_1,\beta_1\ge0$. It is
**nonanticipative** when $\varepsilon_t$ is independent of
$\{\sigma_s^2:s\le t\}$ for every $t$.

* **36. Stationarity of GARCH$(1,1)$.** Let
  $\gamma=\mathbb E\log(\beta_1+\alpha_1\varepsilon_0^2)\in[-\infty,\infty)$.
  If $\gamma<0$, the series below converges almost surely, and
  $$\sigma_t^2=\alpha_0\Bigl(1+\sum_{n=1}^\infty\prod_{j=1}^n
  (\beta_1+\alpha_1\varepsilon_{t-j}^2)\Bigr),\qquad X_t=\sigma_t\varepsilon_t,$$
  defines the unique strictly stationary solution. If $\gamma\ge0$, there is
  no strictly stationary solution. A nonanticipative solution with finite
  second moments that is weakly stationary exists if and only if
  $\alpha_1+\beta_1<1$; it is then the solution above, and $(X_t)$ is weak
  white noise with variance $\alpha_0/(1-\alpha_1-\beta_1)$. Since
  $\gamma\le\log(\alpha_1+\beta_1)$ by Jensen's inequality, strict
  stationarity with infinite variance occurs when $\gamma<0\le
  \log(\alpha_1+\beta_1)$.

Let $(X_k)_{k\ge0}$ be an irreducible aperiodic Markov chain on
$\{1,\ldots,m\}$ with transition matrix $P=(p_{ij})$ and stationary law $\pi$.
From $X_0,\ldots,X_n$ let $n_{ij}$ be the number of transitions from $i$ to $j$
and $n_i=\sum_jn_{ij}$.

* **37. Maximum likelihood for a finite Markov chain.** Conditionally on
  $X_0$, the maximum likelihood estimator of $p_{ij}$ is
  $\hat p_{ij}=n_{ij}/n_i$. As $n\to\infty$, $n_i/n\to\pi_i$ almost surely by
  [CKMA SYNOPSIS08](../lean-CKMA/SYNOPSIS08.md), item 50, and
  $\sqrt n\,(\hat p_{ij}-p_{ij})_{i,j}$ is asymptotically centered normal with
  $$\lim_n n\mathop{\mathrm{Cov}}(\hat p_{ij},\hat p_{i'j'})
  =\frac{\delta_{ii'}\bigl(\delta_{jj'}p_{ij}-p_{ij}p_{ij'}\bigr)}{\pi_i}.$$
  Thus different rows are asymptotically independent, and row $i$ behaves
  like a multinomial sample of size $n\pi_i$. If $p_{ij}=p_{ij}(\theta)$ for
  a parameter $\theta\in\mathbb R^k$ that is identifiable, with continuous
  second derivatives and nonsingular information
  $$\mathcal I(\theta)=\sum_{i,j:\,p_{ij}>0}\pi_i\,
  \frac{\nabla p_{ij}(\theta)\nabla p_{ij}(\theta)^\top}{p_{ij}(\theta)},$$
  a consistent root of the likelihood equation satisfies
  $\sqrt n(\hat\theta-\theta)\Rightarrow N(0,\mathcal I(\theta)^{-1})$. For
  the simple hypothesis $P=P^0$, the statistics
  $\sum_{i,j}(n_{ij}-n_ip^0_{ij})^2/(n_ip^0_{ij})$ and
  $2\sum_{i,j}n_{ij}\log(\hat p_{ij}/p^0_{ij})$, summed over the positive
  entries of $P^0$, are asymptotically chi-squared with $d-m$ degrees of
  freedom, where $d$ is the number of positive entries of $P^0$.

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

### Counting-process martingales and regression for hazards

Let $N=(N_1,\ldots,N_k)$ be a multivariate counting process, adapted to a
filtration, with no two components jumping at the same time, and with
intensity processes $\lambda_h$. By the Doob–Meyer decomposition,
[CKMA SYNOPSIS08](../lean-CKMA/SYNOPSIS08.md), item 13, the processes
$M_h=N_h-\int_0^\cdot\lambda_h(s)\,ds$ are local square-integrable martingales,
and their predictable covariations are
$\langle M_h,M_{h'}\rangle=\delta_{hh'}\int_0^\cdot\lambda_h(s)\,ds$. For
locally bounded predictable $H_h$, the integral
$\sum_h\int_0^\cdot H_h\,dM_h$ is a local square-integrable martingale with
predictable variation $\sum_h\int_0^\cdot H_h^2\lambda_h\,ds$.

* **38. Rebolledo's martingale central limit theorem.** For each $n$ let
  $N^{(n)}$ be a $k_n$-variate counting process as above, with intensities
  $\lambda_h^{(n)}$, let $H^{(n)}=(H^{(n)}_{jh})$ be a $k\times k_n$ matrix of
  locally bounded predictable processes, and set
  $$M_j^{(n)}(t)=\sum_{h=1}^{k_n}\int_0^tH_{jh}^{(n)}(s)
  \bigl(dN_h^{(n)}(s)-\lambda_h^{(n)}(s)\,ds\bigr),\qquad j=1,\ldots,k.$$
  Let $V$ be a continuous deterministic function on $[0,\tau]$ with values in
  the positive semidefinite $k\times k$ matrices, $V(0)=0$, and positive
  semidefinite increments, and let $M^{(\infty)}$ be the continuous centered
  Gaussian martingale with independent increments
  $M^{(\infty)}(t)-M^{(\infty)}(s)\sim N(0,V(t)-V(s))$. Suppose that for all
  $t\in[0,\tau]$, all $j,j'$, and all $\varepsilon>0$,
  $$\sum_h\int_0^tH_{jh}^{(n)}H_{j'h}^{(n)}\lambda_h^{(n)}\,ds\to_PV_{jj'}(t),
  \qquad
  \sum_h\int_0^t\bigl(H_{jh}^{(n)}\bigr)^2
  1_{\{|H_{jh}^{(n)}|>\varepsilon\}}\lambda_h^{(n)}\,ds\to_P0.$$
  Then $M^{(n)}\Rightarrow M^{(\infty)}$ in the Skorokhod space
  $D[0,\tau]^k$. This is the continuous-time analogue of item 1, and items
  12–14 are applications of it.

In the setting of item 14, write $s^{(0)}(\beta,u)=\mathbb E[Y(u)e^{\beta\cdot
Z}]$ and let $\bar e(u)$ be the limit in probability of $e(\beta,u)$ at the true
$\beta$. The **Breslow estimator** of the cumulative baseline hazard
$\Lambda_0(t)=\int_0^t\lambda_0$ is
$$\hat\Lambda_0(t)=\int_0^t
\frac{d\bar N(u)}{\sum_jY_j(u)\exp(\hat\beta\cdot Z_j)},$$
where $\bar N$ is the pooled counting process.

* **39. Breslow estimator.** Under the conditions of item 14 on $[0,\tau]$,
  with $y$ there replaced by $s^{(0)}$ bounded away from zero, the process
  $\sqrt n\,(\hat\Lambda_0-\Lambda_0)$ converges weakly on $[0,\tau]$ to
  $$W(t)-q(t)^\top G,\qquad q(t)=\int_0^t\bar e(u)\,d\Lambda_0(u),$$
  where $W$ is a centered Gaussian martingale with variance function
  $\int_0^td\Lambda_0(u)/s^{(0)}(\beta,u)$, $G$ is the normal limit of
  $\sqrt n(\hat\beta-\beta)$ in item 14, and $W$ and $G$ are independent. The
  asymptotic variance at $t$ is therefore
  $\int_0^td\Lambda_0/s^{(0)}+q(t)^\top\mathcal I^{-1}q(t)$, with
  $\mathcal I$ the information matrix of item 14. Estimated survival
  curves $\exp(-\hat\Lambda_0(t)e^{\hat\beta\cdot z})$ for a fixed covariate
  value follow by the functional delta method of SYNOPSIS103, item 26.

In **Aalen's additive hazards model**, subject $i$ has intensity
$Y_i(t)\bigl(\beta_0(t)+\beta_1(t)Z_{i1}(t)+\cdots+\beta_p(t)Z_{ip}(t)\bigr)$ with
unspecified locally integrable regression functions $\beta_j$ and predictable
covariates. Let $\mathbf Y(t)$ be the $n\times(p+1)$ matrix with rows
$Y_i(t)(1,Z_{i1}(t),\ldots,Z_{ip}(t))$, let $J(t)$ indicate that $\mathbf Y(t)$
has full column rank, and set $B_j(t)=\int_0^t\beta_j$.

* **40. Aalen's additive hazards estimator.** The least-squares estimator
  $$\hat B(t)=\int_0^tJ(u)\bigl(\mathbf Y(u)^\top\mathbf Y(u)\bigr)^{-1}
  \mathbf Y(u)^\top dN(u)$$
  satisfies $\hat B-B^*=\int J(\mathbf Y^\top\mathbf Y)^{-1}\mathbf Y^\top dM$,
  a local martingale, where $B^*=\int J\beta$. Suppose that, uniformly on
  $[0,t]$, $n^{-1}\mathbf Y^\top\mathbf Y$ and the corresponding normalized
  third-order sums $n^{-1}\sum_iY_{ij}Y_{ik}Y_{il}$ converge in probability
  to continuous limits, the limit $r^{(2)}(s)$ of $n^{-1}\mathbf Y^\top\mathbf Y$
  is nonsingular for $s\in[0,t]$, and
  $n^{-1/2}\max_{i,j}\sup_{s\le t}|Y_{ij}(s)|\to_P0$. Then
  $\sqrt n(\hat B-B)$ converges weakly in $D[0,t]^{p+1}$ to a centered
  Gaussian martingale. Its covariance function is consistently estimated by
  $n\int_0^\cdot J(\mathbf Y^\top\mathbf Y)^{-1}\mathbf Y^\top
  \mathop{\mathrm{diag}}(dN)\,\mathbf Y(\mathbf Y^\top\mathbf Y)^{-1}$. The
  slopes of $\hat B_j$ estimate the time-varying effects $\beta_j(t)$.

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

### Wald's identity, random sample sizes, and fixed-width intervals

In the setting of item 15, write $Z_i=\log(f_1(X_i)/f_0(X_i))$ and
$S_n=Z_1+\cdots+Z_n$, and suppose the observations are independent with a
common law $P_\theta$, not necessarily one of the two hypotheses. Wald's
identity $\mathbb E_\theta S_N=\mathbb E_\theta N\,\mathbb E_\theta Z$ is
[CKMA SYNOPSIS06](../lean-CKMA/SYNOPSIS06.md), item 47. The **operating
characteristic** is $L(\theta)=P_\theta(\text{accept }H_0)$.

* **41. Wald's fundamental identity and the operating characteristic.**
  Suppose $P_\theta(Z>0)>0$, $P_\theta(Z<0)>0$, and
  $\phi(t)=\mathbb E_\theta e^{tZ}<\infty$ for every real $t$. Then the
  stopping time $N$ of the sequential probability ratio test satisfies
  $$\mathbb E_\theta\bigl[e^{tS_N}\phi(t)^{-N}\bigr]=1$$
  for every real $t$ with $\phi(t)\ge1$. If $\mathbb E_\theta Z\ne0$, there is
  exactly one real $h=h(\theta)\ne0$ with $\phi(h)=1$, and neglecting the
  overshoot of $S_N$ beyond $\log A$ and $\log B$ gives
  $$L(\theta)\approx\frac{B^{h}-1}{B^{h}-A^{h}},\qquad
  \mathbb E_\theta N\approx
  \frac{L(\theta)\log A+(1-L(\theta))\log B}{\mathbb E_\theta Z}.$$
  At the two hypotheses $h(\theta_0)=1$ and $h(\theta_1)=-1$, and with the
  thresholds of item 15 these approximations return $1-\alpha$ and $\beta$.
  Wald also gives explicit upper and lower bounds for $L(\theta)$ in terms of
  the conditional law of the overshoot.

* **42. Anscombe's theorem.** Let $X_1,X_2,\ldots$ be independent and
  identically distributed with mean $\mu$ and variance $\sigma^2\in(0,\infty)$,
  and let $N_a$ be positive integer random variables with
  $N_a/a\to_Pk\in(0,\infty)$ as $a\to\infty$. Then
  $$\frac{S_{N_a}-N_a\mu}{\sigma\sqrt{N_a}}\Rightarrow N(0,1),$$
  with no independence required between $N_a$ and the observations. More
  generally, if $Y_n\Rightarrow Y$ and $(Y_n)$ is uniformly continuous in
  probability, in the sense that for each $\varepsilon>0$ there is $\delta>0$
  with $P(\max_{0\le j\le n\delta}|Y_{n+j}-Y_n|>\varepsilon)<\varepsilon$ for all
  $n$, then $Y_{N_a}\Rightarrow Y$.

Let $X_1,X_2,\ldots$ be independent $N(\mu,\sigma^2)$ with both parameters
unknown. A **fixed-width interval** of half-width $d>0$ and confidence
$1-\alpha$ has the form $[\bar X_N-d,\bar X_N+d]$. With $a$ the upper
$\alpha/2$ point of $N(0,1)$, the sample size that would be required if
$\sigma$ were known is $C=a^2\sigma^2/d^2$. No fixed sample size achieves
coverage at least $1-\alpha$ for every $\sigma$.

* **43. Stein's two-stage procedure and the Chow–Robbins rule.** Let
  $m\ge2$, let $t_{m-1}$ be the upper $\alpha/2$ point of the $t$ law with
  $m-1$ degrees of freedom, and let $S_m^2$ be the sample variance of the
  first $m$ observations. Stein's rule takes $N$ to be the smallest integer
  $n\ge m$ with $n\ge t_{m-1}^2S_m^2/d^2$. Then
  $$P_{\mu,\sigma}\bigl(|\bar X_N-\mu|\le d\bigr)\ge1-\alpha
  \quad\text{for all }\mu,\sigma,\qquad
  \lim_{d\to0}\frac{\mathbb EN}{C}=\frac{t_{m-1}^2}{a^2}>1.$$
  Exactness rests on the independence of $\bar X_n$ and $S_m^2$ for each
  $n\ge m$ (Basu's theorem, SYNOPSIS101, item 9). The Chow–Robbins rule
  $N=\inf\{n\ge n_0:n\ge a^2s_n^2/d^2\}$, with $n_0\ge2$ and $s_n^2$ the
  running sample variance, satisfies $N<\infty$ almost surely, $N/C\to1$
  almost surely and $\mathbb EN/C\to1$ as $d\to0$, and coverage tending to
  $1-\alpha$. Asymptotic efficiency is gained at the price of exact
  coverage. Chow and Robbins established the same asymptotic properties for
  any distribution with finite positive variance, using a slightly inflated
  variance estimate; item 42 supplies the coverage limit.

### Optimal change detection

For a change point $\nu\in\{0,1,2,\ldots\}$, let $P_\nu$ be the law under which
$X_1,\ldots,X_\nu$ are independent with density $f_0$ and
$X_{\nu+1},X_{\nu+2},\ldots$ are independent with density $f_1$, the two blocks
being independent; $P_\infty$ is the law with no change. Let
$L_n=f_1(X_n)/f_0(X_n)$. The **CUSUM statistic** is
$V_n=\max_{0\le k<n}\prod_{i=k+1}^nL_i$, which satisfies
$V_n=\max(1,V_{n-1})L_n$ with $V_0=1$, and the CUSUM procedure stops at
$T_{\mathrm{CS}}(A)=\inf\{n\ge1:V_n\ge A\}$. **Lorden's worst-case delay** of
a stopping time $T$ is
$$\mathop{\mathrm{ESADD}}(T)=\sup_{\nu\ge0}\mathop{\mathrm{ess\,sup}}
\mathbb E_\nu\bigl[(T-\nu)^+\mid X_1,\ldots,X_\nu\bigr],$$
and $\mathcal C_\gamma$ is the class of stopping times with average run length
to false alarm $\mathbb E_\infty T\ge\gamma$. Write $I=\mathbb E_0\log L_1$ for
the Kullback–Leibler divergence of $f_1$ from $f_0$.

* **44. Optimality of CUSUM.** For every $A>0$,
  $\mathbb E_\infty T_{\mathrm{CS}}(A)\ge A$, and the worst-case delay of the
  CUSUM procedure equals $\mathbb E_0T_{\mathrm{CS}}(A)$. If $\gamma>1$ and the
  threshold $A_\gamma$ is chosen so that $\mathbb E_\infty
  T_{\mathrm{CS}}(A_\gamma)=\gamma$, randomizing on the boundary if
  necessary, then
  $$\mathop{\mathrm{ESADD}}(T_{\mathrm{CS}}(A_\gamma))
  =\inf_{T\in\mathcal C_\gamma}\mathop{\mathrm{ESADD}}(T)$$
  (Moustakides). If $0<I<\infty$, then as $\gamma\to\infty$
  $$\inf_{T\in\mathcal C_\gamma}\mathop{\mathrm{ESADD}}(T)\sim
  \mathbb E_0T_{\mathrm{CS}}(A_\gamma)\sim\frac{\log\gamma}{I}$$
  (Lorden), and the same first-order asymptotics hold for the threshold
  $A=\gamma$. On the logarithmic scale, $W_n=\log V_n$ follows Page's
  recursion $W_n=\max(0,W_{n-1})+\log L_n$.

* **45. Shiryaev and Shiryaev–Roberts procedures.** Let $\nu$ be random,
  independent of the observations without change, with geometric law
  $P(\nu=k)=p(1-p)^k$, $k\ge0$, and let
  $\Pi_n=P(\nu<n\mid X_1,\ldots,X_n)$. Shiryaev's procedure stops at the first
  $n$ with $\Pi_n\ge B$. For every cost $c>0$ per observation of delay, it is
  optimal, with a threshold depending on $(c,p)$, for the Bayes risk
  $P(T\le\nu)+c\,\mathbb E(T-\nu)^+$. Also, if $0<\alpha<1$ and its threshold
  gives false-alarm probability exactly $\alpha$, it minimizes
  $\mathbb E(T-\nu\mid T>\nu)$ among stopping times with
  $P(T\le\nu)\le\alpha$; the threshold $B=1-\alpha$ guarantees
  $P(T\le\nu)\le\alpha$. As $p\to0$ the suitably normalized posterior odds
  tend to the **Shiryaev–Roberts statistic**
  $$R_n=\sum_{k=1}^n\prod_{i=k}^nL_i,\qquad R_n=(1+R_{n-1})L_n,\quad R_0=0.$$
  Under $P_\infty$ the process $R_n-n$ is a zero-mean martingale, so
  $T_{\mathrm{SR}}(A)=\inf\{n:R_n\ge A\}$ has
  $\mathbb E_\infty T_{\mathrm{SR}}(A)\ge A$ by optional sampling. If
  $L_1$ has a continuous law under $P_\infty$ and $A_\gamma$ gives
  $\mathbb E_\infty T_{\mathrm{SR}}(A_\gamma)=\gamma>1$, then $T_{\mathrm{SR}}(A_\gamma)$
  minimizes the integral average delay
  $\sum_{k\ge0}\mathbb E_k(T-k)^+/\mathbb E_\infty T$ over
  $\mathcal C_\gamma$.

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

### Covariance models for random fields

A complex function $K$ on $\mathbb R^d$ is **positive definite** when
$\sum_{j,k}c_j\bar c_kK(x_j-x_k)\ge0$ for all finite families of points and
complex coefficients. A field on $\mathbb R$ is **mean-square differentiable**
when its difference quotients converge in $L^2$, and **$m$ times mean-square
differentiable** when this holds iteratively.

* **46. Bochner's theorem and the Matérn family.** A function $K$ on
  $\mathbb R^d$ is the autocovariance function of a weakly stationary,
  mean-square continuous, complex random field if and only if
  $$K(x)=\int_{\mathbb R^d}e^{i\omega\cdot x}\,F(d\omega)$$
  for a finite positive measure $F$, the **spectral measure**. This is
  Bochner's theorem, [CKMA SYNOPSIS28](../lean-CKMA/SYNOPSIS28.md), item 30.
  On $\mathbb R$, the field is $m$ times mean-square differentiable if and
  only if $K$ has a finite derivative of order $2m$ at $0$, equivalently
  $\int\omega^{2m}F(d\omega)<\infty$; the derivative then has autocovariance
  $-K''$ when $m=1$. The **Matérn covariance**
  $$K(x)=\phi\,(\alpha|x|)^\nu\mathcal K_\nu(\alpha|x|),\qquad
  \phi,\alpha,\nu>0,$$
  with $\mathcal K_\nu$ the modified Bessel function of the second kind, is
  positive definite on every $\mathbb R^d$, with isotropic spectral density
  proportional to $(\alpha^2+|\omega|^2)^{-\nu-d/2}$. On $\mathbb R$ the
  corresponding field is $m$ times mean-square differentiable if and only if
  $\nu>m$. For $\nu=1/2$ the covariance is exponential, and for
  $\nu=m+1/2$ it is $e^{-\alpha|x|}$ times a polynomial of degree $m$ in
  $|x|$. Item 19 explains why the smoothness parameter $\nu$ dominates the
  behavior of kriging under infill asymptotics.

A field $Z$ on $\mathbb R^d$ is **intrinsically stationary** when its
increments $Z(x+h)-Z(x)$ have mean zero and a variance depending only on $h$.
Its **semivariogram** is $\gamma(h)=\tfrac12\mathop{\mathrm{Var}}(Z(x+h)-Z(x))$.
A symmetric function $\gamma$ is **conditionally negative definite** when
$\sum_{j,k}c_jc_k\gamma(x_j-x_k)\le0$ whenever $\sum_jc_j=0$.

* **47. Valid semivariograms.** For an intrinsically stationary field and
  real $c_j$ with $\sum_jc_j=0$,
  $$\mathop{\mathrm{Var}}\Bigl(\sum_jc_jZ(x_j)\Bigr)
  =-\sum_{j,k}c_jc_k\gamma(x_j-x_k),$$
  so every semivariogram is conditionally negative definite with
  $\gamma(0)=0$. Conversely, a continuous symmetric function with
  $\gamma(0)=0$ is the semivariogram of some intrinsically stationary field
  if and only if it is conditionally negative definite, and if and only if
  $$\gamma(x)=\int_{\mathbb R^d}\bigl(1-\cos(\omega\cdot x)\bigr)F(d\omega)
  +x^\top Qx$$
  for a symmetric positive measure $F$ with
  $\int|\omega|^2(1+|\omega|^2)^{-1}F(d\omega)<\infty$ and a positive
  semidefinite matrix $Q$. If $Z$ is weakly stationary with covariance $K$,
  then $\gamma=K(0)-K$ is bounded; unbounded examples are
  $\gamma(h)=|h|^s$, from fractional Brownian fields when $0<s<2$ and
  from a field linear in $x$ when $s=2$.
  Ordinary kriging, item 31 with a constant mean, can be written with
  $\gamma$ in place of $K$ because its weights sum to one.

### Likelihood and second-order structure of point patterns

* **48. Poisson likelihood.** Let $S\subset\mathbb R^d$ be bounded and let
  $\rho_1,\rho_2\ge0$ be intensity functions on $S$ with finite integrals
  $\mu_i(S)=\int_S\rho_i$ and with $\rho_2>0$ wherever $\rho_1>0$. Then the
  Poisson process on $S$ with intensity $\rho_1$ is absolutely continuous
  with respect to that with intensity $\rho_2$, with density
  $$f(x)=\exp\bigl(\mu_2(S)-\mu_1(S)\bigr)\prod_{\xi\in x}
  \frac{\rho_1(\xi)}{\rho_2(\xi)}$$
  at finite configurations $x\subset S$. Taking $\rho_2\equiv1$, the
  log-likelihood of a parametric intensity $\rho_\theta$ is
  $$\ell(\theta)=\sum_{\xi\in x}\log\rho_\theta(\xi)-\int_S\rho_\theta(\xi)\,d\xi,$$
  up to a constant. For a log-linear intensity
  $\rho_\theta=\exp(\theta\cdot z)$ it is concave, and its score
  $\sum_{\xi\in x}z(\xi)-\int_Sz\rho_\theta$ has mean zero by Campbell's
  formula, [CKMA SYNOPSIS06](../lean-CKMA/SYNOPSIS06.md), item 54. Item 20 is
  the constant case. On all of $\mathbb R^d$, by contrast, homogeneous
  Poisson processes of different intensities are mutually singular.

For a point process with intensity function $\rho$ and second-order product
density $\rho^{(2)}$, the **pair correlation function** is
$g(\xi,\eta)=\rho^{(2)}(\xi,\eta)/(\rho(\xi)\rho(\eta))$. When $g(\xi,\eta)$
depends only on $\xi-\eta$, the **$K$-function** and **$L$-function** are
$$K(r)=\int_{|\xi|\le r}g(\xi)\,d\xi,\qquad L(r)=\bigl(K(r)/\omega_d\bigr)^{1/d},$$
where $\omega_d$ is the volume of the unit ball in $\mathbb R^d$.

* **49. Second-order summaries under complete spatial randomness.** For a
  Poisson process, $g\equiv1$, so $K(r)=\omega_dr^d$ and $L(r)=r$; in the
  plane $K(r)=\pi r^2$. If $g$ is isotropic, then
  $K(r)=\sigma_d\int_0^rt^{d-1}g(t)\,dt$ with $\sigma_d$ the surface area of
  the unit sphere. For a stationary process of intensity $\rho$,
  $\rho K(r)$ is the expected number of further points within distance $r$
  of a typical point, the expectation being under the Palm distribution
  described in CKMA SYNOPSIS06, item 70. The $K$-function is unchanged by
  independent thinning. For the planar Thomas cluster process, with parent
  intensity $\kappa$ and Gaussian dispersal of standard deviation $\omega$,
  $$K(r)=\pi r^2+\frac{1-\exp(-r^2/(4\omega^2))}{\kappa},$$
  exceeding the Poisson value; values of $L(r)-r$ above zero thus indicate
  clustering and values below zero indicate regularity at scale $r$.

<a id="synopsis-108e"></a>

## 108E. Extreme-Value Statistics

Let $M_n=\max(X_1,\ldots,X_n)$ for independent copies of a random variable
with distribution function $F$, and write $x_F=\sup\{x:F(x)<1\}$.

* **21. Fisher–Tippett–Gnedenko theorem.** The nondegenerate distributional
  limits of $(M_n-b_n)/a_n$, with $a_n>0$, are the generalized extreme-value
  laws
  $$G_\gamma(x)=\exp\bigl(-(1+\gamma x)^{-1/\gamma}\bigr),
  \qquad\gamma\neq0,\;1+\gamma x>0,$$
  and $G_0(x)=\exp(-e^{-x})$. For $\gamma>0$, $F$ lies in the domain of
  attraction of $G_\gamma$ if and only if $x_F=\infty$ and
  $$\frac{1-F(tx)}{1-F(t)}\to x^{-1/\gamma},\qquad x>0,\quad t\to\infty,$$
  that is, $1-F$ is regularly varying with index $-1/\gamma$. For
  $\gamma<0$, it does so if and only if $x_F<\infty$ and
  $$\frac{1-F(x_F-(tx)^{-1})}{1-F(x_F-t^{-1})}\to x^{1/\gamma},
  \qquad x>0,\quad t\to\infty.$$
  For $\gamma=0$, it does so if and only if there is a positive function
  $a$ with
  $$\frac{1-F(t+xa(t))}{1-F(t)}\to e^{-x},\qquad x\in\mathbb R,\quad
  t\uparrow x_F;$$
  one may then take the mean excess
  $a(t)=\int_t^{x_F}(1-F(s))\,ds/(1-F(t))$, which is finite for $t<x_F$.
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

Let $U$ be the left-continuous inverse of $1/(1-F)$, so that $U(t)$ is the
quantile of order $1-1/t$. A **second-order condition** with index $\gamma>0$
and second-order parameter $\rho<0$ holds when, for a function $A$ of
constant sign with $A(t)\to0$,
$$\lim_{t\to\infty}\frac{U(tx)/U(t)-x^\gamma}{A(t)}=x^\gamma\,\frac{x^\rho-1}{\rho},
\qquad x>0.$$

* **24. Hill estimator.** Suppose $1-F$ is regularly varying of index
  $-1/\gamma$ with $\gamma>0$, and suppose the second-order condition above
  holds. If $k\to\infty$, $k/n\to0$, and $\sqrt k\,A(n/k)\to\lambda\in\mathbb R$,
  then
  $$\sqrt k\,(H_{k,n}-\gamma)\Rightarrow N\Bigl(\frac{\lambda}{1-\rho},\gamma^2\Bigr).$$
  In particular the limit is $N(0,\gamma^2)$ when $\sqrt k\,A(n/k)\to0$. Larger
  $k$ reduces variance at the price of the asymptotic bias $\lambda/(1-\rho)$.

### Exceedances and block maxima

* **50. Poisson approximation for exceedances.** For independent
  observations, $0\le\tau\le\infty$, and real $u_n$,
  $$P(M_n\le u_n)\to e^{-\tau}\quad\text{if and only if}\quad
  n\bigl(1-F(u_n)\bigr)\to\tau.$$
  For finite $\tau$ the number of exceedances of $u_n$ among
  $X_1,\ldots,X_n$ then converges in law to a Poisson law with mean $\tau$,
  by CKMA SYNOPSIS06, item 38. For $0<\tau<\infty$, levels $u_n$ with
  $n(1-F(u_n))\to\tau$ exist if and only if
  $(1-F(x))/(1-F(x-))\to1$ as $x\uparrow x_F$. Hence the Poisson and
  geometric laws, whose atoms do not become negligible in this ratio, are in
  no domain of attraction. Item 23 replaces $e^{-\tau}$ by $e^{-\theta\tau}$
  for dependent sequences.

The **return level** $z_p$ of a law $G$ is the level exceeded with probability
$p$, $G(z_p)=1-p$. For block maxima with the generalized extreme-value law of
location $\mu$, scale $\sigma>0$, and shape $\gamma$,
$$z_p=\mu-\frac\sigma\gamma\Bigl[1-\bigl(-\log(1-p)\bigr)^{-\gamma}\Bigr]
\quad(\gamma\ne0),\qquad z_p=\mu-\sigma\log\bigl(-\log(1-p)\bigr)\quad(\gamma=0).$$

* **51. Likelihood for block maxima.** Let $Z_1,\ldots,Z_m$ be independent
  with the generalized extreme-value law
  $G_\gamma((z-\mu)/\sigma)$, whose support depends on the parameters. If
  $\gamma>-1/2$, the maximum likelihood estimator of $(\mu,\sigma,\gamma)$ is
  regular: consistent, asymptotically normal, and efficient with the inverse
  Fisher information as asymptotic covariance. For $-1<\gamma<-1/2$, maximum
  likelihood estimators generally exist but do not have the standard
  asymptotics, and for $\gamma<-1$ they are generally not obtainable. In the
  regular range, estimated return levels and their intervals follow by the
  delta method or by inverting the likelihood-ratio test of SYNOPSIS103,
  item 7. The
  generalized extreme-value law is the limit of item 21, so the block length
  governs a bias of the same kind as the choice of $k$ in item 24.

## Reference guide

### Correspondence with the subdivisions

- **[108A](#synopsis-108a)**: Brockwell and Davis, Brillinger, Priestley, and
  Hannan and Deistler carry the Wold decomposition, autoregressive estimation,
  Bartlett's formula, and spectral estimation. Hall and Heyde carry the
  martingale central limit theorem. Durbin and Koopman carry the Kalman
  filter. Cappé, Moulines, and Rydén carry hidden Markov likelihoods.
  Giraitis, Koul, and Surgailis carry long memory. Kutoyants and Liptser and
  Shiryaev carry likelihood theory for diffusions. Fan and Yao, and Douc,
  Moulines, and Stoffer, carry the block bootstrap for series. Brockwell and
  Davis also carry the Herglotz representation, the Durbin–Levinson
  recursion, Kolmogorov's formula, and the Whittle asymptotics; Douc,
  Moulines, and Stoffer carry GARCH stationarity; Basawa and Prakasa Rao
  carry likelihood inference for finite Markov chains.
- **[108B](#synopsis-108b)**: Andersen, Borgan, Gill, and Keiding, Fleming
  and Harrington, Kalbfleisch and Prentice, and Aalen, Borgan, and Gjessing
  carry the Nelson–Aalen estimator, the Kaplan–Meier estimator, and the Cox
  partial likelihood. Andersen, Borgan, Gill, and Keiding carry Rebolledo's
  theorem, the Breslow estimator, and Aalen's additive model.
- **[108C](#synopsis-108c)**: Wald carries the sequential probability ratio
  test. Ghosh, Mukhopadhyay, and Sen, and Tartakovsky, Nikiforov, and
  Basseville carry sequential estimation and change detection: Anscombe's
  theorem and fixed-width intervals in the former, the optimality of CUSUM,
  Shiryaev, and Shiryaev–Roberts procedures in the latter. Csörgő and
  Horváth carry the bridge limit for the CUSUM.
- **[108D](#synopsis-108d)**: Stein carries kriging, covariance
  misspecification, spectral and Matérn models, and semivariograms. Møller and Waagepetersen, and Daley and Vere-Jones, carry
  point processes. Rue and Held carry Gaussian Markov random fields.
- **[108E](#synopsis-108e)**: Leadbetter, Lindgren, and Rootzén, Embrechts,
  Klüppelberg, and Mikosch, Resnick, and de Haan and Ferreira carry domains
  of attraction, threshold excesses, the extremal index, and the Hill
  estimator. Coles is the applied companion and carries block-maximum
  likelihood and return levels.

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
now states the second-order condition and the bias term of de Haan and
Ferreira, Theorem 3.2.5.

For the third expansion the following passages were read. Brockwell and
Davis (1991): Theorem 4.3.1 (Herglotz), Theorem 4.4.2 (ARMA spectral
density), Proposition 5.2.1 (Durbin–Levinson), Theorem 5.8.1 (Kolmogorov's
formula, proved there for a continuous spectral density bounded away from
zero, with the general case referred to Hannan), Theorems 8.1.1–8.1.2, and
Theorems 10.8.1–10.8.2 with their parameter set, which give item 35 for
independent identically distributed innovations without Gaussianity.
Douc, Moulines, and Stoffer, Theorems 4.13 and 4.18 and Remark 4.16, for
item 36. Basawa and Prakasa Rao, Chapter 4, Section 2, for item 37.
Andersen, Borgan, Gill, and Keiding: Theorem II.5.1 and its
counting-process form (2.5.6)–(2.5.8) for item 38, Theorem VII.2.3 for
item 39, and Section VII.4 with Theorem VII.4.1 for item 40. Wald,
Appendix A.2.2–A.2.3, for the fundamental identity and the operating
characteristic of item 41, written here with $A<1<B$ as in item 15 (Wald
labels the upper threshold $A$). Ghosh, Mukhopadhyay, and Sen: Theorems
2.7.1–2.7.2 (Anscombe), Theorem 6.2.1 (Stein), and Theorem 8.2.1
(Chow–Robbins, stated there for normal data). Tartakovsky, Nikiforov, and
Basseville: Theorems 8.2.1 and 8.2.3 and Lemma 8.2.1 for item 44,
Theorems 7.1.1–7.1.2, formula (7.6), and Theorem 7.6.1 for item 45. Stein
(1999): Sections 2.4 and 2.6 on mean-square differentiability, Section 2.5,
Theorem 1, Section 2.7 on the Matérn class,
Section 2.9 on intrinsic random functions and semivariograms (Matheron's
representation with $r=0$), and Section 2.10. Møller and Waagepetersen:
Proposition 3.8, Definitions 4.4 and 4.6 with (4.5)–(4.6),
Proposition 4.3, and Example 5.3 with (5.10). de Haan and Ferreira:
Theorems 1.2.1 and 3.2.5, used to sharpen items 21 and 24. Leadbetter,
Lindgren, and Rootzén: Theorems 1.5.1 and 1.7.13 for item 50. Coles,
Sections 3.3.2–3.3.3, for item 51, where the regularity ranges are
Smith's (1985) results as reported by Coles. The Dickey–Fuller limit in
terms of Brownian functionals was not added: Brockwell and Davis (2016),
Section 6.3, gives only the test and its quantiles, and Fuller is not in
the local directory.

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
- [Basawa and Prakasa Rao, *Statistical Inference for Stochastic Processes*](../lean-CKMA/References/BasawaPrakasaRao1980StatisticalInferenceStochasticProcesses-AcademicPress.ProbMathStat.pdf).
- [Brockwell and Davis, *Introduction to Time Series and Forecasting*](../lean-CKMA/References/BrockwellDavis2016IntroductionTimeSeriesForecasting3rdEd-Springer.STS.pdf).
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
