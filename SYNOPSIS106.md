# Synopsis: Dependent data and stochastic models

Part of the [mathematical synopsis series](SYNOPSIS.md).
[Bibliographical scope and references](CKSD-bib.md#cks-106).

This synopsis follows Section 106. Subdivision 106A is time series,
inference for stochastic processes, and spatial prediction and point
patterns. Subdivision 106B is survival analysis and counting processes,
sequential analysis and anytime-valid inference, and extreme values. The
martingale convergence and maximal inequalities are
[CKMA SYNOPSIS06](../lean-CKMA/SYNOPSIS06.md), items 42 and 43. Poisson point
processes are CKMA SYNOPSIS06, items 53 and 70. Equivalence of Gaussian
measures is [CKMA SYNOPSIS09](../lean-CKMA/SYNOPSIS09.md), item 65.
Semiparametric efficiency is [SYNOPSIS102](SYNOPSIS102.md), item 34. Subsampling is [SYNOPSIS102](SYNOPSIS102.md), item 57, and local
asymptotic normality is [SYNOPSIS102](SYNOPSIS102.md), item 13.

Numbered definitions and results have stable identifiers. Additions take the
next free number and are placed beside related material; numbers need not
increase in reading order. Proofs are outside the scope of this synopsis.

<a id="synopsis-106a"></a>

## 106A. Time Series, Stochastic Processes, and Spatial Data

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

* **2. Wold decomposition and causal autoregression.** Suppose the
  innovation variance $\sigma^2=\mathbb E\varepsilon_t^2$ is positive. There
  exist coefficients $\psi_j$ with $\psi_0=1$ and
  $\sum_{j\ge0}\psi_j^2<\infty$, and a process $(V_t)$ orthogonal to every
  innovation, such that
  $$X_t=\sum_{j=0}^\infty\psi_j\varepsilon_{t-j}+V_t,$$
  with convergence in $L^2$. The process $(V_t)$ is deterministic, in the
  sense that $V_t$ lies in the remote-past subspace
  $\bigcap_m\overline{\mathop{\mathrm{span}}}\{X_s:s\le m\}$. The process is
  purely nondeterministic when $V_t=0$. Let $(Z_t)$ be white noise of
  variance $\sigma^2>0$. If the polynomial $1-\varphi_1z-\cdots-\varphi_pz^p$
  has no zero in the closed unit disk, the autoregression
  $X_t=\varphi_1X_{t-1}+\cdots+\varphi_pX_{t-p}+Z_t$ has a unique weakly
  stationary solution; it is $X_t=\sum_{j\ge0}\psi_jZ_{t-j}$ with
  $\sum_j|\psi_j|<\infty$, and $Z_t$ is then the innovation
  $X_t-P_{t-1}X_t$.

Let $\gamma(h)=\mathop{\mathrm{Cov}}(X_{t+h},X_t)$ and
$\rho(h)=\gamma(h)/\gamma(0)$. For an autoregression of order $p$, the
Yule–Walker equation is $\Gamma_p\varphi=\gamma_p$, where $\Gamma_p$ is the
Toeplitz matrix $(\gamma(i-j))_{1\le i,j\le p}$ and
$\gamma_p=(\gamma(1),\ldots,\gamma(p))^\top$. From $X_1,\ldots,X_n$, the
sample autocovariances are
$\hat\gamma(h)=n^{-1}\sum_{t=1}^{n-h}(X_{t+h}-\bar X_n)(X_t-\bar X_n)$ for
$0\le h<n$, and $\hat\rho(h)=\hat\gamma(h)/\hat\gamma(0)$.

* **3. Yule–Walker estimator.** Let $(X_t)$ be the causal autoregression of
  order $p$ of item 2, driven by independent identically distributed $Z_t$
  with mean $0$ and variance $\sigma^2>0$. Let $\hat\varphi$ solve
  $\hat\Gamma_p\hat\varphi=\hat\gamma_p$, with the sample autocovariances in
  place of $\gamma$, and let $\hat\sigma^2=\hat\gamma(0)-\hat\varphi^\top\hat\gamma_p$.
  Then
  $$\sqrt n\,(\hat\varphi-\varphi)\Rightarrow N(0,\sigma^2\Gamma_p^{-1}),
  \qquad\hat\sigma^2\to_P\sigma^2.$$
  The least-squares and Gaussian maximum likelihood estimators of $\varphi$
  have the same limit law (item 17). For Gaussian $Z_t$, $\sigma^{-2}\Gamma_p$
  is the limiting Fisher information per observation for $\varphi$ (item 5).

* **4. Bartlett's theorem.** Let $X_t-\mu=\sum_{j=-\infty}^\infty\psi_jZ_{t-j}$
  with $\sum_j|\psi_j|<\infty$ and with $(Z_t)$ independent identically
  distributed, of mean $0$, variance $\sigma^2>0$, and $\mathbb EZ_t^4<\infty$.
  For each fixed $h$, the vector
  $\sqrt n\,(\hat\rho(1)-\rho(1),\ldots,\hat\rho(h)-\rho(h))$ converges in law
  to $N(0,W)$, where Bartlett's formula gives
  $$w_{ij}=\sum_{k=1}^\infty\bigl(\rho(k+i)+\rho(k-i)-2\rho(i)\rho(k)\bigr)
  \bigl(\rho(k+j)+\rho(k-j)-2\rho(j)\rho(k)\bigr).$$
  If the observations are independent and identically distributed with
  finite positive variance, then for each fixed $h\ge1$,
  $$\sqrt n\,\hat\rho(h)\Rightarrow N(0,1),$$
  and the limits at any fixed finite set of positive lags are independent.

* **5. Gaussian ARMA likelihood.** Let $(X_t)$ be an ARMA$(p,q)$ process
  satisfying the hypotheses of item 17, with Gaussian innovations, and let
  $\mathcal I_n(\beta,\sigma^2)$ be the Fisher information matrix of
  $(X_1,\ldots,X_n)$ for $(\beta,\sigma^2)$. Then
  $$n^{-1}\mathcal I_n(\beta,\sigma^2)\to
  \begin{pmatrix}W(\beta)&0\\0&1/(2\sigma^4)\end{pmatrix},$$
  with $W(\beta)$ as in item 17. Thus the common limit covariance
  $W(\beta)^{-1}$ of the Gaussian maximum likelihood, least-squares, and
  Whittle estimators in item 17 is the inverse of the limiting Fisher
  information per observation for $\beta$.

Let the spectral density in the Brockwell–Davis normalization be
$$f(\omega)=\frac1{2\pi}\sum_{h=-\infty}^\infty\gamma(h)e^{-ih\omega},
\qquad\omega\in[-\pi,\pi],$$
and let the periodogram be
$$I_n(\omega)=\frac1{2\pi n}\Bigl|\sum_{t=1}^n X_te^{-it\omega}\Bigr|^2.$$
A **lag window** is an even, piecewise continuous function $w$, continuous at
$0$, with $w(0)=1$, $|w|\le1$, and $w(x)=0$ for $|x|>1$. Continuity at $0$
gives $w(h/r)\to1$ for each fixed lag $h$ as $r\to\infty$; without it the
mean of the lag-window estimator below need not converge to $f$. The lag-window estimator with
truncation $r$ is
$$\hat f_n(\omega)=\frac1{2\pi}\sum_{|h|\le r}w(h/r)\hat\gamma(h)e^{-ih\omega}.$$
The Fourier frequencies are $2\pi k/n$ with $k\in\mathbb Z$ and
$-\pi<2\pi k/n\le\pi$.

* **6. Periodogram and lag-window estimation.** Let
  $X_t=\sum_{j=-\infty}^\infty\psi_jZ_{t-j}$ with $\sum_j|\psi_j|<\infty$ and
  $(Z_t)$ independent identically distributed with mean $0$ and variance
  $\sigma^2>0$, and suppose $f(\lambda)>0$ for all $\lambda$. Let
  $0<\lambda_1<\cdots<\lambda_m<\pi$ be fixed, and let $\omega_{n,j}$ be a
  Fourier frequency nearest to $\lambda_j$. Then
  $(I_n(\omega_{n,1})/f(\lambda_1),\ldots,I_n(\omega_{n,m})/f(\lambda_m))$
  converges in law to a vector of independent standard exponential random
  variables. In particular $I_n(\omega_{n,j})$ does not converge in
  probability to $f(\lambda_j)$. If in addition
  $\sum_j|\psi_j||j|^{1/2}<\infty$ and $\mathbb EZ_t^4<\infty$, and if
  $r=r_n\to\infty$ and $r/n\to0$, then for every $\omega\in[0,\pi]$,
  $\mathbb E\hat f_n(\omega)\to f(\omega)$ and
  $$\frac nr\mathop{\mathrm{Var}}\bigl(\hat f_n(\omega)\bigr)\to
  c_\omega f(\omega)^2\int_{-1}^1 w(u)^2\,du,$$
  with $c_\omega=1$ for $0<\omega<\pi$ and $c_\omega=2$ for $\omega\in\{0,\pi\}$.
  Hence $\hat f_n(\omega)\to f(\omega)$ in mean square.

Consider a linear state-space model $x_{t+1}=F_tx_t+w_t$ and
$y_t=H_tx_t+v_t$, with Gaussian white noises $w_t$ and $v_t$ of covariances
$Q_t$ and $R_t$, independent of each other and of a Gaussian initial state.
Write $x_{t\mid t-1}$ and $P_{t\mid t-1}$ for the conditional mean and
covariance of $x_t$ given $y_1,\ldots,y_{t-1}$.

* **7. Kalman filter.** Suppose every innovation covariance
  $\Sigma_t=H_tP_{t\mid t-1}H_t^\top+R_t$ is nonsingular, and let $x_{1\mid0}$
  and $P_{1\mid0}$ be the mean and covariance of the initial state. Then the
  conditional law of $x_t$ given $y_1,\ldots,y_t$ is Gaussian with mean
  $x_{t\mid t}$ and covariance $P_{t\mid t}$, where, with the gain
  $K_t=P_{t\mid t-1}H_t^\top\Sigma_t^{-1}$,
  $$x_{t\mid t}=x_{t\mid t-1}+K_t(y_t-H_tx_{t\mid t-1}),\qquad
  P_{t\mid t}=P_{t\mid t-1}-K_tH_tP_{t\mid t-1},$$
  and $x_{t+1\mid t}=F_tx_{t\mid t}$,
  $P_{t+1\mid t}=F_tP_{t\mid t}F_t^\top+Q_t$. The innovations
  $y_t-H_tx_{t\mid t-1}$, $t=1,\ldots,n$, are independent, with laws
  $N(0,\Sigma_t)$, and the density of $(y_1,\ldots,y_n)$ is the product of
  their densities.

* **8. Hidden Markov likelihood.** Let $(S_t)_{t\ge1}$ be a Markov chain on
  $\{1,\ldots,m\}$ with initial law $\nu$ (a row vector) and transition
  matrix $P$, and let $Y_1,Y_2,\ldots$ be conditionally independent given
  $(S_t)$, with $Y_t$ having density $g_{S_t}$. Write
  $D(y)=\mathop{\mathrm{diag}}(g_1(y),\ldots,g_m(y))$ and $\mathbf 1$ for the
  vector of ones. Then the density of $(Y_1,\ldots,Y_n)$ is
  $$p(y_1,\ldots,y_n)=\nu D(y_1)PD(y_2)\cdots PD(y_n)\mathbf 1.$$
  Equivalently, the forward variables $\alpha_1=\nu D(y_1)$ and
  $\alpha_t=\alpha_{t-1}PD(y_t)$ satisfy
  $\alpha_t(i)=p(y_1,\ldots,y_t,S_t=i)$ and $p(y_1,\ldots,y_n)=\alpha_n\mathbf 1$,
  so the likelihood is computed with $O(nm^2)$ arithmetic operations.

* **9. Long memory.** Suppose $\gamma(h)\sim c\,h^{2d-1}$ as $h\to\infty$,
  with $c>0$ and $d\in(0,1/2)$. Then, as $n\to\infty$,
  $$\mathop{\mathrm{Var}}(\bar X_n)\sim\frac{c}{d(2d+1)}\,n^{2d-1}.$$

* **10. Likelihood for an ergodic diffusion.** Let
  $dX_t=\theta h(X_t)\,dt+\sigma(X_t)\,dW_t$, $\theta\in\mathbb R$, with $h$
  and $\sigma$ continuous and $\sigma>0$, be observed continuously on
  $[0,T]$. Suppose that at the true $\theta$ the equation has a unique
  solution in law, which is ergodic with invariant probability $\mu_\theta$,
  and that
  $$0<I(\theta)=\int\frac{h(x)^2}{\sigma(x)^2}\,\mu_\theta(dx)<\infty.$$
  The maximum likelihood estimator is
  $$\hat\theta_T=\frac{\int_0^T h(X_t)\sigma(X_t)^{-2}\,dX_t}
  {\int_0^T h(X_t)^2\sigma(X_t)^{-2}\,dt},$$
  and as $T\to\infty$,
  $\sqrt T(\hat\theta_T-\theta)\Rightarrow N(0,I(\theta)^{-1})$. The
  experiments are locally asymptotically normal at $\theta$ with rate
  $\sqrt T$ and information $I(\theta)$, so the estimator attains the bound
  of SYNOPSIS102, item 16.

Let $\sigma_\infty^2=\sum_{k=-\infty}^\infty\gamma(k)$ be the long-run
variance, assumed positive and finite.

For a strictly stationary sequence, the **strong mixing coefficients** are
$\alpha(k)=\sup|P(A\cap B)-P(A)P(B)|$, over $A\in\sigma(X_s:s\le0)$ and
$B\in\sigma(X_s:s\ge k)$. For a block length $b\le n$ and $\ell=\lfloor n/b\rfloor$,
the **moving-block bootstrap** sample concatenates $\ell$ blocks
$(X_i,\ldots,X_{i+b-1})$ whose starting indices are drawn independently and
uniformly from $\{1,\ldots,n-b+1\}$; let $\bar X_n^*$ be its mean and
$\mathbb E^*$, $P^*$ the expectation and probability given the data.

* **11. Moving-block bootstrap.** Let $(X_t)$ be strictly stationary with
  mean $\mu$, and suppose that for some $\delta>0$,
  $\mathbb E|X_1|^{2+\delta}<\infty$ and
  $\sum_k\alpha(k)^{\delta/(2+\delta)}<\infty$. Then $\sigma_\infty^2$ is
  finite; assume it is positive. If $b\to\infty$ and $b/n\to0$, then
  $$\sup_x\Bigl|P^*\bigl(\sqrt{\ell b}\,(\bar X_n^*-\mathbb E^*\bar X_n^*)\le
  x\bigr)-P\bigl(\sqrt n\,(\bar X_n-\mu)\le x\bigr)\Bigr|\to_P0,$$
  and both laws are asymptotically $N(0,\sigma_\infty^2)$.

### Mean estimation and innovation likelihoods

* **12. Long-run variance of a sample mean.** For a stationary process with
  absolutely summable autocovariances $\gamma(h)$,
  $$n\mathop{\mathrm{Var}}(\bar X_n)\to
  v=\sum_{h\in\mathbb Z}\gamma(h)=2\pi f(0),$$
  where $f(\omega)=(2\pi)^{-1}\sum_h\gamma(h)e^{-ih\omega}$.
  For a linear process $X_t-\mu=\sum_{j\ge0}\psi_j\varepsilon_{t-j}$ with
  absolutely summable coefficients and independent identically distributed
  innovations of mean zero and finite variance $\sigma^2$,
  $\sqrt n(\bar X_n-\mu)\Rightarrow N(0,v)$, where
  $v=\sigma^2(\sum_j\psi_j)^2$. If moreover $v>0$ and $\hat v_n\to_Pv$, then
  for $z$ the upper $\alpha/2$ point of $N(0,1)$,
  $P\bigl(|\bar X_n-\mu|\le z(\hat v_n/n)^{1/2}\bigr)\to1-\alpha$.

* **13. Gaussian likelihood through innovations.** For a nondegenerate
  Gaussian observation vector, let
  $\hat X_t=\mathbb E[X_t\mid X_1,\ldots,X_{t-1}]$ and
  $v_t=\mathop{\mathrm{Var}}(X_t\mid X_1,\ldots,X_{t-1})$.
  The innovations $X_t-\hat X_t$ are independent centered normals and
  $$\ell_n=-\tfrac12\sum_{t=1}^n
  \left[\log(2\pi v_t)+\frac{(X_t-\hat X_t)^2}{v_t}\right].$$
  For a state-space model as in item 7, $\hat X_t$ and $v_t$ are the
  quantities $H_tx_{t\mid t-1}$ and $\Sigma_t$ of the Kalman filter.

### Spectral representation and linear prediction

A complex function $\gamma$ on the integers is **nonnegative definite** when
$\sum_{r,s=1}^n a_r\gamma(r-s)\bar a_s\ge0$ for all $n$ and all complex
$a_1,\ldots,a_n$. An **ARMA$(p,q)$ process** is a weakly stationary solution of
$\varphi(B)X_t=\theta(B)Z_t$, where $B$ is the backward shift, $(Z_t)$ is white
noise of variance $\sigma^2$, $\varphi(z)=1-\varphi_1z-\cdots-\varphi_pz^p$, and
$\theta(z)=1+\theta_1z+\cdots+\theta_qz^q$.

* **14. Herglotz theorem and rational spectral densities.** A complex
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

* **15. Durbin–Levinson algorithm and partial autocorrelation.** If
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

* **16. Kolmogorov's formula for the prediction error.** Let $(X_t)$ be a
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

* **17. Asymptotic covariance of ARMA estimators.** Let $(X_t)$ be an
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
  Yule–Walker estimator in item 3. Under Gaussian innovations $W(\beta)$ is
  the limiting Fisher information per observation, item 5.

A **GARCH$(1,1)$ process** is a solution of $X_t=\sigma_t\varepsilon_t$ and
$\sigma_t^2=\alpha_0+\alpha_1X_{t-1}^2+\beta_1\sigma_{t-1}^2$, where
$(\varepsilon_t)_{t\in\mathbb Z}$ is independent and identically distributed
with mean $0$ and variance $1$, $\alpha_0>0$, and $\alpha_1,\beta_1\ge0$. It is
**nonanticipative** when $\varepsilon_t$ is independent of
$\{\sigma_s^2:s\le t\}$ for every $t$.

* **18. Stationarity of GARCH$(1,1)$.** Let
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

* **19. Maximum likelihood for a finite Markov chain.** Conditionally on
  $X_0$, the maximum likelihood estimator of $p_{ij}$ is
  $\hat p_{ij}=n_{ij}/n_i$. As $n\to\infty$, $n_i/n\to\pi_i$ almost surely by
  [CKMA SYNOPSIS08](../lean-CKMA/SYNOPSIS08.md), item 50, and
  $\sqrt n\,(\hat p_{ij}-p_{ij})_{i,j}$ is asymptotically centered normal with
  $$\lim_n n\mathop{\mathrm{Cov}}(\hat p_{ij},\hat p_{i'j'})
  =\frac{\delta_{ii'}\bigl(\delta_{jj'}p_{ij}-p_{ij}p_{ij'}\bigr)}{\pi_i}.$$
  Thus different rows are asymptotically independent. Suppose
  $p_{ij}=p_{ij}(\theta)$ for $\theta$ in an open set
  $\Theta\subset\mathbb R^k$, that the set $D$ of pairs $(i,j)$ with
  $p_{ij}(\theta)>0$ does not depend on $\theta$, that each $p_{ij}$ has
  continuous partial derivatives of third order, and that the
  $|D|\times k$ matrix $(\partial p_{ij}/\partial\theta_u)_{(i,j)\in D}$ has
  rank $k$. With the information
  $$\mathcal I(\theta)=\sum_{i,j:\,p_{ij}>0}\pi_i\,
  \frac{\nabla p_{ij}(\theta)\nabla p_{ij}(\theta)^\top}{p_{ij}(\theta)},$$
  which is then nonsingular, with probability tending to one the likelihood
  equation has a root $\hat\theta$ with $\hat\theta\to_P\theta$, and every such
  sequence of roots satisfies
  $\sqrt n(\hat\theta-\theta)\Rightarrow N(0,\mathcal I(\theta)^{-1})$. For
  the simple hypothesis $P=P^0$, the statistics
  $\sum_{i,j}(n_{ij}-n_ip^0_{ij})^2/(n_ip^0_{ij})$ and
  $2\sum_{i,j}n_{ij}\log(\hat p_{ij}/p^0_{ij})$, summed over the positive
  entries of $P^0$, are asymptotically chi-squared with $d-m$ degrees of
  freedom, where $d$ is the number of positive entries of $P^0$.

### Spatial data, point patterns, and Gaussian processes

Let $X$ be a centered second-order process on a domain $\mathcal D$, with
known covariance $k$. Write $K$ for the covariance matrix of the observations
$X(s_1),\ldots,X(s_n)$ and $k_0$ for the vector of covariances between
$X(s_0)$ and these observations.

* **20. Simple kriging.** Suppose $K$ is nonsingular. The linear predictor
  $k_0^\top K^{-1}(X(s_1),\ldots,X(s_n))^\top$ minimizes the mean squared
  error among linear predictors of $X(s_0)$. The minimal mean squared error is
  $k(s_0,s_0)-k_0^\top K^{-1}k_0$. If $X$ is Gaussian, the predictor is the
  conditional expectation and the minimal error is the conditional variance.

* **21. Stein's prediction theorem.** Let $h_1,h_2,\ldots$ be random
  variables, linearly independent under covariance $k_0$, and let
  $\mathcal H$ be their closed linear span in $L^2$ under $k_0$. For
  $\psi\in\mathcal H$ and $i=0,1$, let $e_i(\psi,n)$ be the error of the best
  linear predictor of $\psi$ from $h_1,\ldots,h_n$ computed as if the
  covariance were $k_i$, and write $\mathbb E_i$ for expectation under the
  zero-mean Gaussian law with covariance $k_i$. Suppose these two Gaussian
  laws of $(h_1,h_2,\ldots)$ are equivalent. Then, with the suprema over
  $\psi\in\mathcal H$ with $\mathbb E_0e_0(\psi,n)^2>0$,
  $$\sup_\psi\Bigl|\frac{\mathbb E_0e_1(\psi,n)^2}{\mathbb E_0e_0(\psi,n)^2}
  -1\Bigr|\to0,\qquad
  \sup_\psi\Bigl|\frac{\mathbb E_1e_0(\psi,n)^2}{\mathbb E_0e_0(\psi,n)^2}
  -1\Bigr|\to0.$$
  The roles of $k_0$ and $k_1$ may be exchanged. With $k_0$ true, the first
  limit says that the kriging predictor computed from $k_1$ is uniformly
  asymptotically optimal, and the second, with the roles exchanged, that the
  mean squared error $\mathbb E_1e_1(\psi,n)^2$ it presumes is asymptotically
  correct. An example is $h_j=X(s_j)$ with sites $s_j$ dense in a bounded
  domain.

A Gaussian Markov random field on a finite graph has conditional independence
across non-edges if and only if the corresponding entries of its precision
matrix vanish. That characterization is SYNOPSIS105, item 26.

On a window $W$ of finite positive measure, a Poisson point process of
intensity function $\lambda$ has $N(W)\sim\mathop{\mathrm{Poisson}}(\int_W\lambda)$,
and conditionally on $N(W)=n$ the points are independent with density
proportional to $\lambda$. The existence and the Laplace functional are
CKMA SYNOPSIS06, item 53, and the Palm description of the Poisson case is
CKMA SYNOPSIS06, item 70.

* **22. Constant intensity.** For a homogeneous Poisson point process of
  intensity $\lambda$, the maximum likelihood estimator based on the
  restriction to $W$ is $N(W)/|W|$. It is unbiased and is the uniform minimum
  variance unbiased estimator of $\lambda$, with variance $\lambda/|W|$. For
  windows $W_k$ with $|W_k|\to\infty$,
  $\sqrt{|W_k|}\,\bigl(N(W_k)/|W_k|-\lambda\bigr)\Rightarrow N(0,\lambda)$.

* **23. Universal kriging.** Suppose the spatial mean is
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
  A constant mean gives ordinary kriging; a known mean gives item 20.

### Covariance models for random fields

A complex function $K$ on $\mathbb R^d$ is **positive definite** when
$\sum_{j,k}c_j\bar c_kK(x_j-x_k)\ge0$ for all finite families of points and
complex coefficients. A field on $\mathbb R$ is **mean-square differentiable**
when its difference quotients converge in $L^2$, and **$m$ times mean-square
differentiable** when this holds iteratively.

* **24. Bochner's theorem and the Matérn family.** A function $K$ on
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
  $|x|$.

A field $Z$ on $\mathbb R^d$ is **intrinsically stationary** when its
increments $Z(x+h)-Z(x)$ have mean zero and a variance depending only on $h$.
Its **semivariogram** is $\gamma(h)=\tfrac12\mathop{\mathrm{Var}}(Z(x+h)-Z(x))$.
A symmetric function $\gamma$ is **conditionally negative definite** when
$\sum_{j,k}c_jc_k\gamma(x_j-x_k)\le0$ whenever $\sum_jc_j=0$.

* **25. Valid semivariograms.** For an intrinsically stationary field and
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

### Likelihood and second-order structure of point patterns

* **26. Poisson likelihood.** Let $S\subset\mathbb R^d$ be bounded and let
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
  formula, [CKMA SYNOPSIS06](../lean-CKMA/SYNOPSIS06.md), item 54. Item 22 is
  the constant case. On all of $\mathbb R^d$, by contrast, homogeneous
  Poisson processes of different intensities are mutually singular.

For a point process with intensity function $\rho$ and second-order product
density $\rho^{(2)}$, the **pair correlation function** is
$g(\xi,\eta)=\rho^{(2)}(\xi,\eta)/(\rho(\xi)\rho(\eta))$. When $g(\xi,\eta)$
depends only on $\xi-\eta$, the **$K$-function** and **$L$-function** are
$$K(r)=\int_{|\xi|\le r}g(\xi)\,d\xi,\qquad L(r)=\bigl(K(r)/\omega_d\bigr)^{1/d},$$
where $\omega_d$ is the volume of the unit ball in $\mathbb R^d$.

* **27. Second-order summaries under complete spatial randomness.** For a
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
  which exceeds the Poisson value $\pi r^2$ for every $r>0$.

<a id="synopsis-106b"></a>

## 106B. Survival Analysis, Sequential Analysis, and Extreme Values

### Survival analysis and counting processes

Let $T$ be a failure time, let $C$ be a censoring time, and write
$\tilde T=\min(T,C)$ and $\delta=1_{\{T\le C\}}$. Assume independent censoring:
$T$ and $C$ are independent, and the observable data are independent copies of
$(\tilde T,\delta)$. Let $N(t)=1_{\{\tilde T\le t,\,\delta=1\}}$ and
$Y(t)=1_{\{\tilde T\ge t\}}$. On the event $\{Y=1\}$ the intensity of $N$ is
the failure hazard $\lambda$. The compensator of $N$ is
$\int_0^t Y(s)\lambda(s)\,ds$. Write $y(u)=\mathbb P(\tilde T\ge u)$, and
assume $y(\tau)>0$.

* **28. Nelson–Aalen estimator.** With $d_i$ failures and $n_i$ subjects at
  risk at an observed failure time $t_i$, the Nelson–Aalen estimator of the
  cumulative hazard $\Lambda(t)=\int_0^t\lambda$ is
  $\hat\Lambda(t)=\sum_{t_i\le t}d_i/n_i$. Suppose the failure distribution is
  continuous. From $n$ independent copies of $(\tilde T,\delta)$,
  $$\sqrt n\,(\hat\Lambda-\Lambda)$$
  converges weakly in $D[0,\tau]$ to a centered Gaussian martingale $W$
  with independent increments and variance function
  $\int_0^t d\Lambda(u)/y(u)$.

* **29. Kaplan–Meier estimator.** The product-limit estimator
  $$\hat S(t)=\prod_{t_i\le t}\Bigl(1-\frac{d_i}{n_i}\Bigr)$$
  satisfies, under the assumptions of item 28,
  $$\sqrt n\,(\hat S-S)\Rightarrow G=-S\,W$$
  weakly in $D[0,\tau]$, with $W$ as in item 28, so that
  $$\mathop{\mathrm{Var}}(G(t))
  =S(t)^2\int_0^t\frac{d\Lambda(u)}{y(u)}.$$
  Greenwood's estimator, in a sample of size $n$, is
  $$\widehat{\mathop{\mathrm{Var}}}(\hat S(t))
  =\hat S(t)^2\sum_{t_i\le t}\frac{d_i}{n_i(n_i-d_i)},$$
  and $n\,\widehat{\mathop{\mathrm{Var}}}(\hat S(t))\to_P\mathop{\mathrm{Var}}(G(t))$
  uniformly in $t\in[0,\tau]$.

In the **Cox model** the conditional hazard is
$\lambda(t\mid Z)=\lambda_0(t)\exp(\beta\cdot Z)$, with $\lambda_0$
unspecified. The partial likelihood is
$$L(\beta)=\prod_{\delta_i=1}
\frac{\exp(\beta\cdot Z_i)}{\sum_{j:\tilde T_j\ge\tilde T_i}\exp(\beta\cdot Z_j)}.$$
Write $e(\beta,t)$ for the weighted average of the covariates of subjects
still at risk at time $t$, with weights proportional to $\exp(\beta\cdot Z)$.

* **30. Cox partial likelihood.** Let $(T_i,C_i,Z_i)$, $i=1,\ldots,n$, be
  independent copies of $(T,C,Z)$, where $Z\in\mathbb R^p$ is a bounded
  covariate, $T$ has conditional hazard $\lambda(t\mid Z)$ with
  $\Lambda_0(\tau)<\infty$, and $T$ and $C$ are conditionally independent
  given $Z$. Suppose $P(\tilde T\ge\tau)>0$, let the partial likelihood be
  restricted to failures in $[0,\tau]$, and let
  $\bar e(u)=\mathbb E[Y(u)Ze^{\beta\cdot Z}]/\mathbb E[Y(u)e^{\beta\cdot Z}]$ at
  the true $\beta$. If the matrix
  $$\mathcal I=\mathbb E\int_0^\tau\bigl(Z-\bar e(u)\bigr)^{\otimes2}\,dN(u)$$
  is positive definite, then the maximizer $\hat\beta$ satisfies
  $\hat\beta\to_P\beta$ and $\sqrt n(\hat\beta-\beta)\Rightarrow N(0,\mathcal I^{-1})$.
  This matrix is the efficient information for $\beta$ in the multiplicative
  intensity model, so $\hat\beta$ attains the convolution bound of
  SYNOPSIS102, item 34. In the two-sample problem, with $Z$ the group
  indicator, the score test of $\beta=0$ is the log-rank test.

### Censoring likelihood and competing causes

* **31. Likelihood under independent right censoring.** Let $T,C$ be
  independent nonnegative times with continuous densities. For
  $\tilde T=\min(T,C)$ and $\delta=1_{\{T\le C\}}$, the observed density
  is
  $$[f_T(t)S_C(t)]^\delta[f_C(t)S_T(t)]^{1-\delta}.$$
  If the failure and censoring parameters are distinct, the contribution
  for failure inference is $f_T(t)^\delta S_T(t)^{1-\delta}$, or
  $\lambda_T(t)^\delta\exp(-\Lambda_T(t))$.
  The law of $(\tilde T,\delta)$ determines $S_T(t)$ for every $t$ with
  $S_C(t)>0$. If $S_C(t_0)=0$, any two failure laws that agree on
  $[0,t_0]$ give the same law of $(\tilde T,\delta)$.

* **32. Log-rank statistic.** At pooled failure times $t_j$, let $Y_{aj}$
  and $d_{aj}$ be the at-risk and failure counts in group $a=0,1$,
  and let $Y_j=Y_{0j}+Y_{1j}$, $d_j=d_{0j}+d_{1j}$. Under equal failure
  hazards and independent censoring within each group, the score statistic
  and its variance estimate are
  $$U=\sum_j\left(d_{1j}-\frac{Y_{1j}d_j}{Y_j}\right),\qquad
  \hat V=\sum_j\frac{Y_{1j}Y_{0j}d_j(Y_j-d_j)}{Y_j^2(Y_j-1)},$$
  omitting terms with $Y_j\le1$. Suppose group $a$ consists of $n_a$
  independent copies of $(\tilde T,\delta)$ as above, with a common
  continuous failure law in both groups and censoring laws that may differ
  between groups, that the sums run over failure times in $[0,\tau]$, that
  $n_a/(n_0+n_1)\to p_a\in(0,1)$, that $P(\tilde T\ge\tau)>0$ in each
  group, and that $P(T\le\tau)>0$. Then, as $n_0+n_1\to\infty$,
  $U/\sqrt{\hat V}\Rightarrow N(0,1)$. This is the binary-covariate score
  test of item 30.

* **33. Cumulative incidence in competing risks.** For a failure time $T$
  and observed cause $J\in\{1,\ldots,k\}$, let $\lambda_j$ be the
  cause-specific hazard, and assume each
  $\Lambda_j(t)=\int_0^t\lambda_j$ is finite. Then
  $$S(t)=\exp\left(-\sum_j\Lambda_j(t)\right),\qquad
  F_j(t)=P(T\le t,J=j)=\int_0^t S(u)\,d\Lambda_j(u).$$
  With independent right censoring, estimating each $\Lambda_j$ by its
  cause-specific Nelson–Aalen estimator and $S$ by the all-cause
  Kaplan–Meier estimator gives
  $\hat F_j(t)=\sum_{u\le t}\hat S(u-)\,dN_j(u)/Y(u)$.
  From $n$ independent copies, if $P(\tilde T\ge\tau)>0$, then
  $\sup_{t\le\tau}|\hat F_j(t)-F_j(t)|\to_P0$. Treating other causes as
  censoring, one minus the Kaplan–Meier estimator converges in probability to
  $1-\exp(-\Lambda_j(t))$ for $t\le\tau$, which is at least $F_j(t)$. For
  any such law of $(T,J)$ there are independent latent times
  $T_1,\ldots,T_k$ in $(0,\infty]$, with $T_j$ of cumulative hazard
  $\Lambda_j$, such that
  $(\min_jT_j,\mathop{\mathrm{arg\,min}}_jT_j)$ has the law of $(T,J)$;
  so the law of $(T,J)$ does not determine whether latent times are
  independent.

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

* **34. Rebolledo's martingale central limit theorem.** For each $n$ let
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
  $D[0,\tau]^k$. This is the continuous-time analogue of item 1, and items 28–30 are applications of it.

In the setting of item 30, write $s^{(0)}(\beta,u)=\mathbb E[Y(u)e^{\beta\cdot
Z}]$, and note that $\bar e(u)$ of item 30 is the limit in probability of
$e(\beta,u)$ at the true $\beta$. The **Breslow estimator** of the
cumulative baseline hazard $\Lambda_0(t)=\int_0^t\lambda_0$ is
$$\hat\Lambda_0(t)=\int_0^t
\frac{d\bar N(u)}{\sum_jY_j(u)\exp(\hat\beta\cdot Z_j)},$$
where $\bar N$ is the pooled counting process.

* **35. Breslow estimator.** Under the conditions of item 30, the process
  $\sqrt n\,(\hat\Lambda_0-\Lambda_0)$ converges weakly on $[0,\tau]$ to
  $$W(t)-q(t)^\top G,\qquad q(t)=\int_0^t\bar e(u)\,d\Lambda_0(u),$$
  where $W$ is a centered Gaussian martingale with variance function
  $\int_0^td\Lambda_0(u)/s^{(0)}(\beta,u)$, $G$ is the normal limit of
  $\sqrt n(\hat\beta-\beta)$ in item 30, and $W$ and $G$ are independent. The
  asymptotic variance at $t$ is therefore
  $\int_0^td\Lambda_0/s^{(0)}+q(t)^\top\mathcal I^{-1}q(t)$, with
  $\mathcal I$ the information matrix of item 30. Estimated survival
  curves $\exp(-\hat\Lambda_0(t)e^{\hat\beta\cdot z})$ for a fixed covariate
  value follow by the functional delta method of SYNOPSIS102, item 28.

In **Aalen's additive hazards model**, subject $i$ has intensity
$Y_i(t)\bigl(\beta_0(t)+\beta_1(t)Z_{i1}(t)+\cdots+\beta_p(t)Z_{ip}(t)\bigr)$ with
unspecified locally integrable regression functions $\beta_j$ and predictable
covariates. Let $\mathbf Y(t)$ be the $n\times(p+1)$ matrix with rows
$Y_i(t)(1,Z_{i1}(t),\ldots,Z_{ip}(t))$, let $J(t)$ indicate that $\mathbf Y(t)$
has full column rank, and set $B_j(t)=\int_0^t\beta_j$.

* **36. Aalen's additive hazards estimator.** The least-squares estimator
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
  Gaussian martingale, and
  $n\int_0^\cdot J(\mathbf Y^\top\mathbf Y)^{-1}\mathbf Y^\top
  \mathop{\mathrm{diag}}(dN)\,\mathbf Y(\mathbf Y^\top\mathbf Y)^{-1}$
  converges in probability, uniformly on $[0,t]$, to its covariance
  function.

### Sequential analysis, change detection, and anytime-valid inference

Let $f_0$ and $f_1$ be the densities of a single observation under two simple
hypotheses, and let $\Lambda_n=\prod_{i=1}^n f_1(X_i)/f_0(X_i)$. The sequential
probability ratio test continues sampling while $A<\Lambda_n<B$ and stops at
the first exit, rejecting $H_0$ if $\Lambda_n\ge B$ and accepting $H_0$ if
$\Lambda_n\le A$, where $0<A<1<B$.

* **37. Sequential probability ratio test.** Let the observations be
  independent with density $f_i$ under $\mathbb P_i$, $i=0,1$, and suppose
  $0<\mathbb E_i|\log(f_1/f_0)|<\infty$ and $\mathbb P_i(f_1\neq f_0)>0$ for
  $i=0,1$. Then the stopping time $N$ satisfies $\mathbb E_iN<\infty$ for
  $i=0,1$, and $\mathbb E_iN=\mathbb E_i\log\Lambda_N/\mathbb E_i\log(f_1/f_0)$
  by Wald's identity. Let $\alpha=\mathbb P_0(\text{reject }H_0)$ and
  $\beta=\mathbb P_1(\text{accept }H_0)$. Then
  $$B\le\frac{1-\beta}\alpha,\qquad A\ge\frac{\beta}{1-\alpha}.$$
  Among all tests, sequential or of fixed sample size, whose type I error
  is at most $\alpha$ and whose type II error is at most $\beta$, this
  sequential probability ratio test minimizes both $\mathbb E_0N$ and
  $\mathbb E_1N$ (Wald and Wolfowitz).

* **38. Ville's inequality and e-values.** Let $(M_n)_{n\ge0}$ be a
  nonnegative supermartingale with $M_0\le1$. For every $\alpha\in(0,1)$,
  $$\mathbb P\Bigl(\sup_{n\ge0}M_n\ge\frac1\alpha\Bigr)\le\alpha.$$
  An e-value for a null hypothesis is a nonnegative random variable whose
  expectation is at most $1$ under every law in the null. Let
  $E_1,E_2,\ldots$ be nonnegative and adapted to a filtration
  $(\mathcal F_n)$, with $\mathbb E[E_n\mid\mathcal F_{n-1}]\le1$ under every
  law in the null. Then $M_n=E_1\cdots E_n$, $M_0=1$, is a nonnegative
  supermartingale under every such law, so $M_\tau$ is an e-value for every
  almost surely finite stopping time $\tau$, and the test that rejects at
  the first $n$ with $M_n\ge1/\alpha$ rejects with probability at most
  $\alpha$ under every law in the null.

* **39. CUSUM and the Brownian bridge.** Let $X_1,X_2,\ldots$ be independent
  with a common distribution, mean $\mu_0$, and variance
  $\sigma^2\in(0,\infty)$, and let
  $S_k=\sum_{t=1}^k(X_t-\mu_0)$. Under a constant mean,
  $$\frac1{\sigma\sqrt n}\max_{1\le k\le n}\Bigl|S_k-\frac kn S_n\Bigr|
  \Rightarrow\sup_{t\in[0,1]}|B^0(t)|.$$

* **40. Inversion into confidence sequences.** For each parameter value
  $\theta$, let $M_t(\theta)$ be a nonnegative supermartingale under
  $P_\theta$ with $M_0(\theta)\le1$. Then
  $$C_t=\{\theta:M_t(\theta)<1/\alpha\}$$
  satisfies $P_\theta(\theta\in C_t\text{ for every }t)\ge1-\alpha$.
  Consequently $P_\theta(\theta\in C_\tau)\ge1-\alpha$ for every random time
  $\tau$ with values in $\{0,1,2,\ldots\}$, in particular for every almost
  surely finite stopping time. The bound is item 38 applied to
  $M_t(\theta)$.

### Wald's identity, random sample sizes, and fixed-width intervals

In the setting of item 37, write $Z_i=\log(f_1(X_i)/f_0(X_i))$ and
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
  exactly one real $h=h(\theta)\ne0$ with $\phi(h)=1$, and then
  $\mathbb E_\theta e^{hS_N}=1$ and
  $\mathbb E_\theta N=\mathbb E_\theta S_N/\mathbb E_\theta Z$. If in addition
  there is no overshoot, that is, $S_N\in\{\log A,\log B\}$ almost surely,
  then
  $$L(\theta)=\frac{B^{h}-1}{B^{h}-A^{h}},\qquad
  \mathbb E_\theta N=
  \frac{L(\theta)\log A+(1-L(\theta))\log B}{\mathbb E_\theta Z}.$$
  These right-hand sides are Wald's approximations in general. If $f_0$
  and $f_1$ are positive on the same set, then under $f_0$ one has $h=1$
  and under $f_1$ one has $h=-1$; with $A=\beta/(1-\alpha)$ and
  $B=(1-\beta)/\alpha$ the displayed formula then gives $L=1-\alpha$ and $L=\beta$ respectively.

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
  The Chow–Robbins rule
  $N=\inf\{n\ge n_0:n\ge a^2s_n^2/d^2\}$, with $n_0\ge2$ and $s_n^2$ the
  running sample variance, satisfies $N<\infty$ almost surely and, as
  $d\to0$, $N/C\to1$ almost surely, $\mathbb EN/C\to1$, and
  $P_{\mu,\sigma}(|\bar X_N-\mu|\le d)\to1-\alpha$. For independent
  identically distributed observations from any distribution with finite
  positive variance, the rule with $s_n^2$ replaced by $s_n^2+n^{-1}$ has the
  same properties (Chow and Robbins); item 42 supplies the coverage limit.

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
  $P(T\le\nu)\le\alpha$. For each $n$ and each sample, as $p\to0$,
  $p^{-1}\Pi_n/(1-\Pi_n)$ tends to the **Shiryaev–Roberts statistic**
  $$R_n=\sum_{k=1}^n\prod_{i=k}^nL_i,\qquad R_n=(1+R_{n-1})L_n,\quad R_0=0.$$
  Under $P_\infty$ the process $R_n-n$ is a zero-mean martingale, so
  $T_{\mathrm{SR}}(A)=\inf\{n:R_n\ge A\}$ has
  $\mathbb E_\infty T_{\mathrm{SR}}(A)\ge A$ by optional sampling. If
  $L_1$ has a continuous law under $P_\infty$ and $A_\gamma$ gives
  $\mathbb E_\infty T_{\mathrm{SR}}(A_\gamma)=\gamma>1$, then $T_{\mathrm{SR}}(A_\gamma)$
  minimizes the integral average delay
  $\sum_{k\ge0}\mathbb E_k(T-k)^+/\mathbb E_\infty T$ over
  $\mathcal C_\gamma$.

### Extreme-value statistics

Let $M_n=\max(X_1,\ldots,X_n)$ for independent copies of a random variable
with distribution function $F$, and write $x_F=\sup\{x:F(x)<1\}$.

* **46. Fisher–Tippett–Gnedenko theorem.** The nondegenerate distributional
  limits of $(M_n-b_n)/a_n$, with $a_n>0$, are exactly the laws
  $G_\gamma(ax+b)$ with $a>0$, $b,\gamma\in\mathbb R$, where the generalized
  extreme-value laws are
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

* **47. Excesses over high thresholds.** The distribution $F$ lies in the
  domain of attraction of $G_\gamma$ if and only if there is a positive scale
  $\sigma(u)$ such that
  $$\sup_y\Bigl|
  \mathbb P(X-u\le y\mid X>u)-H_{\gamma,\sigma(u)}(y)\Bigr|\to0$$
  as $u\uparrow x_F$, where the supremum runs over all $y\ge0$, including
  points at and beyond a finite excess endpoint, and
  $$H_{\gamma,\sigma}(y)
  =1-\Bigl(1+\frac{\gamma y}\sigma\Bigr)^{-1/\gamma}$$
  for $\gamma\neq0$, while $H_{0,\sigma}(y)=1-e^{-y/\sigma}$. The support is
  the set of $y>0$ with $1+\gamma y/\sigma>0$. The distribution function
  is zero for $y<0$ and, when $\gamma<0$, one for $y\ge-\sigma/\gamma$.

For a strictly stationary sequence, let $M_n$ be the sample maximum and let
$u_n$ satisfy $n(1-F(u_n))\to\tau\in(0,\infty)$.

Condition $D(u_n)$ holds when there are numbers $\alpha_{n,l}$, with
$\alpha_{n,l_n}\to0$ for some $l_n=o(n)$, such that
$$\Bigl|P\bigl(\max_{i\in I\cup J}X_i\le u_n\bigr)-
P\bigl(\max_{i\in I}X_i\le u_n\bigr)P\bigl(\max_{i\in J}X_i\le u_n\bigr)\Bigr|
\le\alpha_{n,l}$$
for all $I,J\subset\{1,\ldots,n\}$ with $j-i\ge l$ for all $i\in I$,
$j\in J$. Condition $D'(u_n)$ holds when
$\limsup_nn\sum_{j=2}^{\lfloor n/k\rfloor}P(X_1>u_n,X_j>u_n)\to0$ as
$k\to\infty$.

* **48. Extremal index.** The sequence has extremal index $\theta\in(0,1]$
  when, for every $\tau>0$, $\mathbb P(M_n\le u_n)\to e^{-\theta\tau}$ for
  every sequence $(u_n)$ with $n(1-F(u_n))\to\tau$. An independent sequence
  has extremal index $1$. More generally, if $D(u_n)$ and $D'(u_n)$ hold
  for every such sequence and every $\tau>0$, the extremal index is $1$
  (Leadbetter).

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

* **49. Hill estimator.** Suppose $1-F$ is regularly varying of index
  $-1/\gamma$ with $\gamma>0$, and suppose the second-order condition above
  holds. If $k\to\infty$, $k/n\to0$, and $\sqrt k\,A(n/k)\to\lambda\in\mathbb R$,
  then
  $$\sqrt k\,(H_{k,n}-\gamma)\Rightarrow N\Bigl(\frac{\lambda}{1-\rho},\gamma^2\Bigr).$$
  In particular the limit is $N(0,\gamma^2)$ when $\sqrt k\,A(n/k)\to0$.

### Exceedances and block maxima

* **50. Poisson approximation for exceedances.** For independent
  observations, $0\le\tau\le\infty$, and real $u_n$,
  $$P(M_n\le u_n)\to e^{-\tau}\quad\text{if and only if}\quad
  n\bigl(1-F(u_n)\bigr)\to\tau.$$
  For finite $\tau$ the number of exceedances of $u_n$ among
  $X_1,\ldots,X_n$ then converges in law to a Poisson law with mean $\tau$,
  by CKMA SYNOPSIS06, item 38. For $0<\tau<\infty$, levels $u_n$ with
  $n(1-F(u_n))\to\tau$ exist if and only if both
  $\lim_{x\uparrow x_F}F(x)=1$ and
  $(1-F(x))/(1-F(x-))\to1$ as $x\uparrow x_F$. Hence the Poisson and
  geometric laws, whose atoms do not become negligible in this ratio, are in
  no domain of attraction. Item 48 replaces $e^{-\tau}$ by $e^{-\theta\tau}$
  for dependent sequences.

The **return level** $z_p$ of a law $G$ is the level exceeded with probability
$p$, $G(z_p)=1-p$. For block maxima with the generalized extreme-value law of
location $\mu$, scale $\sigma>0$, and shape $\gamma$,
$$z_p=\mu-\frac\sigma\gamma\Bigl[1-\bigl(-\log(1-p)\bigr)^{-\gamma}\Bigr]
\quad(\gamma\ne0),\qquad z_p=\mu-\sigma\log\bigl(-\log(1-p)\bigr)\quad(\gamma=0).$$

* **51. Likelihood for block maxima.** Let $Z_1,\ldots,Z_m$ be independent
  with the generalized extreme-value law
  $G_\gamma((z-\mu)/\sigma)$, whose support depends on the parameters, and
  write $\vartheta=(\mu,\sigma,\gamma)$. If $\gamma>-1/2$, the Fisher
  information $\mathcal I(\vartheta)$ of one observation is finite and
  nonsingular, and as $m\to\infty$, with probability tending to one the
  likelihood equations have a root $\hat\vartheta_m$ with
  $\hat\vartheta_m\to_P\vartheta$ and
  $\sqrt m(\hat\vartheta_m-\vartheta)\Rightarrow N(0,\mathcal I(\vartheta)^{-1})$.
  For fixed $p\in(0,1)$, the delta method then gives
  $\sqrt m(z_p(\hat\vartheta_m)-z_p(\vartheta))\Rightarrow
  N(0,\nabla z_p^\top\mathcal I(\vartheta)^{-1}\nabla z_p)$.

## Reference guide

### Correspondence with the subdivisions

- **[106A](#synopsis-106a)**: Brockwell and Davis, Brillinger, Priestley, and
  Hannan and Deistler carry the Wold decomposition, autoregressive estimation,
  Bartlett's formula, and spectral estimation. Hall and Heyde carry the
  martingale central limit theorem. Durbin and Koopman carry the Kalman
  filter. Cappé, Moulines, and Rydén carry hidden Markov likelihoods.
  Giraitis, Koul, and Surgailis carry long memory. Kutoyants and Liptser and
  Shiryaev carry likelihood theory for diffusions. Lahiri carries the block
  bootstrap for series; Fan and Yao treat only the subsampling bootstrap,
  and Douc, Moulines, and Stoffer the parametric bootstrap. Brockwell and
  Davis also carry the Herglotz representation, the Durbin–Levinson recursion,
  Kolmogorov's formula, and the Whittle asymptotics; Douc, Moulines, and
  Stoffer carry GARCH stationarity; Basawa and Prakasa Rao carry likelihood
  inference for finite Markov chains. Stein carries kriging, covariance
  misspecification, spectral and Matérn models, and semivariograms. Møller and
  Waagepetersen, and Daley and Vere-Jones, carry point processes. Rue and Held
  carry Gaussian Markov random fields.
- **[106B](#synopsis-106b)**: Andersen, Borgan, Gill, and Keiding, Fleming and
  Harrington, Kalbfleisch and Prentice, and Aalen, Borgan, and Gjessing carry
  the Nelson–Aalen estimator, the Kaplan–Meier estimator, and the Cox partial
  likelihood. Andersen, Borgan, Gill, and Keiding carry Rebolledo's theorem,
  the Breslow estimator, and Aalen's additive model. Wald carries the
  sequential probability ratio test. Ghosh, Mukhopadhyay, and Sen, and
  Tartakovsky, Nikiforov, and Basseville carry sequential estimation and
  change detection: Anscombe's theorem and fixed-width intervals in the
  former, the optimality of CUSUM, Shiryaev, and Shiryaev–Roberts procedures
  in the latter. Csörgő and Horváth carry the bridge limit for the CUSUM.
  Leadbetter, Lindgren, and Rootzén, Embrechts, Klüppelberg, and Mikosch,
  Resnick, and de Haan and Ferreira carry domains of attraction, threshold
  excesses, the extremal index, and the Hill estimator. Coles is the applied
  companion and carries block-maximum likelihood and return levels.

### Source comparisons and local copies

Brockwell–Davis supplies the long-run variance and innovations
framework used in items 12 and 13. Kalbfleisch–Prentice, Section 1.5,
was read for the log-rank statistic and its hypergeometric variance,
and Chapter 8 for cumulative incidence, including formulas (8.5) and
(8.11). The distinction between a cause-specific hazard and a cumulative
incidence is essential when other causes compete. Independent censoring
identifies the failure distribution only over the observable time range.
Item 40 is the parameterwise inversion of Ville's inequality; item 23
combines generalized least squares with the kriging projection of item 20.
The negative-index tail ratio in item 46 uses the same limiting
variable in numerator and denominator.

Item 6 uses the Brockwell–Davis normalization in which the spectral density
integrates to $\gamma(0)$ over $[-\pi,\pi]$ and a white-noise periodogram has
exponential mean $f(\omega)$. Item 6 follows Brockwell and Davis,
Theorem 10.3.2 and the lag-window variance (10.4.11) under the conditions
of Theorem 10.4.1; a central limit theorem for the lag-window estimator
needs a bias condition and is not stated. Item 8 is the matrix-product form of the likelihood and the forward
recursion, as in Cappé, Moulines, and Rydén. Item 10 concerns a drift
linear in the parameter,
where the estimator is explicit; Kutoyants treats the general case. Item 11
is the moving-block bootstrap theorem for the mean in the strong-mixing form
of Lahiri, *Resampling Methods for Dependent Data* (2003), Theorem 3.2, in
dimension one, with the resample size $\ell b$ and the centering
$\mathbb E^*\bar X_n^*$ of his Section 3.2; Theorem 3.1 there gives the
corresponding consistency of the bootstrap variance. Item 37 records Wald's inequalities and
Wald's identity for the expected sample size; Wald's approximations, which
neglect overshoot, appear in item 41 as exact formulas under the hypothesis
of no overshoot. Item 21 is Stein (1999), Section 4.3, Theorem 8 (from
Stein (1990a), Theorem 3.1 and Corollary 3.1), stated for zero means: its
two displays are (37) and (35) there, and the exchanged forms are (38) and
(36). Item 21 uses equivalence of Gaussian measures in the form already numbered in the
analysis synopsis. Item 48 states Leadbetter's conditions as in Leadbetter,
Lindgren, and Rootzén, Section 3.4. Item 49 states the second-order condition and the bias term of de Haan and
Ferreira, Theorem 3.2.5.

The following source passages support the numbered statements. Brockwell and
Davis (1991): Theorem 4.3.1 (Herglotz), Theorem 4.4.2 (ARMA spectral
density), Proposition 5.2.1 (Durbin–Levinson), Theorem 5.8.1 (Kolmogorov's
formula, proved there for a continuous spectral density bounded away from
zero, with the general case referred to Hannan), Theorems 8.1.1–8.1.2, and
Theorems 10.8.1–10.8.2 with their parameter set, which give item 17 for
independent identically distributed innovations without Gaussianity.
Brockwell and Davis do not state the Fisher information. The limit in item 5
is Whittle (1953), *Ark. Mat.* 2, 423–434, Section 3, equations
(3.2)–(3.7): with the one-step prediction variance as parameter, the
information is asymptotically block diagonal, the variance block is
$n/(2\sigma^4)$, and the $\beta$ block is $n$ times
$(4\pi)^{-1}\int_{-\pi}^{\pi}\nabla_\beta\log g\,\nabla_\beta\log g^\top\,d\lambda$.
Whittle's derivation neglects end effects; Box, Jenkins, Reinsel, and Ljung,
Section 7.2.6, give the $\beta$ block in the time-domain form
$\sigma^{-2}\mathbb E[X^\top X]$ under the same approximation, and a rigorous
proof is attributed to Porat, *Digital Processing of Random Signals* (1994),
Theorem 5.3, which was not accessed.
Douc, Moulines, and Stoffer, Theorems 4.13 and 4.18 and Remark 4.16, for
item 18. Basawa and Prakasa Rao, Chapter 4, Section 2, for item 19.
Andersen, Borgan, Gill, and Keiding: Theorem II.5.1 and its
counting-process form (2.5.6)–(2.5.8) for item 34, Theorem VII.2.3 for
item 35, and Section VII.4 with Theorem VII.4.1 for item 36. Wald,
Appendix A.2.2–A.2.3, for the fundamental identity and the operating
characteristic of item 41, written here with $A<1<B$ as in item 37 (Wald
labels the upper threshold $A$). Ghosh, Mukhopadhyay, and Sen: Theorems
2.7.1–2.7.2 (Anscombe), Theorem 6.2.1 (Stein), and Theorem 8.2.1
(Chow–Robbins, stated there for normal data). The distribution-free form in
item 43 is Chow and Robbins (1965), *Ann. Math. Statist.* 36, 457–462, whose
rule with $s_n^2+n^{-1}$, the sample variance taken with divisor $n-1$, and
whose three limits for $0<\sigma^2<\infty$ are restated in Mukhopadhyay and
Datta (1996), *Ann. Inst. Statist. Math.* 48, 497–507, (1.1)–(1.2); the
original paper was not accessed. Tartakovsky, Nikiforov, and
Basseville: Theorems 8.2.1 and 8.2.3 and Lemma 8.2.1 for item 44,
Theorems 7.1.1–7.1.2, formula (7.6), and Theorem 7.6.1 for item 45. Stein
(1999): Sections 2.4 and 2.6 on mean-square differentiability, Section 2.5,
Theorem 1, Section 2.7 on the Matérn class,
Section 2.9 on intrinsic random functions and semivariograms (Matheron's
representation with $r=0$), and Section 2.10. Møller and Waagepetersen:
Proposition 3.8, Definitions 4.4 and 4.6 with (4.5)–(4.6),
Proposition 4.3, and Example 5.3 with (5.10). de Haan and Ferreira:
Theorems 1.2.1 and 3.2.5 for items 46 and 49. Leadbetter,
Lindgren, and Rootzén: Theorems 1.5.1 and 1.7.13 for item 50. Coles,
Sections 3.3.2–3.3.3, for item 51, where the regular range $\gamma>-1/2$ is
Smith's (1985) result as reported by Coles; the nonregular ranges are not
stated. The Dickey–Fuller limit in
terms of Brownian functionals is outside the selection: Brockwell and Davis (2016),
Section 6.3, gives only the test and its quantiles, and Fuller is not in
the local directory.

Siegmund, *Sequential Analysis*, Ramdas and Wang's survey of e-values, and
Chopin and Papaspiliopoulos, *An Introduction to Sequential Monte Carlo*, are
not in the local reference directory. Item 38 is Ville's inequality together
with the definition of a sequential e-value. Csörgő and Horváth is present as
a DjVu file and was not text-extracted; item 39 is the Brownian-bridge limit
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
- [Lahiri, *Resampling Methods for Dependent Data*](../lean-CKMA/References/Lahiri2003ResamplingMethodsDependentData-Springer.SSS.pdf).
- [Box, Jenkins, Reinsel, and Ljung, *Time Series Analysis*](../lean-CKMA/References/BoxJenkinsReinselLjung2015TimeSeriesAnalysisForecastingControl5thEd-WileySerProbStat.epub).
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
