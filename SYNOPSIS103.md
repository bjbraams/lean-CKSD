# Synopsis: Nonparametric and high-dimensional inference

Part of the [mathematical synopsis series](SYNOPSIS.md).
[Bibliographical scope and references](CKSD-bib.md#cks-103).

This synopsis follows Section 103. Subdivision 103A is rank methods,
smoothing, shape constraints, nonparametric minimax rates, and functional
data. Subdivision 103B is sparsity, minimax lower bounds, sparse recovery,
model selection, multiple testing, low-rank and graphical-model estimation,
and high-dimensional covariance and principal components. The two
subdivisions share the reduction of estimation to testing. Parametric
efficiency is [SYNOPSIS102](SYNOPSIS102.md), items 13, 14, 16, and 17, and semiparametric efficiency is [SYNOPSIS102](SYNOPSIS102.md), item 34. The
empirical-process limit and the Dvoretzky–Kiefer–Wolfowitz inequality are
[CKMA SYNOPSIS06](../lean-CKMA/SYNOPSIS06.md), item 59, and
[CKMA SYNOPSIS07](../lean-CKMA/SYNOPSIS07.md), item 39. The Sauer–Shelah
bound, uniform deviations for VC classes, covariance estimation, the
restricted isometry property, the Marchenko–Pastur law, and the Tracy–Widom
law of the Gaussian unitary ensemble are CKMA SYNOPSIS07, items 35, 37, 46,
48, 51, and 69. Bonferroni's method is [SYNOPSIS101](SYNOPSIS101.md), item 59. Learning-theoretic bounds
are [SYNOPSIS107](SYNOPSIS107.md), and nonparametric priors are
[SYNOPSIS104](SYNOPSIS104.md).

Numbered definitions and results have stable identifiers. Additions take the
next free number and are placed beside related material; numbers need not
increase in reading order. Proofs are outside the scope of this synopsis.

<a id="synopsis-103a"></a>

## 103A. Ranks, Smoothing, Shape Constraints, Minimax Estimation, and Functional Data

Throughout this subdivision, $X_1,\ldots,X_n$ are independent copies of a real
random variable with distribution function $F$ and, when a density exists,
density $f$. The empirical distribution function is $F_n$.

* **1. Kolmogorov–Smirnov statistic.** If $F$ is continuous, the law of
  $\sup_x|F_n(x)-F(x)|$ does not depend on $F$. By the empirical-process
  limit, as $n\to\infty$,
  $$\sqrt n\sup_x|F_n(x)-F(x)|\Rightarrow\sup_{t\in[0,1]}|B^0(t)|,$$
  where $B^0$ is a Brownian bridge, and for $x>0$
  $$P\bigl(\sup_t|B^0(t)|\le x\bigr)
  =1-2\sum_{k=1}^\infty(-1)^{k-1}e^{-2k^2x^2}.$$
  The Dvoretzky–Kiefer–Wolfowitz inequality, with Massart's constant, gives
  $P\bigl(\sqrt n\sup_x|F_n(x)-F(x)|>x\bigr)\le2e^{-2x^2}$ for every $n$ and
  every $x>0$.

* **2. Linear rank statistics.** Let $X_1,\ldots,X_N$ be independent with a
  common continuous distribution function, and let $R_i$ be the rank of
  $X_i$ in the pooled sample. Then the rank vector $(R_1,\ldots,R_N)$ is
  uniform on the $N!$ permutations, so the law of every function of the
  ranks does not depend on the common distribution. The asymptotic
  normality of a linear rank statistic $S_N=\sum_i c_{N,i}a_N(R_i)$ is
  item 14. In the two-sample shift problem with sample sizes $m,n$ and
  $m/(m+n)\to\lambda\in(0,1)$, the Wilcoxon rank-sum test is the locally
  most powerful rank test for the logistic shift (item 14), and its Pitman
  efficiency relative to the two-sample $t$ test, at a normal shift, equals
  $3/\pi$.

* **3. Hodges–Lehmann estimator.** For a distribution symmetric about
  $\theta$ with density $f$, let $\hat\theta_n$ be the median of the Walsh
  averages $(X_i+X_j)/2$ for $1\le i\le j\le n$. If $\int f^2<\infty$ and
  $f$ is continuous and positive at the center of symmetry of $X_1-X_2$, then
  $$\sqrt n\,(\hat\theta_n-\theta)
  \Rightarrow N\Bigl(0,\frac{1}{12\bigl(\int f(x)^2\,dx\bigr)^2}\Bigr).$$
  The asymptotic variance is the reciprocal of the efficacy of the Wilcoxon
  signed-rank test.

A **kernel density estimator** with bandwidth $h>0$ and kernel $K$ is
$$\hat f_h(x)=\frac1{nh}\sum_{i=1}^n K\bigl((x-X_i)/h\bigr).$$
Write $\mu_2(K)=\int u^2K(u)\,du$ and $R(K)=\int K(u)^2\,du$.

* **4. Kernel density asymptotics.** Let $K$ be a bounded symmetric
  probability density with finite $\mu_2(K)$ and $R(K)$. Let $f$ be twice
  continuously differentiable, with $f$ and $f''$ square-integrable. If
  $f''$ is bounded, $f(x)>0$, and $h\to0$, $nh\to\infty$, and $nh^5=O(1)$,
  then
  $$\sqrt{nh}\Bigl(\hat f_h(x)-f(x)-\tfrac12 h^2\mu_2(K)f''(x)\Bigr)
  \Rightarrow N\bigl(0,R(K)f(x)\bigr).$$
  If $h\to0$ and $nh\to\infty$, the mean integrated squared error satisfies
  $$\mathbb E\int(\hat f_h-f)^2
  =\tfrac14 h^4\mu_2(K)^2\int(f'')^2+\frac{R(K)}{nh}
  +o\Bigl(h^4+\frac1{nh}\Bigr).$$
  If $\int(f'')^2>0$, the leading term is minimized by
  $h_n^*=\bigl(R(K)/(\mu_2(K)^2\int(f'')^2\,n)\bigr)^{1/5}$, with minimum
  value $\tfrac54\bigl(\mu_2(K)^2\int(f'')^2\bigr)^{1/5}R(K)^{4/5}n^{-4/5}$.

* **5. Universal $L^1$ consistency.** Let $K$ be a bounded integrable kernel
  on $\mathbb R^d$ with $\int K=1$ and compact support. If $h\to0$ and
  $nh^d\to\infty$, then $\int|\hat f_h-f|\to0$ almost surely for every
  density $f$ on $\mathbb R^d$.

For regression, let $(X_i,Y_i)$ be independent copies of $(X,Y)$ with
$m(x)=\mathbb E[Y\mid X=x]$ and $\sigma^2(x)=\mathop{\mathrm{Var}}(Y\mid X=x)$.
The **Nadaraya–Watson** estimator weights $Y_i$ by
$K_h(X_i-x)/\sum_j K_h(X_j-x)$. The **local linear** estimator is the
intercept of the weighted least-squares fit of a straight line, with the same
kernel weights.

* **6. Interior asymptotics of kernel regression.** Let $X$ have density
  $f_X$ continuous and positive at an interior point $x$, let $m$ be twice
  continuously differentiable at $x$, and let $\sigma^2$ be continuous at $x$.
  Assume that $\mathbb E\bigl[|Y|^{2+\delta}\bigm|X=z\bigr]$ is bounded for
  $z$ in a neighbourhood of $x$, for some $\delta>0$, and let $K$ be a
  nonnegative bounded symmetric compactly supported probability kernel
  positive near zero. If $h\to0$, $nh\to\infty$, and
  $nh^5=O(1)$, the local linear estimator satisfies
  $$\sqrt{nh}\Bigl(\hat m_h(x)-m(x)-\tfrac12 h^2\mu_2(K)m''(x)\Bigr)
  \Rightarrow N\Bigl(0,\frac{R(K)\sigma^2(x)}{f_X(x)}\Bigr).$$
  If in addition $f_X$ and $m$ are continuously differentiable at $x$, the
  Nadaraya–Watson estimator satisfies the same limit with the bias
  $\tfrac12 h^2\mu_2(K)m''(x)$ replaced by
  $$\tfrac12 h^2\mu_2(K)\Bigl(m''(x)+2m'(x)\frac{f_X'(x)}{f_X(x)}\Bigr).$$
  Boundary points are treated in item 24.

* **7. Stone's theorem.** Assume $\mathbb E Y^2<\infty$. For the
  Nadaraya–Watson estimator $\hat m_n$ on $\mathbb R^d$, with $0/0$ read as
  $0$ and with a nonnegative bounded compactly supported kernel
  bounded below by a positive constant in a neighborhood of zero,
  $h\to0$ and $nh^d\to\infty$ imply
  $$\mathbb E\bigl[(\hat m_n(X)-m(X))^2\bigm|X_1,Y_1,\ldots,X_n,Y_n\bigr]
  \to0$$
  in probability, for every distribution of $(X,Y)$ on $\mathbb R^d\times\mathbb R$.
  The same $L^2$ consistency holds for $k$-nearest-neighbor
  regression when $k\to\infty$ and $k/n\to0$, for every distribution of
  $(X,Y)$ with $\mathbb EY^2<\infty$ in which $X$ has a density.

Let $\mathcal H$ be a reproducing-kernel Hilbert space of real functions on
a set $\mathcal X$, with kernel $K$. A loss $L(y,u)$ is evaluated only through
the predicted value $u$.

* **8. Representer theorem.** A minimizer of
  $$\frac1n\sum_{i=1}^n L(Y_i,f(X_i))+\lambda\|f\|_{\mathcal H}^2,
  \qquad\lambda>0,$$
  over $f\in\mathcal H$, has the form
  $f(\cdot)=\sum_{i=1}^n\alpha_i K(X_i,\cdot)$. In particular, for
  $n\ge2$ distinct design points $x_i\in[a,b]$, the smoothing spline
  criterion
  $$\sum_{i=1}^n(Y_i-f(x_i))^2+\lambda\int_a^b(f'')^2$$
  on the Sobolev space of functions on $[a,b]$ with square-integrable
  second derivative has a minimizer that is a natural cubic spline with
  knots at the design points $x_i$.

In the **Gaussian sequence model**, one observes
$Y_i=\theta_i+\varepsilon\xi_i$ for $i\ge1$, with $\xi_i$ independent standard
normal. The white-noise model $dY(t)=f(t)\,dt+\varepsilon\,dW(t)$ on $[0,1]$
is equivalent to a sequence model through an orthonormal basis.

* **9. Pinsker's theorem and the Sobolev rate.** Let $\Theta$ be the
  ellipsoid $\sum_{j\ge1}a_j^2\theta_j^2\le R$, with $a_j$ positive,
  nondecreasing, and $a_j\to\infty$. Let $R_N(\varepsilon)$ be the minimax
  mean squared error over $\Theta$ among all estimators and
  $R_L(\varepsilon)$ that among linear estimators
  $\hat\theta_j=c_jY_j$. Then $R_N(\varepsilon)/R_L(\varepsilon)\to1$ as
  $\varepsilon\to0$, and $R_L$ is attained by the shrinkage weights
  $c_j=(1-a_j/\mu)_+$ for a suitable $\mu=\mu(\varepsilon)>0$. If
  $a_j=j^\beta$ with $\beta>0$, then as $\varepsilon\to0$
  $$R_N(\varepsilon)\sim P_\beta R^{1/(2\beta+1)}\varepsilon^{4\beta/(2\beta+1)},
  \qquad
  P_\beta=(2\beta+1)^{1/(2\beta+1)}\Bigl(\frac\beta{\beta+1}\Bigr)^{2\beta/(2\beta+1)}.$$
  If only $c\,j^\beta\le a_j\le C\,j^\beta$ for constants $0<c\le C$, as for
  a periodic Sobolev ball in the white-noise model in the trigonometric
  basis, then $R_N(\varepsilon)$ is bounded above and below by positive multiples of
  $R^{1/(2\beta+1)}\varepsilon^{4\beta/(2\beta+1)}$ depending only on
  $\beta,c,C$, for all sufficiently small $\varepsilon$. With
  $\varepsilon=n^{-1/2}$ the squared-error rate is
  $n^{-2\beta/(2\beta+1)}$.

* **10. Soft-threshold oracle inequality.** In the finite sequence model
  $Y_i=\theta_i+\sigma\xi_i$, $i=1,\ldots,n$, let $\hat\theta$ be coordinatewise
  soft thresholding at $\lambda=\sigma\sqrt{2\log n}$. Then
  $$\mathbb E\|\hat\theta-\theta\|^2
  \le(2\log n+1)\Bigl(\sigma^2+\sum_{i=1}^n\min(\theta_i^2,\sigma^2)\Bigr).$$

* **11. Grenander estimator.** Let $f$ be a density vanishing on
  $(-\infty,0)$ and decreasing on $[0,\infty)$, with $f'(x_0)<0$ and $f$
  continuous at $x_0>0$. The maximum
  likelihood estimator $\hat f_n$ is the left slope of the least concave
  majorant of $F_n$. Then
  $$n^{1/3}\bigl(\hat f_n(x_0)-f(x_0)\bigr)
  \Rightarrow\bigl|4f(x_0)f'(x_0)\bigr|^{1/3}Z,$$
  where $Z=\mathop{\mathrm{argmax}}_{t\in\mathbb R}\bigl(W(t)-t^2\bigr)$ and
  $W$ is standard two-sided Brownian motion. The limit law is Chernoff's
  distribution up to the deterministic scale displayed above.

Let $K\subset\mathbb R^p$ be a closed polyhedral convex cone and let
$Y\sim N_p(\mu,I_p)$. Write $P_K$ for metric projection onto $K$.

* **12. Chi-bar-squared law.** The likelihood-ratio statistic for testing
  $\mu=0$ against $\mu\in K$ equals $\|P_KY\|^2$. Under the null its law is
  the mixture $\sum_{j=0}^p w_j\chi^2_j$, where $w_j$ is the probability that
  $P_KY$ lies in the relative interior of a $j$-dimensional face of $K$.
  Here $\chi^2_0$ is the point mass at $0$.

Testing $f=0$ in the white-noise model against a smoothness class at a
positive $L^2$ separation is a different problem from estimating $f$.

* **13. Nonparametric detection boundary.** In the white-noise model with
  $\varepsilon=n^{-1/2}$, let $\mathcal F$ be a Sobolev ball of smoothness
  $\beta>0$ and fixed radius, and for $\rho>0$ let
  $$\gamma_n(\rho)=\inf_\psi\Bigl(P_0(\psi=1)
  +\sup\bigl\{P_f(\psi=0):f\in\mathcal F,\ \|f\|_2\ge\rho\bigr\}\Bigr),$$
  the infimum over all tests $\psi$. Put $r_n=n^{-2\beta/(4\beta+1)}$. If
  $\rho_n/r_n\to0$ then $\gamma_n(\rho_n)\to1$, and if $\rho_n/r_n\to\infty$
  then $\gamma_n(\rho_n)\to0$. Since $2\beta/(4\beta+1)>\beta/(2\beta+1)$,
  $r_n$ is of smaller order than the $L^2$ estimation error rate
  $n^{-\beta/(2\beta+1)}$ of item 9.

### Rank scores, rank correlation, and goodness of fit

Let $U_{N(1)}<\cdots<U_{N(N)}$ be the order statistics of $N$ independent
uniform variables on $[0,1]$. A measurable, not almost everywhere constant
function $\varphi$ on $(0,1)$ with $\int_0^1\varphi^2<\infty$ is a
**score-generating function**; it generates the **exact scores**
$a_N(i)=\mathbb E\varphi(U_{N(i)})$ and the **approximate scores**
$\varphi(i/(N+1))$. Write $\bar c_N$ and $\bar a_N$ for the averages of the
regression constants and of the scores.

* **14. Score-generating functions and locally most powerful rank tests.**
  Let $X_1,\ldots,X_N$ be independent with a common continuous distribution
  function $F$, let $R_i$ be their ranks, and let
  $T_N=\sum_ic_{N,i}a_N(R_i)$ with exact scores. Then
  $\mathbb ET_N=N\bar c_N\bar a_N$,
  $$\mathop{\mathrm{Var}}T_N=\frac1{N-1}\sum_{i=1}^N(c_{N,i}-\bar c_N)^2
  \sum_{i=1}^N\bigl(a_N(i)-\bar a_N\bigr)^2,$$
  and $T_N$ is asymptotically equivalent, in the sense that the variance of
  the difference is negligible relative to $\mathop{\mathrm{Var}}T_N$, to
  $$N\bar c_N\bar a_N+\sum_{i=1}^N(c_{N,i}-\bar c_N)\,\varphi(F(X_i)).$$
  The standardized statistic is therefore asymptotically normal whenever
  $\max_i(c_{N,i}-\bar c_N)^2/\sum_i(c_{N,i}-\bar c_N)^2\to0$. The same
  holds for approximate scores if $\varphi$ is continuous almost everywhere
  and $N^{-1}\sum_i\varphi^2(i/(N+1))\to\int_0^1\varphi^2$. If $X_i$ has
  density $f(x-\theta c_{N,i})$, where $f$ is absolutely continuous with
  finite Fisher information for location, the locally most powerful rank
  test of $\theta=0$ against $\theta>0$ (the rank test that, for some
  $\epsilon>0$, is most powerful among rank tests of the same size for
  every $\theta\in(0,\epsilon)$) rejects for large $T_N$ with
  exact scores generated by
  $$\varphi_f(u)=-\frac{f'}{f}\bigl(F^{-1}(u)\bigr).$$
  For the logistic density this gives the Wilcoxon scores $i$; for the
  normal density it gives the normal scores
  $\mathbb E\Phi^{-1}(U_{N(i)})$, of which
  $\Phi^{-1}(i/(N+1))$ are the van der Waerden approximations. For the
  scale family $e^{-\theta}f(e^{-\theta}x)$ the generating function is
  $-1-F^{-1}(u)\,(f'/f)(F^{-1}(u))$; for the standard exponential density
  this is $-1-\log(1-u)$, which generates the log-rank (Savage) scores of
  SYNOPSIS106, item 32.

* **15. Asymptotic optimality and efficiencies of rank tests.** Let
  $X_1,\ldots,X_m$ have density $f(x-\mu)$ and $Y_1,\ldots,Y_n$ density
  $f(x-\nu)$, all independent, with $f$ of finite Fisher information
  $I_f$, $N=m+n$, and $m/N\to\lambda\in(0,1)$. Fix $\mu_0$ and
  $0<\alpha<1$. Let $\phi_N$ be any tests, possibly using $f$, with
  $\limsup_N\mathbb E_{\mu,\nu}\phi_N\le\alpha$ whenever
  $\mu=\nu=\mu_0+g/\sqrt N$, for every $g\in\mathbb R$. Then at
  $\mu=\mu_0+g/\sqrt N$, $\nu=\mu_0+(g+h)/\sqrt N$ with $h>0$,
  $$\limsup_N\mathbb E_{\mu,\nu}\phi_N
  \le1-\Phi\bigl(z_\alpha-h\sqrt{\lambda(1-\lambda)I_f}\bigr),$$
  and the two-sample rank test of asymptotic level $\alpha$ that rejects
  for large values of the statistic with scores generated by $\varphi_f$
  of item 14 attains this bound as a limit. Thus the Wilcoxon test attains
  it for the logistic shift and the normal-scores test for the normal
  shift. For a
  symmetric $f$ of finite Fisher information and observations with density
  $f(x-\theta)$, the signed-rank statistic
  $\sum_i\mathop{\mathrm{sign}}(X_i)\,a_n(R_i^+)$, with $R_i^+$ the rank of
  $|X_i|$ and exact scores generated by
  $-(f'/f)\bigl((F^+)^{-1}(u)\bigr)$, $F^+=2F-1$ on $[0,\infty)$, gives a
  test of $\theta=0$ of asymptotic level $\alpha$ whose power at
  $\theta=h/\sqrt n$ tends to $1-\Phi(z_\alpha-h\sqrt{I_f})$, the corresponding bound for
  tests of asymptotic level $\alpha$ at $\theta=0$; replacing $f$ by
  $\sigma^{-1}f(x/\sigma)$ multiplies these scores by $\sigma^{-1}$ and
  leaves the test unchanged. The Pitman efficiencies of the sign and
  Wilcoxon tests relative to the $t$ test, including the Hodges–Lehmann
  bound $108/125$, are SYNOPSIS102, item 22. The efficiency of the
  normal-scores test relative to the $t$ test is at least $1$ for every
  $f$ of finite variance, with equality at the normal law
  (Chernoff–Savage). The general theory of Pitman efficiency is
  SYNOPSIS102, item 21.

For independent copies of a pair $(X,Y)$ with continuous marginal laws,
**Kendall's tau** is $\tau=2P\bigl((X_2-X_1)(Y_2-Y_1)>0\bigr)-1$, estimated by
$$\hat\tau_n=\binom n2^{-1}\sum_{i<j}
\mathop{\mathrm{sign}}\bigl((X_j-X_i)(Y_j-Y_i)\bigr).$$
**Spearman's rho** $r_s$ is the ordinary sample correlation of the two rank
vectors, $r_s=1-6\sum_i(R_i-S_i)^2/\bigl(n(n^2-1)\bigr)$, where $R_i$ is
the rank of $X_i$ among $X_1,\ldots,X_n$ and $S_i$ that of $Y_i$ among
$Y_1,\ldots,Y_n$.

* **16. Rank tests of independence.** The statistic $\hat\tau_n$ is a
  $U$-statistic of order $2$ with bounded kernel. By SYNOPSIS102, item 8,
  $\sqrt n(\hat\tau_n-\tau)\Rightarrow N(0,4\zeta_1)$, where $\zeta_1$ is
  the variance of the conditional expectation of the kernel given one pair.
  Under independence the rank vectors are independent and uniform on the
  permutations, so the laws of $\hat\tau_n$ and $r_s$ are distribution-free.
  Then
  $$\mathbb E\hat\tau_n=0,\qquad
  \mathop{\mathrm{Var}}\hat\tau_n=\frac{2(2n+5)}{9n(n-1)},\qquad
  \sqrt n\,\hat\tau_n\Rightarrow N(0,4/9),$$
  and
  $$\mathbb Er_s=0,\qquad\mathop{\mathrm{Var}}r_s=\frac1{n-1},\qquad
  \sqrt n\,r_s\Rightarrow N(0,1).$$
  The two-sided test that rejects when
  $\tfrac32\sqrt n|\hat\tau_n|>z_{\alpha/2}$ has asymptotic level $\alpha$ under independence and power tending to
  one at every fixed law with $\tau\ne0$; there are dependent laws with
  $\tau=0$. The same holds for $r_s$ with $\tau$ replaced by the population
  rank correlation $12\,\mathbb E[F_X(X)F_Y(Y)]-3$, where $F_X,F_Y$ are the
  marginal distribution functions.

* **17. Cramér–von Mises and two-sample Kolmogorov–Smirnov limits.** If $F$
  is continuous, the Cramér–von Mises statistic
  $W_n^2=n\int(F_n-F)^2\,dF$ is distribution-free and
  $$W_n^2\Rightarrow\int_0^1B^0(t)^2\,dt
  \stackrel{d}{=}\sum_{j=1}^\infty\frac{Z_j^2}{j^2\pi^2},$$
  with $Z_j$ independent standard normal; the numbers $(j\pi)^{-2}$ are the
  eigenvalues of the Brownian-bridge covariance $s\wedge t-st$, and the
  limit has mean $1/6$. For independent samples of sizes $m$ and $n$ with
  empirical distribution functions $F_m$ and $G_n$, under a common continuous
  law the statistic $D_{m,n}=\sup_x|F_m(x)-G_n(x)|$ is distribution-free and,
  as $\min(m,n)\to\infty$,
  $$\sqrt{\frac{mn}{m+n}}\,D_{m,n}\Rightarrow\sup_{t\in[0,1]}|B^0(t)|,$$
  with the Kolmogorov law of item 1. If the two laws differ, the normalized
  statistic tends to infinity in probability, so the test is consistent
  against every alternative. Let $\{F_\theta:\theta\in\Theta\}$,
  $\Theta\subset\mathbb R^k$ open, be a family of distribution functions with
  $\sup_x|F_{\theta+u}(x)-F_\theta(x)-u^\top\dot F_\theta(x)|=o(|u|)$ as
  $u\to0$, and let
  $\sqrt n(\hat\theta_n-\theta)=n^{-1/2}\sum_i\psi_\theta(X_i)+o_P(1)$ under
  $F_\theta$, with $\mathbb E\psi_\theta(X)=0$ and
  $\mathbb E|\psi_\theta(X)|^2<\infty$. Then $\sqrt n(F_n-F_{\hat\theta_n})$
  converges in law in $\ell^\infty(\mathbb R)$ to a centered Gaussian
  process $G$ with covariance
  $$F_\theta(x\wedge y)-F_\theta(x)F_\theta(y)
  -\dot F_\theta(x)^\top\mathbb E\bigl[\psi_\theta(X)1_{\{X\le y\}}\bigr]
  -\dot F_\theta(y)^\top\mathbb E\bigl[\psi_\theta(X)1_{\{X\le x\}}\bigr]
  +\dot F_\theta(x)^\top\mathbb E\bigl[\psi_\theta\psi_\theta^\top\bigr]
  \dot F_\theta(y),$$
  and $\sqrt n\sup_x|F_n(x)-F_{\hat\theta_n}(x)|\Rightarrow\sup_x|G(x)|$.

### Exact ranks, smoothing bias, and shape constraints

* **18. Sign test.** For independent continuous observations with median
  $\theta_0$, $\sum_i1_{\{X_i>\theta_0\}}\sim\mathop{\mathrm{Bin}}(n,1/2)$.
  Hence the test that rejects when this count is at least $k$ has size
  $P(\mathop{\mathrm{Bin}}(n,1/2)\ge k)$ under every such law, with no
  symmetry assumption. Inversion is the quantile interval in SYNOPSIS101,
  item 22.

* **19. Wilcoxon sampling laws.** Under a continuous distribution symmetric
  about zero, the signs are independent fair signs and independent of the
  absolute values. Thus the positive signed-rank sum has the law
  $\sum_{j=1}^n jB_j$ for independent Bernoulli$(1/2)$ variables, with
  mean $n(n+1)/4$ and variance $n(n+1)(2n+1)/24$.
  For independent samples of sizes $m,n$ from a common continuous law,
  $U=\sum_{i,j}1_{\{X_i<Y_j\}}$ has mean $mn/2$ and variance
  $mn(m+n+1)/12$. Both centered, variance-normalized statistics tend to
  $N(0,1)$, in the second case when $m/(m+n)\to\lambda\in(0,1)$.

* **20. Kruskal–Wallis test.** For $k$ independent samples from a common
  continuous law, let $R_j$ be the sum of pooled ranks in group $j$, of
  size $n_j$, and put $N=\sum_jn_j$. For fixed $k$ and
  $n_j/N\to\lambda_j>0$,
  $$\frac{12}{N(N+1)}\sum_{j=1}^k\frac{R_j^2}{n_j}-3(N+1)
  \Rightarrow\chi^2_{k-1}.$$
  Its finite-sample permutation law is distribution-free.

* **21. Isotonic least squares.** For observations $y_i$ at ordered design
  points and weights $w_i>0$, the minimizer of
  $\sum_iw_i(y_i-\theta_i)^2$ over $\theta_1\le\cdots\le\theta_n$ is unique
  and satisfies
  $$\hat\theta_i=\max_{a\le i}\min_{b\ge i}
  \frac{\sum_{j=a}^bw_jy_j}{\sum_{j=a}^bw_j}.$$
  It is the vector of successive slopes of the greatest convex minorant
  of the cumulative-sum diagram
  $(\sum_{j\le i}w_j,\sum_{j\le i}w_jy_j)$, including $(0,0)$.

* **22. Hölder regression rates.** Let $Y_i=f(i/n)+\xi_i$,
  $i=1,\ldots,n$, with $\xi_i$ independent $N(0,\sigma^2)$, $\sigma>0$. For
  $\beta>0$ and $L>0$, let $\ell$ be the largest integer strictly smaller
  than $\beta$, and let $\Sigma(\beta,L)$ be the Hölder class of functions
  $f$ on $[0,1]$ that are $\ell$ times differentiable with
  $|f^{(\ell)}(x)-f^{(\ell)}(x')|\le L|x-x'|^{\beta-\ell}$. Write
  $R_n^{(2)}=\inf_{\hat f}\sup_{f\in\Sigma(\beta,L)}\mathbb E\|\hat f-f\|_2^2$
  and $R_n^{(\infty)}$ for the same with $\|\cdot\|_\infty^2$, the infima
  over all estimators. Then
  $$0<\liminf_n n^{2\beta/(2\beta+1)}R_n^{(2)}
  \le\limsup_n n^{2\beta/(2\beta+1)}R_n^{(2)}<\infty,$$
  and the same holds for $R_n^{(\infty)}$ with $n^{2\beta/(2\beta+1)}$
  replaced by $(n/\log n)^{2\beta/(2\beta+1)}$. In the $L^2$ case the upper
  bound is attained by the local polynomial estimator of degree $\ell$
  with bandwidth $h=c\,n^{-1/(2\beta+1)}$, $c>0$, and a kernel $K$ with
  $K_{\min}1_{\{|u|\le\Delta\}}\le K(u)\le K_{\max}1_{\{|u|\le1\}}$ for
  constants $K_{\min},\Delta>0$ and $K_{\max}<\infty$. The lower bounds
  follow from the reductions of items 39 and 40.

Bias matters for confidence statements even at a mean-squared-error optimal
bandwidth. For the second-order smoothers of items 4 and 6, $nh^5\to0$
makes the leading $h^2$ bias negligible relative to $(nh)^{-1/2}$.
At $h\asymp n^{-1/5}$ it has the same order as the standard error, so
pointwise intervals require bias correction or undersmoothing.

### Bandwidth selection, linear smoothers, and density rates

For the kernel density estimator, let $\hat f_{h,-i}$ be the estimator
computed from the observations other than $X_i$, with divisor $(n-1)h$. The
**least-squares cross-validation criterion** is
$$\mathop{\mathrm{CV}}(h)=\int\hat f_h^2-\frac2n\sum_{i=1}^n\hat f_{h,-i}(X_i).$$
A regression estimator is a **linear smoother** if its fitted values are
$\hat m=LY$ for a matrix $L$ depending only on the design and the smoothing
parameter.

* **23. Cross-validation.** If $\int f^2<\infty$ and
  $\iint|K((x-z)/h)|f(z)f(x)\,dz\,dx<\infty$, then for every $h>0$
  $$\mathbb E\mathop{\mathrm{CV}}(h)
  =\mathbb E\int(\hat f_h-f)^2-\int f^2.$$
  Stone's version of the criterion replaces the divisor $n-1$ by $n$:
  $$M_1(h)=\int\hat f_h^2-\frac2{n^2h}\sum_{i\ne j}
  K\Bigl(\frac{X_i-X_j}h\Bigr)
  =\int\hat f_h^2-\frac{2(n-1)}{n^2}\sum_{i=1}^n\hat f_{h,-i}(X_i).$$
  If $f$ is bounded, $K$ is a symmetric, compactly supported,
  Hölder-continuous probability density, and $\hat h$ minimizes $M_1$
  over $h>0$, then (Stone)
  $$\frac{\int(\hat f_{\hat h}-f)^2}{\inf_{h>0}\int(\hat f_h-f)^2}\to1
  \quad\hbox{almost surely}.$$
  For a linear smoother whose matrix $L$ has row sums $1$ and $L_{ii}<1$,
  put $\hat m_{(-i)}(x_i)=\sum_{j\ne i}L_{ij}Y_j/(1-L_{ii})$, the fit with
  the weight of the $i$th observation set to zero and the remaining
  weights in row $i$ renormalized. Then
  $$\frac1n\sum_{i=1}^n\bigl(Y_i-\hat m_{(-i)}(x_i)\bigr)^2
  =\frac1n\sum_{i=1}^n\left(\frac{Y_i-\hat m(x_i)}{1-L_{ii}}\right)^2.$$
  For Nadaraya–Watson, local polynomial, and smoothing-spline smoothers,
  $\hat m_{(-i)}(x_i)$ equals the fit at $x_i$ computed from the data
  without the $i$th observation.

Let $\hat\beta(x_0)$ be the coefficient vector of the kernel-weighted
least-squares fit of a polynomial of degree $p$ in $X_i-x_0$, and estimate
$m^{(\nu)}(x_0)$, $0\le\nu\le p$, by $\hat m_\nu(x_0)=\nu!\,\hat\beta_\nu$. With
$\mu_j=\int u^jK(u)\,du$ and $S=(\mu_{j+l})_{0\le j,l\le p}$, the
**equivalent kernel** is
$$K_\nu^*(t)=e_{\nu+1}^\top S^{-1}(1,t,\ldots,t^p)^\top K(t),$$
which satisfies $\int t^qK_\nu^*(t)\,dt=\delta_{\nu q}$ for $0\le q\le p$.

* **24. Local polynomial regression.** Let $f_X(x_0)>0$, let $f_X$,
  $m^{(p+1)}$, and $\sigma^2$ be continuous near $x_0$, let $K$ be a bounded
  symmetric compactly supported probability density, and let $h\to0$ and
  $nh\to\infty$. If $p-\nu$ is odd, then, conditionally on the design,
  $$\mathop{\mathrm{Bias}}\hat m_\nu(x_0)
  =\frac{\nu!}{(p+1)!}\Bigl(\int t^{p+1}K_\nu^*(t)\,dt\Bigr)
  m^{(p+1)}(x_0)\,h^{p+1-\nu}+o_P(h^{p+1-\nu}),$$
  $$\mathop{\mathrm{Var}}\hat m_\nu(x_0)
  =\frac{\nu!^2\int K_\nu^{*2}\;\sigma^2(x_0)}{f_X(x_0)\,nh^{1+2\nu}}
  +o_P\bigl((nh^{1+2\nu})^{-1}\bigr).$$
  If $p-\nu$ is even, the term of order $h^{p+1-\nu}$ vanishes by symmetry.
  If also $f_X'$ and $m^{(p+2)}$ are continuous near $x_0$ and
  $nh^3\to\infty$, the bias is $O_P(h^{p+2-\nu})$, with the same variance
  expansion. For $p-\nu$ even, $\int K_{\nu,p}^{*2}=\int K_{\nu,p+1}^{*2}$,
  where $K_{\nu,p}^*$ is the equivalent kernel for degree $p$, so the
  asymptotic variance is unchanged when the degree is raised from $p$ to
  $p+1$. Let the design density be supported on $[0,\infty)$, let $f_X$,
  $m^{(p+1)}$, and $\sigma^2$ be continuous on $[0,\eta)$ for some
  $\eta>0$, with $f_X(0)>0$, and let $x_0=ch$ for a fixed $c\ge0$. Then,
  for every $p\ge\nu$, the bias is
  $O_P(h^{p+1-\nu})$ and the variance is $O_P\bigl((nh^{1+2\nu})^{-1}\bigr)$,
  with $S$ replaced by the truncated moment matrix
  $\bigl(\int_{-c}^\infty u^{j+l}K\bigr)$ in the equivalent kernel. Item 6
  is the case $p=1$, $\nu=0$, and the Nadaraya–Watson estimator is
  $p=\nu=0$.

For design points $a<t_1<\cdots<t_n<b$, let $Q$ and $R$ be the
$n\times(n-2)$ and $(n-2)\times(n-2)$ band matrices of the
**value–second-derivative representation** of natural cubic splines with
knots $t_i$. For such a spline $g$, with
$\mathbf g=(g(t_1),\ldots,g(t_n))^\top$, the penalty is
$\int(g'')^2=\mathbf g^\top QR^{-1}Q^\top\mathbf g$.

* **25. Smoothing splines as linear smoothers.** Let $n\ge3$ and $\alpha>0$.
  The unique minimizer of
  $$\sum_{i=1}^n\bigl(Y_i-g(t_i)\bigr)^2+\alpha\int_a^b g''(t)^2\,dt$$
  over functions with absolutely continuous first derivative and
  square-integrable second derivative is the natural cubic spline with
  values $(I+\alpha QR^{-1}Q^\top)^{-1}Y$ at the knots. It is a linear
  smoother with hat matrix $A(\alpha)=(I+\alpha QR^{-1}Q^\top)^{-1}$, so
  item 23 gives
  $$\mathop{\mathrm{CV}}(\alpha)
  =\frac1n\sum_{i=1}^n\left(\frac{Y_i-\hat g(t_i)}{1-A_{ii}(\alpha)}\right)^2.$$

Away from the ends of the design, Silverman's equivalent-kernel
approximation describes the weights of this smoother by the kernel
$\kappa(u)=\tfrac12e^{-|u|/\sqrt2}\sin\bigl(|u|/\sqrt2+\pi/4\bigr)$, whose
Fourier transform is $1/(1+\omega^4)$, with local bandwidth
$(\alpha/(nf(t)))^{1/4}$ at a design point $t$ of local design density
$f(t)$; it is not stated here as a theorem.

A **kernel of order** $\ell\ge1$ is a function $K$ with $\int K=1$ and
$\int u^jK(u)\,du=0$ for $1\le j\le\ell$. For $\beta>0$, let $\ell$ be the
largest integer strictly smaller than $\beta$. The **Hölder density class**
$\mathcal P(\beta,L)$ is the set of probability densities on $\mathbb R$ that
are $\ell$ times differentiable with
$|f^{(\ell)}(x)-f^{(\ell)}(x')|\le L|x-x'|^{\beta-\ell}$.

* **26. Minimax rates of density estimation.** Let $K$ be a kernel of order
  $\ell$ with $\int K^2<\infty$ and $\int|u|^\beta|K(u)|\,du<\infty$, and let
  $h=c\,n^{-1/(2\beta+1)}$ for fixed $c>0$. Then
  $$\sup_{x_0\in\mathbb R}\ \sup_{f\in\mathcal P(\beta,L)}
  \mathbb E\bigl(\hat f_h(x_0)-f(x_0)\bigr)^2\le Cn^{-2\beta/(2\beta+1)}$$
  for all $n\ge1$, with $C$ depending only on $\beta,L,K,c$. Conversely,
  there is $c'>0$ depending only on $\beta,L$ such that, for every $x_0$,
  $\liminf_n n^{2\beta/(2\beta+1)}\inf_{T_n}\sup_{f\in\mathcal P(\beta,L)}
  \mathbb E(T_n(x_0)-f(x_0))^2\ge c'$, the infimum over all estimators
  $T_n$; the same lower bound holds for
  $\mathbb E\int(T_n-f)^2$. For an integer $m\ge1$, let $\mathcal F_{m,M}$
  be the class of densities with $m$ continuous derivatives and
  $\int(f^{(m)})^2\le M$. Kernels of order $m-1$ with
  $\int|y|^m|K(y)|\,dy<\infty$ and bandwidth $n^{-1/(2m+1)}$ give
  $$\sup_{f\in\mathcal F_{m,M}}\mathbb E\int(\hat f_h-f)^2
  \le C_{m,M}n^{-2m/(2m+1)},$$
  with $C_{m,M}$ depending only on $m,M,K$. Assouad's lemma, applied to
  $2^{r_n}$ local perturbations with $r_n$ of exact order $n^{1/(2m+1)}$,
  gives a lower bound $D_{m,M}n^{-2m/(2m+1)}$, with $D_{m,M}>0$
  depending only on $m,M$, for every estimator and all sufficiently large
  $n$. A kernel of order at least $2$ takes negative values, since
  $\int u^2K(u)\,du=0$.

### Risk bounds under shape constraints

* **27. Risk of isotonic regression.** Let $Y_i=\theta_i^*+\varepsilon_i$ for
  $i=1,\ldots,n$, with $\theta_1^*\le\cdots\le\theta_n^*$ and independent
  errors of mean zero and variance one. Let $\hat\theta$ be the
  isotonic least-squares estimator of item 21 with unit weights. There is a
  universal constant $C$ such that
  $$\frac1n\mathbb E\|\hat\theta-\theta^*\|^2
  \le C\left\{\Bigl(\frac{\theta_n^*-\theta_1^*}{n}\Bigr)^{2/3}
  +\frac{\log(en)}n\right\}.$$
  In particular the worst-case risk over nondecreasing sequences with
  $\|\theta^*\|_\infty\le1$ is at most $C'n^{-2/3}$ with $C'$ universal,
  and for standard normal errors no estimator has worst-case risk over
  this class below $c\,n^{-2/3}$, for a universal $c>0$. For constant
  $\theta^*$ the bound is $C\log(en)/n$.

Let $\mathcal F_d$ be the class of upper semicontinuous log-concave
densities on $\mathbb R^d$. The squared Hellinger distance is
$H^2(f,g)=\int(\sqrt f-\sqrt g)^2$.

* **28. Log-concave maximum likelihood.** Let $P$ be a probability measure on
  $\mathbb R^d$ with finite first moment that assigns probability less than
  one to every hyperplane. Then $\int\log f\,dP$ has a unique maximizer
  $f^*\in\mathcal F_d$, the log-concave projection of $P$. The set where
  $f^*>0$ contains the interior of the convex support of $P$ and is
  contained in that convex support. If
  $X_1,\ldots,X_n$ are points of $\mathbb R^d$ with $n\ge d+1$ and
  $d$-dimensional convex hull $C_n$, this gives a unique log-concave maximum
  likelihood estimator $\hat f_n$, which is supported on $C_n$. Its
  logarithm is a tent function: for suitable heights $y_i$, the smallest
  concave function with value at least $y_i$ at $X_i$ for every $i$,
  which is piecewise affine on $C_n$. For samples
  from $f_0\in\mathcal F_d$ and $n\ge d+1$,
  $$\sup_{f_0\in\mathcal F_d}\mathbb E H^2(\hat f_n,f_0)\le C_d\cdot
  \begin{cases}n^{-4/5},&d=1,\\ n^{-2/(d+1)}\log n,&d\ge2,\end{cases}$$
  with $C_d$ depending only on $d$, and there is $c_d>0$, depending only on
  $d$, such that every estimator $\tilde f_n$ satisfies
  $\sup_{f_0\in\mathcal F_d}\mathbb E H^2(\tilde f_n,f_0)\ge c_d\,n^{-4/5}$ for
  $d=1$ and $\ge c_d\,n^{-2/(d+1)}$ for $d\ge2$.

### Functional data analysis

Let $X$ be a random element of a separable Hilbert space $H$ with
$\mathbb E\|X\|^2<\infty$, mean $\mu$, and covariance operator
$C=\mathbb E[(X-\mu)\otimes(X-\mu)]$. Then $C$ is compact, self-adjoint,
nonnegative, and trace-class. Its eigenvalues and orthonormal eigenfunctions
are $(\lambda_j,\varphi_j)$.

* **29. Karhunen–Loève expansion and the Hilbertian central limit theorem.**
  For each positive eigenvalue, set
  $\xi_j=\langle X-\mu,\varphi_j\rangle/\sqrt{\lambda_j}$.
  These variables are uncorrelated with mean $0$ and variance $1$, and
  $$X=\mu+\sum_{j\ge1}\sqrt{\lambda_j}\,\xi_j\varphi_j,$$
  where only positive eigenvalues are included, with convergence in $L^2$
  and almost surely in $H$. For independent copies,
  $\sqrt n\,(\bar X_n-\mu)$ converges in law in $H$ to the centered Gaussian
  random element with covariance operator $C$.

* **30. Principal components of the empirical covariance.** Let $\hat C_n$ be
  the empirical covariance and let $\hat\lambda_j$ and $\hat\varphi_j$ be its
  eigenvalues and eigenfunctions. If $\lambda_j$ is simple and positive and
  $\mathbb E\|X\|^4<\infty$, then
  $$\sqrt n\,(\hat\lambda_j-\lambda_j)
  \Rightarrow N\bigl(0,\mathop{\mathrm{Var}}(\langle X-\mu,\varphi_j\rangle^2)\bigr).$$
  For a Gaussian $X$ the asymptotic variance equals $2\lambda_j^2$. The
  eigenvalues being ordered decreasingly, the empirical eigenfunction,
  multiplied by a sign so that $\langle\hat\varphi_j,\varphi_j\rangle\ge0$,
  satisfies $\|\hat\varphi_j-\varphi_j\|=O_P(n^{-1/2})$.
  Its first-order expansion is
  $$\hat\varphi_j-\varphi_j
  =\sum_{k\ne j}\frac{\langle(\hat C_n-C)\varphi_j,\varphi_k\rangle}
  {\lambda_j-\lambda_k}\varphi_k+o_P(n^{-1/2}),$$
  with the zero eigenspace included when present.

* **31. Optimality of functional principal components.** If the eigenvalues
  of $C$ are ordered decreasingly, then among all orthogonal projections
  $P_V$ onto $k$-dimensional subspaces of $H$,
  $$\inf_{\dim V=k}\mathbb E\|X-\mu-P_V(X-\mu)\|^2
  =\sum_{j>k}\lambda_j.$$
  The first $k$ eigenfunctions span a minimizing subspace. If
  $\lambda_k>\lambda_{k+1}$, that subspace is unique.

### Functional linear regression

Let $X$ be a centered random element of $L^2[0,1]$ with continuous
covariance kernel, covariance eigenvalues $\lambda_1\ge\lambda_2\ge\cdots$, and
tail sums $V_k=\sum_{j>k}\lambda_j$. In the **functional linear model**
$Y_i=\langle\beta,X_i\rangle+\varepsilon_i$, the $X_i$ are independent copies
of $X$, the errors are independent of them with mean zero and variance
$\sigma^2$, and $\beta$ lies in the Sobolev space $W_q[0,1]$ with
$\|g\|_{W_q}^2=\|g\|^2+\|g^{(q)}\|^2$. The **penalized least-squares
estimator** $\hat\beta_\eta$ minimizes
$$\frac1n\sum_{i=1}^n\bigl(Y_i-\langle g,X_i\rangle\bigr)^2
+\eta\|g\|_{W_q}^2,\qquad g\in W_q[0,1].$$

* **32. Prediction rates in functional linear regression.** Assume
  $V_k=O(k^{-\alpha})$ for some $\alpha>0$. Assume also a fourth-moment
  condition on the principal-component scores $Z_j=\langle X,\varphi_j\rangle$:
  $\mathop{\mathrm{Var}}(Z_jZ_k)\le c\,\lambda_j\lambda_k$ for all $j,k$ and
  a constant $c$. With
  $\eta=n^{-(2q+\alpha+1)/(2q+\alpha+2)}$, let $\mathbb E_{\varepsilon,X}$
  denote expectation over the errors and over an independent new copy $X$,
  given $X_1,\ldots,X_n$. Then
  $$\mathbb E_{\varepsilon,X}\bigl(\langle X,\hat\beta_\eta\rangle
  -\langle X,\beta\rangle\bigr)^2
  =O_P\bigl(n^{-(2q+\alpha+1)/(2q+\alpha+2)}+n^{-(\alpha+1)/2}\bigr).$$
  For $\alpha\ge1$, the first term dominates. Let $\alpha\ge1$ and let
  $\Theta$ be the class of models, specified by $\beta$ and the laws of $X$
  and $\varepsilon$, with $\|\beta\|_{W_q}\le1$ and $V_k\le k^{-\alpha}$
  for all $k$. Then for some $C>0$
  $$\liminf_{n\to\infty}\,n^{(2q+\alpha+1)/(2q+\alpha+2)}
  \inf_{\tilde\beta}\sup_\Theta
  \mathbb E\bigl(\langle X,\tilde\beta\rangle-\langle X,\beta\rangle\bigr)^2
  \ge C,$$
  the infimum over all estimators $\tilde\beta$ with values in $L^2[0,1]$.
  For Brownian-motion covariates, $\lambda_j=4/((2j-1)\pi)^2$,
  $\alpha=1$, and the rate is $n^{-(2q+2)/(2q+3)}$.

<a id="synopsis-103b"></a>

## 103B. High-Dimensional and Large-Scale Inference

In the Gaussian sequence model, one observes $Y=\theta+\sigma\xi$ in
$\mathbb R^p$, with $\xi$ standard normal.

* **33. Sparse minimax rate.** There are universal constants $0<c\le C$
  such that, for $1\le s\le p/2$, the minimax mean squared error
  $\inf_{\hat\theta}\sup\mathbb E\|\hat\theta-\theta\|^2$ over the class of
  vectors with at most $s$ nonzero coordinates lies between
  $c\,\sigma^2 s\log(p/s)$ and $C\sigma^2 s\log(p/s)$. When $s$ is known,
  soft thresholding at $\sigma\sqrt{2\log(p/s)}$ has worst-case risk over
  this class at most $C\sigma^2 s\log(p/s)$. The universal threshold
  $\sigma\sqrt{2\log p}$ gives, by item 10, risk at most
  $(2\log p+1)(s+1)\sigma^2$; if also $s\le p^a$ for a fixed $a<1$, this is
  within a factor depending only on $a$ of the minimax risk, for
  $p\ge3$.

Let $Y=X\beta+\varepsilon$ with $X$ an $n\times p$ design and with
$\varepsilon\in\mathbb R^n$. The **lasso** is any minimizer
$$\hat\beta\in\mathop{\mathrm{argmin}}_{\beta\in\mathbb R^p}
\Bigl(\frac1{2n}\|Y-X\beta\|_2^2+\lambda\|\beta\|_1\Bigr).$$
For an index set $S$ and a stretching factor $L>0$, the **compatibility
constant** is
$$\kappa^2(S,L)=\inf\Bigl\{
\frac{|S|\,\|X\delta\|_2^2}{n\|\delta_S\|_1^2}:
\delta\neq0,\;\|\delta_{S^c}\|_1\le L\|\delta_S\|_1\Bigr\}.$$

* **34. Lasso under compatibility.** Let $S$ be nonempty and $\lambda>0$.
  Suppose $\beta$ is supported on $S$ and
  $$\lambda\ge\frac2n\|X^\top\varepsilon\|_\infty.$$
  If $\kappa(S,3)>0$, then every lasso solution satisfies
  $$\frac1n\|X(\hat\beta-\beta)\|_2^2
  \le\frac{9\lambda^2|S|}{4\kappa^2(S,3)}$$
  and
  $$\|\hat\beta-\beta\|_1\le\frac{6\lambda|S|}{\kappa^2(S,3)}.$$
  The error $\hat\beta-\beta$ lies in the cone
  $\|\delta_{S^c}\|_1\le3\|\delta_S\|_1$. If the design satisfies the
  **restricted eigenvalue condition**
  $n^{-1}\|X\delta\|_2^2\ge\kappa\|\delta\|_2^2$ on that cone, with
  $\kappa>0$, then
  $$\|\hat\beta-\beta\|_2\le\frac{3\sqrt{|S|}\,\lambda}\kappa,$$
  and $\kappa^2(S,3)\ge\kappa$, since $\|\delta_S\|_1^2\le|S|\,\|\delta\|_2^2$.
  For a design with independent centered unit-variance sub-Gaussian
  entries, there are constants $C,c,\kappa_0>0$ depending only on the
  sub-Gaussian parameter such that, if $n\ge C|S|\log(ep/|S|)$, the
  restricted eigenvalue condition holds with $\kappa=\kappa_0$ with
  probability at least $1-2e^{-cn}$; this follows from the restricted
  isometry property of CKMA SYNOPSIS07, item 48. If the columns satisfy
  $\|X_{\cdot j}\|_2^2/n\le1$ and the errors are independent
  $N(0,\sigma^2)$, then for $t>0$ the choice
  $\lambda=2\sigma\sqrt{2(\log p+t)/n}$ meets the noise condition with
  probability at least $1-2e^{-t}$.

In the **Gaussian regression model** one observes $Y=f+\sigma\xi$ in
$\mathbb R^n$, with $f\in\mathbb R^n$ unknown and $\xi$ standard normal.
Let $(S_m)$ be a countable collection of linear subspaces of $\mathbb R^n$,
of dimensions $d_m$, and let $\hat f_m$ be the orthogonal projection
of $Y$ onto $S_m$. Write $\|\cdot\|_n$ for the norm
$\|v\|_n^2=n^{-1}\|v\|_2^2$.

* **35. Penalized model selection.** In the Gaussian regression model, let
  $(\pi_m)$ be positive weights with $\sum_m\pi_m\le1$. There is a
  universal constant $\kappa_0$ such that the following holds for every
  $\kappa>\kappa_0$. Take
  $$\mathop{\mathrm{pen}}(m)\ge\kappa\frac{\sigma^2}n\bigl(d_m+\log(1/\pi_m)\bigr).$$
  The penalized selector $\hat m$ minimizing
  $\|Y-\hat f_m\|_n^2+\mathop{\mathrm{pen}}(m)$ obeys
  $$\mathbb E\|\hat f_{\hat m}-f\|_n^2
  \le C(\kappa)\Bigl(\inf_m\Bigl(
  \inf_{g\in S_m}\|g-f\|_n^2+\mathop{\mathrm{pen}}(m)\Bigr)
  +\frac{\sigma^2}n\Bigr),$$
  where the constant $C(\kappa)$ depends only on $\kappa$.

* **36. AIC and BIC.** In the Gaussian regression model with known
  $\sigma^2$, let $\mathcal M$ be a model given by a linear subspace $S$ of
  dimension $k$, with maximized log-likelihood $\ell_n(\hat\theta)$
  attained at $\hat f=P_SY$. Let $Y'$ be an independent copy of $Y$ and
  $\ell_n'$ its log-likelihood. Then, whether or not $f\in S$,
  $$\mathbb E\bigl[\ell_n(\hat\theta)-\ell_n'(\hat\theta)\bigr]=k,$$
  and Akaike's criterion $-2\ell_n(\hat\theta)+2k$ corrects
  the maximized log-likelihood by this optimism. Fix $J$ and integers
  $k_1<\cdots<k_J$; for each $n$ let $S_1\subset\cdots\subset S_J$ be
  subspaces of $\mathbb R^n$ of dimensions $k_1,\ldots,k_J$. Let $j_0<J$ be
  fixed, let $f\in S_{j_0}$ for every $n$, and assume that, if $j_0>1$,
  $\|f-P_{S_{j_0-1}}f\|_2^2/\log n\to\infty$. Then the probability that
  the Akaike selector returns some $j>j_0$ has $\liminf$ at least
  $P\bigl(\chi^2_{d}>2d\bigr)>0$, $d=k_{j_0+1}-k_{j_0}$, while the
  selector minimizing the Bayes information criterion of SYNOPSIS104,
  item 5, $-2\ell_n(\hat\theta)+k\log n$, returns $j_0$ with probability
  tending to one.

Let $p_{(1)}\le\cdots\le p_{(m)}$ be ordered $p$-values for $m$ hypotheses,
of which $m_0$ are true nulls, each with a valid $p$-value, and let $V$ and $R$ be the numbers of false
and of all rejections.

* **37. Benjamini–Hochberg procedure.** Fix $\alpha\in(0,1)$ and let
  $k=\max\{i:p_{(i)}\le i\alpha/m\}$, with $k=0$ when the set is empty. Reject
  the hypotheses attached to $p_{(1)},\ldots,p_{(k)}$. If the null $p$-values
  are independent of each other and of the non-null $p$-values, or if the
  vector $p$ of $p$-values is positively regression dependent on the subset
  of null coordinates (for every set $D\subset[0,1]^m$ such that $x\in D$
  and $x\le y$ coordinatewise imply $y\in D$, and every true null $i$,
  $t\mapsto P(p\in D\mid p_i=t)$ is nondecreasing),
  then the false-discovery rate satisfies
  $$\mathbb E\Bigl[\frac{V}{\max(R,1)}\Bigr]\le\alpha\frac{m_0}m\le\alpha.$$

Let $X$ be an $n\times p$ matrix with independent standard normal entries, and
let $\ell_{\max}$ be the largest eigenvalue of the sample covariance
$n^{-1}X^\top X$. Write $y$ for a limit of $p/n$ in $(0,\infty)$.

* **38. Tracy–Widom law and spiked covariance.** As $n,p\to\infty$ with
  $p/n\to y$,
  $$\frac{\ell_{\max}-\mu_{n,p}}{\sigma_{n,p}}\Rightarrow F_1,$$
  where $F_1$ is the Tracy–Widom law of the Gaussian orthogonal ensemble,
  $$\mu_{n,p}=\frac{\bigl(\sqrt{n-1}+\sqrt p\bigr)^2}n,$$
  and
  $$\sigma_{n,p}
  =\frac{\bigl(\sqrt{n-1}+\sqrt p\bigr)
  \bigl((n-1)^{-1/2}+p^{-1/2}\bigr)^{1/3}}n.$$
  The empirical distribution of the eigenvalues converges weakly almost
  surely to the Marchenko–Pastur law of ratio $y$, whose absolutely
  continuous part is supported on $[(1-\sqrt y)^2,(1+\sqrt y)^2]$, by CKMA
  SYNOPSIS07, item 51. The edge law $F_2$ of the Gaussian unitary ensemble
  is CKMA SYNOPSIS07, item 69. In Johnstone's spiked model, the rows of $X$
  are independent $N(0,\Sigma)$ and $\Sigma$ has one eigenvalue $\alpha$
  and the remaining eigenvalues equal to $1$. As $p/n\to y$, the largest
  eigenvalue $\ell_{\max}$ of $n^{-1}X^\top X$ converges almost surely to
  $(1+\sqrt y)^2$ when $1<\alpha\le1+\sqrt y$, and to
  $\alpha+y\alpha/(\alpha-1)$ when $\alpha>1+\sqrt y$.

### Lower bounds, regularization, and multiplicity

* **39. Le Cam's two-point method.** If two parameters are at metric
  distance at least $2s$, then every estimator satisfies
  $$\max_{j=0,1}P_j(d(\hat\theta,\theta_j)\ge s)
  \ge\tfrac12(1-\|P_0-P_1\|_{\mathrm{TV}}).$$
  For any nonnegative increasing loss $\ell$, this gives a minimax risk
  lower bound $\ell(s)(1-\|P_0-P_1\|_{\mathrm{TV}})/2$.
  The probabilities here are the full observation laws. For product laws
  $P_j=Q_j^{\otimes n}$, $D(P_0\|P_1)=nD(Q_0\|Q_1)$, and
  $\|P_0-P_1\|_{\mathrm{TV}}\le\sqrt{D(P_0\|P_1)/2}$ by Pinsker's
  inequality.

* **40. Fano's method.** Let $\theta_1,\ldots,\theta_M$ be $2s$-separated,
  $M\ge2$, with observation laws $P_j$. For a uniform index $J$ and
  data $X\mid J=j\sim P_j$, every estimator satisfies
  $$\sup_jP_j(d(\hat\theta,\theta_j)\ge s)
  \ge1-\frac{I(J;X)+\log2}{\log M}.$$
  With $\bar P=M^{-1}\sum_jP_j$,
  $$I(J;X)=\frac1M\sum_jD(P_j\|\bar P)
  \le\frac1M\sum_jD(P_j\|Q)$$
  for any reference law $Q$ for which the right side is finite.
  With the packings of item 45, this gives the lower bounds in items 33
  and 22.

* **41. Lasso without a restricted eigenvalue.** Under the noise event
  of item 34, the basic inequality gives
  $$\frac1n\|X(\hat\beta-\beta)\|^2\le3\lambda\|\beta\|_1.$$
  This prediction bound holds for every $\beta$, without sparsity or
  compatibility assumptions.

* **42. Orthogonal designs and soft thresholding.** If
  $X^\top X/n=I_p$, the lasso solution is
  $$\hat\beta_j=\mathop{\mathrm{sign}}(z_j)(|z_j|-\lambda)_+,
  \qquad z=X^\top Y/n.$$
  The ridge estimator $(X^\top X+\lambda I)^{-1}X^\top Y$ of SYNOPSIS105,
  item 12, equals $nz/(n+\lambda)$.

* **43. Debiased linear estimation.** Let $Y=X\beta+\varepsilon$ with
  $\varepsilon\sim N(0,\sigma^2I_n)$ independent of the design $X$, let
  $\hat\beta$ be any estimator, let the $p\times p$ matrix $\hat\Theta$ be
  a function of $X$ only, and define
  $$\tilde\beta=\hat\beta+
  \hat\Theta X^\top(Y-X\hat\beta)/n.$$
  Then the exact decomposition is
  $$\sqrt n(\tilde\beta-\beta)
  =\hat\Theta X^\top\varepsilon/\sqrt n
  +\sqrt n(I-\hat\Theta\hat\Sigma)(\hat\beta-\beta),
  \qquad\hat\Sigma=X^\top X/n.$$
  If $\|\hat\Theta\hat\Sigma-I\|_{\max}
  \|\hat\beta-\beta\|_1=o_P(n^{-1/2})$, the second term tends to zero in
  probability in $\|\cdot\|_\infty$. Conditionally on $X$, the first term
  is exactly $N(0,\sigma^2\hat\Theta\hat\Sigma\hat\Theta^\top)$. Write
  $v_j=(\hat\Theta\hat\Sigma\hat\Theta^\top)_{jj}$. If in addition
  $\hat\sigma\to\sigma$ in probability and $P(v_j\ge c)\to1$ for some
  $c>0$, then
  $$P\Bigl(|\tilde\beta_j-\beta_j|\le z_{\alpha/2}\,\hat\sigma
  \sqrt{v_j/n}\Bigr)\to1-\alpha.$$

* **44. False-discovery control under arbitrary dependence.** Let
  $H_m=\sum_{j=1}^m1/j$. Replacing the Benjamini–Hochberg thresholds in
  item 37 by $i\alpha/(mH_m)$ controls the false-discovery rate at most
  $\alpha m_0/m$ for any joint distribution of valid null $p$-values.
  This is the Benjamini–Yekutieli correction. Family-wise error control
  under arbitrary dependence is SYNOPSIS101, items 67 and 68.

### Packings and hypercube lower bounds

Write $\rho(\omega,\omega')=\sum_{j=1}^m1_{\{\omega_j\ne\omega'_j\}}$ for the
**Hamming distance** on the hypercube $\Omega=\{0,1\}^m$.

* **45. Varshamov–Gilbert bound.** If $m\ge8$, there are points
  $\omega^{(0)},\ldots,\omega^{(M)}$ of $\{0,1\}^m$ with
  $\omega^{(0)}=(0,\ldots,0)$,
  $$\rho(\omega^{(j)},\omega^{(k)})\ge\frac m8
  \quad(0\le j<k\le M),\qquad M\ge2^{m/8}.$$
  Thus the hypercube contains exponentially many points at pairwise
  distance proportional to $m$. Indexing parameters by such points
  supplies the large separated families required in Fano's method,
  item 40.

* **46. Assouad's lemma.** Let $(P_\omega)_{\omega\in\Omega}$ be $2^m$
  probability laws for the observation, indexed by $\Omega=\{0,1\}^m$.
  For every estimator $\hat\omega$ with values in $\Omega$,
  $$\max_{\omega\in\Omega}E_\omega\,\rho(\hat\omega,\omega)
  \ge\frac m2\min_{\rho(\omega,\omega')=1}\;\inf_\psi
  \bigl(P_\omega(\psi=1)+P_{\omega'}(\psi=0)\bigr),$$
  where $\psi$ ranges over tests with values in $\{0,1\}$. If
  $\|P_\omega-P_{\omega'}\|_{\mathrm{TV}}\le\alpha<1$ whenever
  $\rho(\omega,\omega')=1$, the right side is at least $m(1-\alpha)/2$; if
  instead each such pair has $D(P_\omega\|P_{\omega'})\le\alpha<\infty$,
  it is at least
  $$\frac m2\max\Bigl(\tfrac12e^{-\alpha},\,1-\sqrt{\alpha/2}\Bigr).$$
  For parameters $\theta_\omega$ in a metric space with
  $d(\theta_\omega,\theta_{\omega'})^2\ge c\,\rho(\omega,\omega')$, every
  estimator $\hat\theta$ obeys
  $\max_\omega E_\omega d(\hat\theta,\theta_\omega)^2\ge(c/4)\max_\omega
  E_\omega\rho(\hat\omega,\omega)$, where $\hat\omega$ is a nearest index to
  $\hat\theta$. Unlike Fano's method, the lower bound is assembled from $m$
  two-point problems of the kind in item 39.

Let $Y=X\beta+\varepsilon$ with $\varepsilon\sim N(0,\sigma^2I_n)$ and a fixed
$n\times p$ design. For an integer $D_{\max}\le p/5$ let
$\underline c_X$ and $\overline c_X$ be the infimum and supremum of
$\|X\beta\|_2/\|\beta\|_2$ over nonzero $\beta$ with at most $2D_{\max}$
nonzero coordinates, and let
$V_D(X)=\{X\beta:\beta\text{ has exactly }D\text{ nonzero coordinates}\}$.

* **47. Minimax risk of sparse regression.** For $1\le D\le D_{\max}$,
  $$\inf_{\hat f}\sup_{f\in V_D(X)}E_f\|\hat f-f\|_2^2
  \ge\frac e{4(2e+1)^2}\Bigl(\frac{\underline c_X}{\overline c_X}\Bigr)^2
  D\log\Bigl(\frac p{5D}\Bigr)\sigma^2,$$
  the infimum running over all estimators. Conversely, let $S_m$ be the
  span of the columns of $X$ indexed by $m\subset\{1,\ldots,p\}$, with
  weights $\pi_m=2^{-|m|-1}\binom p{|m|}^{-1}$. Item 35 with these
  subspaces, a fixed $\kappa>\kappa_0$, and the penalty equal to its lower
  bound gives an estimator with
  $\sup_{f\in V_D(X)}E_f\|\hat f-f\|_2^2\le C\sigma^2D\log(ep/D)$ for
  $1\le D\le p$, with $C$ depending only on $\kappa$. If $D\le p/25$, the
  two bounds differ by a factor depending only on
  $\underline c_X/\overline c_X$.

### Exact and stable sparse recovery

For $S\subset\{1,\ldots,p\}$ and $L>0$ write
$\mathcal C_L(S)=\{\delta:\|\delta_{S^c}\|_1\le L\|\delta_S\|_1\}$. An
$n\times p$ matrix $X$ has the **restricted nullspace property** with respect
to $S$ if its kernel meets $\mathcal C_1(S)$ only at $0$. **Basis pursuit**
is the program of minimizing $\|b\|_1$ subject to $Xb=y$. The
**restricted isometry constant** $\delta_k(A)$ of a matrix $A$ is the
smallest $\delta\ge0$ with
$(1-\delta)\|v\|_2^2\le\|Av\|_2^2\le(1+\delta)\|v\|_2^2$ for every $v$ with
at most $k$ nonzero coordinates.

* **48. Restricted nullspace and exact recovery.** The following are
  equivalent: for every $\beta$ supported in $S$, basis pursuit with
  $y=X\beta$ has the unique solution $\beta$; and $X$ has the restricted
  nullspace property with respect to $S$. If
  $\delta_{2s}(n^{-1/2}X)<1/3$, the restricted nullspace property holds for
  every $S$ with $|S|\le s$, so every $s$-sparse vector is recovered from
  its noiseless measurements. For independent centered unit-variance
  sub-Gaussian entries there are constants $C,c>0$, depending only on the
  sub-Gaussian parameter, such that $\delta_{2s}(n^{-1/2}X)<1/3$ with
  probability at least $1-2e^{-cn}$ whenever $n\ge Cs\log(ep/s)$, by CKMA
  SYNOPSIS07, item 48.

Write $\sigma_s(\beta)_1=\min\{\|\beta-b\|_1:b\text{ has at most }s
\text{ nonzero coordinates}\}$ for the $\ell^1$ error of best $s$-term
approximation.

* **49. Stable recovery under restricted isometry.** Let $A$ be an
  $n\times p$ matrix with
  $$\delta_{2s}(A)<\frac4{\sqrt{41}}\approx0.6246.$$
  For every $\beta\in\mathbb R^p$ and $y$ with $\|A\beta-y\|_2\le\eta$, every
  minimizer $\beta^\sharp$ of $\|b\|_1$ subject to $\|Ab-y\|_2\le\eta$
  satisfies
  $$\|\beta^\sharp-\beta\|_1\le C\sigma_s(\beta)_1+D\sqrt s\,\eta,
  \qquad
  \|\beta^\sharp-\beta\|_2\le\frac C{\sqrt s}\sigma_s(\beta)_1+D\eta,$$
  with constants $C,D$ depending only on $\delta_{2s}(A)$. For $\eta=0$ and
  $s$-sparse $\beta$ this gives $\beta^\sharp=\beta$.

* **50. Support recovery under mutual incoherence.** Let $\beta$ be
  supported on $S$ with $|S|=s$. Assume that
  $\lambda_{\min}(X_S^\top X_S/n)\ge c_{\min}>0$ and that, for some
  $\alpha\in[0,1)$,
  $$\max_{j\notin S}\bigl\|(X_S^\top X_S)^{-1}X_S^\top X_{\cdot j}\bigr\|_1
  \le\alpha.$$
  Let $\Pi$ be the orthogonal projection onto the orthogonal complement of
  the column span of $X_S$, and let
  $$\lambda\ge\frac2{1-\alpha}
  \Bigl\|X_{S^c}^\top\Pi\varepsilon/n\Bigr\|_\infty.$$
  Then the lasso has a unique solution, its support is contained in $S$,
  and
  $$\|\hat\beta_S-\beta_S\|_\infty\le
  B=\Bigl\|\Bigl(\frac{X_S^\top X_S}n\Bigr)^{-1}
  \frac{X_S^\top\varepsilon}n\Bigr\|_\infty
  +\Bigl\|\Bigl(\frac{X_S^\top X_S}n\Bigr)^{-1}\Bigr\|_{\infty\to\infty}
  \lambda.$$
  Every $j\in S$ with $|\beta_j|>B$ is selected. If the errors are
  independent, centered, and $\sigma$-sub-Gaussian, and
  $\|X_{\cdot j}\|_2\le C\sqrt n$ for all $j$, the choice
  $$\lambda=\frac{2C\sigma}{1-\alpha}
  \Bigl(\sqrt{\frac{2\log(p-s)}n}+\delta\Bigr)$$
  gives these conclusions with probability at least $1-4e^{-n\delta^2/2}$,
  with the first term of $B$ at most
  $c_{\min}^{-1/2}\sigma(\sqrt{2(\log s)/n}+\delta)$.

### Low-rank and structured covariance estimation

For matrices write $\|\cdot\|_{\mathrm{op}}$, $\|\cdot\|_F$, and
$\|\cdot\|_{\mathrm{nuc}}$ for the operator, Frobenius, and nuclear
(trace) norms, and $\|M\|_{\max}=\max_{j,k}|M_{jk}|$. In **trace
regression** one observes $y_i=\mathop{\mathrm{tr}}(X_i^\top\Theta^*)+w_i$,
$i=1,\ldots,n$, for an unknown $d_1\times d_2$ matrix $\Theta^*$.

* **51. Nuclear-norm penalized trace regression.** Let the $X_i$ have
  independent standard normal entries, let the $w_i$ be independent
  $N(0,\sigma^2)$ and independent of the design, and let $\Theta^*$ have
  rank at most $r$. Let $\hat\Theta$ minimize
  $$\frac1{2n}\sum_{i=1}^n\bigl(y_i-\mathop{\mathrm{tr}}(X_i^\top\Theta)\bigr)^2
  +\lambda\|\Theta\|_{\mathrm{nuc}},
  \qquad\lambda=10\sigma\Bigl(\sqrt{\frac{d_1+d_2}n}+\delta\Bigr).$$
  There are universal constants $c,C$ such that, if
  $n>c\,r(d_1+d_2)$, then with probability at least $1-2e^{-2n\delta^2}$,
  $$\|\hat\Theta-\Theta^*\|_F^2\le
  C\sigma^2\Bigl(\frac{r(d_1+d_2)}n+r\delta^2\Bigr).$$

Let $x_1,\ldots,x_n$ be independent copies of a centered random vector in
$\mathbb R^p$ with covariance $\Sigma$, and let
$\hat\Sigma=n^{-1}\sum_ix_ix_i^\top$. The **hard-threshold operator**
$T_\lambda$ replaces each entry $u$ of a matrix by $u1_{\{|u|>\lambda\}}$.
Let $A$ be the $0$–$1$ matrix with $A_{jk}=1$ exactly when
$\Sigma_{jk}\ne0$.

* **52. Thresholded covariance estimation.** If
  $\|\hat\Sigma-\Sigma\|_{\max}\le\lambda$, then
  $$\|T_\lambda(\hat\Sigma)-\Sigma\|_{\mathrm{op}}
  \le2\lambda\|A\|_{\mathrm{op}}\le2s\lambda,$$
  where $s$ is the largest number of nonzero entries in a row of $\Sigma$.
  If each coordinate of $x_i$ is $\sigma$-sub-Gaussian and $n>\log p$, the
  choice $\lambda=\sigma^2(8\sqrt{(\log p)/n}+\delta)$ makes this event hold
  with probability at least $1-8e^{-n\min(\delta,\delta^2)/16}$. With
  $\delta=\sqrt{(\log p)/n}$ this gives
  $$\|T_\lambda(\hat\Sigma)-\Sigma\|_{\mathrm{op}}
  \le18s\sigma^2\sqrt{(\log p)/n}$$
  with probability at least $1-8p^{-1/16}$. This is the thresholding
  estimator of Bickel and Levina.

For a centered Gaussian vector with covariance $\Sigma$ and **precision
matrix** $\Theta=\Sigma^{-1}$, the conditional-independence graph of
SYNOPSIS105, item 26, has an edge $\{j,k\}$ exactly when $\Theta_{jk}\ne0$.
The **neighbourhood** $N(j)$ of $j$ is the set of such $k$. The regression of
coordinate $j$ on the others has coefficients $-\Theta_{jk}/\Theta_{jj}$,
so its support is $N(j)$. **Neighbourhood selection** runs a lasso of each
coordinate on the others and joins the estimated neighbourhoods by the
"and" or the "or" rule. The **graphical lasso** minimizes
$$\mathop{\mathrm{tr}}(\Theta\hat\Sigma)-\log\det\Theta
+\lambda\sum_{j\ne k}|\Theta_{jk}|$$
over positive definite $\Theta$.

* **53. Gaussian graphical model selection.** Let the data be $n$
  independent $N(0,\Sigma)$ vectors in $\mathbb R^p$, with
  $\Sigma_{jj}\le1$, at most $m$ neighbours per vertex, and
  $n\ge c_1m\log p$. Suppose that for each $j$ the covariance
  $\Gamma$ of the coordinates other than $j$ satisfies
  $$\max_{k\notin N(j)}\|\Gamma_{kN(j)}\Gamma_{N(j)N(j)}^{-1}\|_1\le1-\alpha$$
  for some $\alpha\in(0,1]$, and that
  $\|\Sigma_{N(j)N(j)}^{-1}\|_{\infty\to\infty}\le b$ with $b\ge1$. With
  $\lambda=c_0\alpha^{-1}(\sqrt{(\log p)/n}+\delta)$, $0<\delta\le1$,
  neighbourhood selection by either rule includes no false edge and
  includes every edge with
  $|\Theta_{jk}|\ge7b\lambda\max(\Theta_{jj},\Theta_{kk})$, that is, every
  edge whose two regression coefficients $-\Theta_{jk}/\Theta_{jj}$ and
  $-\Theta_{jk}/\Theta_{kk}$ are at least $7b\lambda$ in absolute value,
  with probability at least $1-c_2\exp(-c_3n\min(\delta^2,1/m))$; the
  constants $c_0,c_1,c_2,c_3$ are universal. Since $\Theta_{jj}\ge1$ is not
  bounded above by these hypotheses, this condition is stronger than
  $|\Theta_{jk}|\ge7b\lambda$, the form in the statement of Wainwright
  (2019), Theorem 11.12; the proof there bounds the regression coefficients
  and gives the condition stated here. For the graphical lasso, let the
  coordinates of the observations be $\sigma$-sub-Gaussian, let $\Theta$
  have at most $m$ nonzero entries per row, and let
  $\lambda=8\sigma^2(\sqrt{(\log p)/n}+\delta)$ with $0<\delta\le1$. If
  $6(\|\Theta\|_{\mathrm{op}}+1)^2\lambda\sqrt{mp}<1$, then with
  probability at least $1-8e^{-n\delta^2/16}$ the graphical-lasso estimate
  $\hat\Theta$ satisfies
  $$\|\hat\Theta-\Theta\|_F^2\le9(\|\Theta\|_{\mathrm{op}}+1)^4mp\lambda^2.$$

### Principal components in high dimensions

* **54. Perturbation of the leading eigenvector.** Let $\Sigma$ be
  symmetric positive semidefinite with eigenvalues
  $\gamma_1>\gamma_2\ge\cdots$, eigengap $\nu=\gamma_1-\gamma_2$, and unit
  leading eigenvector $\theta^*$. Let $P$ be symmetric with
  $\|P\|_{\mathrm{op}}<\nu/2$. Then $\Sigma+P$ has a unique leading unit
  eigenvector $\hat\theta$, up to sign, and with the sign chosen so that
  $\langle\hat\theta,\theta^*\rangle\ge0$,
  $$\|\hat\theta-\theta^*\|_2\le
  \frac{2\|(I-\theta^*\theta^{*\top})P\theta^*\|_2}{\nu-2\|P\|_{\mathrm{op}}}.$$
  This is a form of the Davis–Kahan theorem, CKMA SYNOPSIS13, item 67. In
  the spiked model $\Sigma=\nu\theta^*\theta^{*\top}+I_p$ with
  $x_i=\sqrt\nu\,\xi_i\theta^*+w_i$, where $\xi_i$ and $w_i$ are
  independent, centered, sub-Gaussian with parameter at most one, of
  variance one and covariance $I_p$ respectively, assume $n>p$ and
  $\nu^{-2}(\nu+1)p/n\le1/128$. Then with probability at least
  $1-c_1\exp(-c_2n\min(\sqrt\nu\,\delta,\nu\delta^2))$, the leading sample
  eigenvector satisfies
  $$\|\hat\theta-\theta^*\|_2\le
  c_0\sqrt{\frac{\nu+1}{\nu^2}\frac pn}+\delta,$$
  with universal constants $c_0,c_1,c_2$.

* **55. Spiked sample eigenvectors.** In the spiked model of item 38 with a
  single spike $\alpha>1+\sqrt y$ in the direction $e_1$, let $\hat u$ be a
  unit eigenvector of the sample covariance for its largest eigenvalue.
  Almost surely,
  $$\langle\hat u,e_1\rangle^2\to
  \frac{(\alpha-1)^2-y}{(\alpha-1)(\alpha-1+y)}.$$
  The limit is strictly less than one when $y>0$, and it tends to zero as
  $\alpha$ decreases to the threshold $1+\sqrt y$ at which the sample
  eigenvalue of item 38 separates from the bulk. Thus, when $y>0$,
  $|\langle\hat u,e_1\rangle|$ does not tend to $1$, and $\hat u$ is not a
  consistent estimator of $\pm e_1$.

## Reference guide

### Correspondence with the subdivisions

- **[103A](#synopsis-103a)**: Wand and Jones, Fan and Gijbels, Wahba,
  Groeneboom and Jongbloed, Johnstone's Gaussian-sequence draft, the wavelet
  monograph of Härdle, Kerkyacharian, Picard, and Tsybakov, and Ingster and
  Suslina carry the smoothing expansions, the representer theorem,
  shape-constrained limits, and the sequence-model minimax theory. Rank
  asymptotics are the subject of Hájek, Šidák, and Sen, and of van der Vaart,
  Chapters 13–15. Samworth and Shah give the finite-sample shape-constrained
  risk bounds. Hsing and Eubank develop the Hilbert-space geometry, the
  covariance operator, and the asymptotics of functional principal components.
- **[103B](#synopsis-103b)**: van de Geer, Wainwright, Giraud, Koltchinskii,
  and Massart carry sparsity and penalized model selection. Dudoit and van der
  Laan, and Dickhaus, carry multiple testing. Yao, Zheng, and Bai carry the
  Wishart edge and the spiked model. Vershynin, Boucheron, Lugosi, and
  Massart, Tropp, and Foucart and Rauhut supply the concentration and
  restricted-isometry ingredients cited from the analysis synopsis. Tsybakov
  and Giraud carry the hypercube and sparse minimax lower bounds; Wainwright
  carries sparse recovery, low-rank and graphical-model estimation, and
  high-dimensional principal components.

### Source comparisons and local copies

#### Nonparametric, semiparametric, and robust inference

Hollander, Wolfe, and Chicken, Chapters 3, 4, and 6, provide the exact sign
and rank procedures and the several-sample comparison. Robertson,
Wright, and Dykstra, Section 1.2 and the max–min formulas of Section 1.4,
give the cumulative-sum and max–min descriptions of isotonic regression.
Wand–Jones and Fan–Gijbels supply the bias expansions; the bandwidth
conditions ensure that replacing the exact bias by its leading term is
legitimate in the normal limit. Tsybakov's full text is available in
`ReferencesSuppl`; its regression upper and lower bound chapters were
consulted, including the supremum-norm comparison in Corollary 2.5. Item 22
records the corresponding one-dimensional Hölder rates for the regular
design, from Theorems 1.7 and 2.8 and Corollaries 2.3 and 2.5. Hsing–Eubank,
Chapters 1 and 9, supplies the reconstruction interpretation and the
spectral perturbation framework.

The kernel expansions of items 4 and 6 are the interior-point formulae of
Wand and Jones and of Fan and Gijbels. Item 8 is the Kimeldorf–Wahba
representer theorem, as used throughout Wahba's spline monograph. Items 9 and 10 follow Johnstone's chapters on Pinsker's theorem and on thresholding.
Item 11 is the pointwise limit in Groeneboom and Jongbloed. Item 13 is the
Sobolev detection boundary of Ingster and Suslina. Item 12 is the cone
mixture of Robertson, Wright, and Dykstra.

The following passages support items 14–17, 23–28, and 32. The rank items 14–17
follow van der Vaart, Theorem 13.5, Section 13.3 and Examples 13.13–13.22,
Corollary 15.10 and Example 15.15, Table 14.2 with Problem 14.8, Examples
12.5 and 12.13, and Corollary 19.21 and Theorem 19.23. The exact null
moments of Kendall's and Spearman's statistics and the two-sample
Kolmogorov–Smirnov limit are those of Hollander, Wolfe, and Chicken,
Sections 5.4, 8.1, and 8.5; the Chernoff–Savage bound is quoted there. Item 23 follows Tsybakov, Proposition 1.9, and Wasserman, Theorems 5.34,
6.34, and 6.37. Stone (1984), *Ann. Statist.* 12, 1285–1297, was not
accessible. Its abstract (as reviewed in zbMATH/MaRDI) assumes only that
the density and its one-dimensional marginals are bounded; secondary
sources report that Stone's kernel is compactly supported and Hölder
continuous and that his criterion is $M_1$ (Stark's Berkeley lecture
notes; Wasserman's (6.35) writes the cross-validation score in this form
up to a remainder). Whether the theorem holds verbatim for
$\mathop{\mathrm{CV}}$ with divisor $n-1$ was not checked. Symmetry
and nonnegativity of $K$ are retained as hypotheses but were not checked
against Stone's paper. Item 24 is Fan–Gijbels, Theorems 3.1 and
3.2 with Sections 3.2.2 and 3.3. Item 25 is Green–Silverman, Theorems 2.4
and 3.1. The unnumbered remark after it follows Green–Silverman, Section 3.7,
on Silverman's equivalent kernel, and Tsybakov, Section 1.3, on its Fourier
transform. Item 26 combines Tsybakov, Theorem 1.1
and Exercises 2.8 and 2.10, with van der Vaart, Theorems 24.2 and 24.4.
Items 27 and 28 are Samworth and Shah, Theorems 9.39, 9.15, and 9.26, with
the tent-function description of Section 9.2.

Item 32 is Hsing and Eubank, Theorems 11.2.7 and 11.3.1.

Lehmann's *Nonparametrics*, Silverman's density monograph, and the Györfi,
Kohler, Krzyżak, and Walk distribution-free regression monograph were not
located in the local reference directories. Hájek, Šidák, and Sen is present
as a DjVu file and was not text-extracted.

#### High-dimensional statistics and statistical learning

Wainwright's Chapter 15 was read for the estimation-to-testing reduction, Le
Cam's method, and Proposition 15.12 on Fano's method. Its sparse-regression
and model-selection chapters supply the surrounding regularization
framework. Item 33 distinguishes a sparsity-tuned threshold from the
universal threshold, and item 35 requires a sufficiently large penalty
multiplier. Item 36 is stated for Gaussian regression with known variance,
where the optimism identity behind Akaike's criterion is exact. Item 43 states the exact bias decomposition, a sufficient
remainder condition, and the coordinate intervals that follow from it,
without asserting that the remainder condition holds for arbitrary
designs.

Item 34 is the consequence, at stretching factor $3$, of the sharp oracle
inequality in van de Geer for the lasso normalized as
$n^{-1}\|Y-X\beta\|_2^2+2\lambda\|\beta\|_1$. The factor $3$ is the cone
constant obtained when the penalty level is at least twice
$n^{-1}\|X^\top\varepsilon\|_\infty$. Item 38 follows Yao, Zheng, and Bai:
the centering $\mu_{n,p}$ is asymptotic to the Marchenko–Pastur right edge
$(1+\sqrt y)^2$, and the spike map $\alpha+y\alpha/(\alpha-1)$ is continuous
at the threshold $1+\sqrt y$.

For items 45–55, and SYNOPSIS107, items 10–15 the following passages were read. Tsybakov, Lemma 2.9 and
Lemma 2.12 with Theorem 2.12, supplies the Varshamov–Gilbert bound and
Assouad's lemma; the metric reduction in item 46 is the nearest-index
argument of his Example 2.2. Giraud, Theorem 3.5 and Section 3.4.2, gives
the sparse-regression minimax bound of item 47. Wainwright supplies Theorem
7.8 and Proposition 7.11 (item 48), Theorem 7.13 (the $\ell^2$ bound in item 34), Theorem 7.21 and
Corollary 7.22 (item 50), Corollary 10.10 for the standard Gaussian ensemble
(item 51), Theorem 6.23 and Corollary 6.24 (item 52), Proposition 11.9 and
Theorem 11.12 (item 53), Theorem 8.5 and Corollary 8.7 (item 54), and
Theorem 13.17, Corollary 13.18, and Examples 13.19–13.20 (SYNOPSIS107, item 13). Foucart
and Rauhut, Theorem 6.12, gives item 49. Yao, Zheng, and Bai, Theorem 11.5
and Corollary 11.6, give the spiked-eigenvector limit of item 55.

The graphical-lasso bound in item 53 is Wainwright's Proposition 11.9,
checked against a layout-preserving extraction of the local copy: the side
condition is $6(\|\Theta\|_{\mathrm{op}}+1)^2\lambda_n\sqrt{md}<1$, as at the
end of the proof. The constant in the conclusion is the one given by
Corollary 9.20, bound (9.49b), $9\lambda_n^2\Psi^2/\kappa^2$ with
$\Psi^2\le md$ and $\kappa=(\|\Theta\|_{\mathrm{op}}+1)^{-2}$; the
printed display (11.11) appears to set the factor
$(\|\Theta\|_{\mathrm{op}}+1)^4$ as a denominator, which is inconsistent
with that proof.
No local source treats the knockoff filter or PAC-Bayes bounds, and the
boosting training-error bound is left to the model-oriented Section 107.

The false-discovery statement in item 37 is the Benjamini–Hochberg theorem
under independence and under positive regression dependence. A supplemental
copy of Cucker and Zhou, *Learning Theory*, is present but is not part of
the consulted source basis.

Local texts directly consulted or identified for this selection:

- [Hollander, Wolfe, and Chicken, *Nonparametric Statistical Methods*](../lean-CKMA/References/HollanderWolfeChicken2014NonparametricStatisticalMethods3rdEd-Wiley.SerProbStat.pdf).
- [Tsybakov, *Introduction to Nonparametric Estimation*](../lean-CKMA/ReferencesSuppl/Tsybakov2009IntroductionNonparametricEstimation-SpringerSSS.pdf).
- [Wand and Jones, *Kernel Smoothing*](../lean-CKMA/References/WandJones1995KernelSmoothing-ChapmanHallCRC.MSAP60.pdf).
- [Fan and Gijbels, *Local Polynomial Modelling and Its Applications*](../lean-CKMA/References/FanGijbels1996LocalPolynomialModellingApplications-ChapmanHallCRC.MSAP66.pdf).
- [Wahba, *Spline Models for Observational Data*](../lean-CKMA/References/Wahba1990SplineModelsObservationalData-SIAM.CBMS59.pdf).
- [Groeneboom and Jongbloed, *Nonparametric Estimation under Shape Constraints*](../lean-CKMA/References/GroeneboomJongbloed2014NonparametricEstimationShapeConstraintsEstimatorsAlgorithmsAsymptotics-Cambridge.SerStatProbMath.pdf).
- [Johnstone, *Gaussian Estimation: Sequence and Wavelet Models*](../lean-CKMA/References/Johnstone2017GaussianEstimationSequenceWaveletModels-AuthorManuscript.pdf).
- [Härdle, Kerkyacharian, Picard, and Tsybakov, *Wavelets, Approximation, and Statistical Applications*](../lean-CKMA/References/HärdleKerkyacharianPicardTsybakov1998WaveletsApproximationStatisticalApplications-Springer.LNS129.pdf).
- [Ingster and Suslina, *Nonparametric Goodness-of-Fit Testing Under Gaussian Models*](../lean-CKMA/References/IngsterSuslina2003NonparametricGoodnessFitTestingGaussianModels-Springer.LNS169.pdf).
- [Robertson, Wright, and Dykstra, *Order Restricted Statistical Inference*](../lean-CKMA/References/RobertsonWrightDykstra1988OrderRestrictedStatisticalInference-Wiley.SerProbStat.pdf).
- [Devroye and Lugosi, *Combinatorial Methods in Density Estimation*](../lean-CKMA/References/DevroyeLugosi2001CombinatorialMethodsDensityEstimation-Springer.SSS.pdf).
- [Hsing and Eubank, *Theoretical Foundations of Functional Data Analysis*](../lean-CKMA/References/HsingEubank2015TheoreticalFoundationsFunctionalDataAnalysisIntroductionLinearOperators-Wiley.SerProbStat.pdf).
- [Hájek, Šidák, and Sen, *Theory of Rank Tests*](../lean-CKMA/References/HájekŠidákSen1999TheoryRankTests2ndEd-AcademicPress.djvu).
- [van der Vaart, *Asymptotic Statistics*](../lean-CKMA/References/VanDerVaart1998AsymptoticStatistics-CambridgeSerStatProbMath03.pdf).
- [Wasserman, *All of Nonparametric Statistics*](../lean-CKMA/ReferencesSuppl/Wasserman2006NonparametricStatistics-SpringerSTS.pdf).
- [Green and Silverman, *Nonparametric Regression and Generalized Linear Models*](../lean-CKMA/References/GreenSilverman1994NonparametricRegressionGeneralizedLinearModelsRoughnessPenaltyApproach-ChapmanHall.MSAP58.pdf).
- [Samworth and Shah, *Modern Statistical Methods and Theory*](../lean-CKMA/References/SamworthShah2026ModernStatisticalMethodsTheoryIntroductionNonparametricHighDimensionalStatistics-Cambridge.SerStatProbMat.pdf).
- [van de Geer, *Estimation and Testing Under Sparsity*](../lean-CKMA/References/VanDeGeer2016EstimationTestingUnderSparsityÉcoleDÉtéProbabilitésSaintFlourXLV2015-Springer.LNM2159.pdf).
- [Wainwright, *High-Dimensional Statistics*](../lean-CKMA/References/Wainwright2019HighDimensionalStatistics-Cambridge.pdf).
- [Giraud, *Introduction to High-Dimensional Statistics*](../lean-CKMA/References/Giraud2022IntroductionHighDimensionalStatistics2ndEd-ChapmanHallCRC.MSAP168.pdf).
- [Massart, *Concentration Inequalities and Model Selection*](../lean-CKMA/References/Massart2007ConcentrationInequalitiesModelSelectionÉcoleDÉtéProbabilitésSaintFlourXXXIII2003-Springer.LNM1896.pdf).
- [Koltchinskii, *Oracle Inequalities in Empirical Risk Minimization*](../lean-CKMA/References/Koltchinskii2011OracleInequalitiesEmpiricalRiskMinimizationSparseRecoveryProblems-Springer.LNM2033.pdf).
- [Yao, Zheng, and Bai, *Large Sample Covariance Matrices and High-Dimensional Data Analysis*](../lean-CKMA/References/YaoZhengBai2015LargeSampleCovarianceMatricesHighDimensionalDataAnalysis-Cambridge.SerStatProbMath.pdf).
- [Dudoit and van der Laan, *Multiple Testing Procedures*](../lean-CKMA/References/DudoitVanDerLaan2008MultipleTestingProceduresApplicationsGenomics-Springer.SSS.pdf).
- [Dickhaus, *Simultaneous Statistical Inference*](../lean-CKMA/References/Dickhaus2014SimultaneousStatisticalInferenceApplicationsLifeSciences-Springer.pdf).
- [Vershynin, *High-Dimensional Probability*](../lean-CKMA/References/Vershynin2018HighDimensionalProbabilityIntroductionApplicationsDataScience-CambridgeSerStatProbMath47.pdf).
- [Boucheron, Lugosi, and Massart, *Concentration Inequalities*](../lean-CKMA/References/BoucheronLugosiMassart2013ConcentrationInequalitiesNonasymptoticTheoryIndependence-Oxford.pdf).
- [Foucart and Rauhut, *A Mathematical Introduction to Compressive Sensing*](../lean-CKMA/References/FoucartRauhut2013MathematicalIntroductionCompressiveSensing-BirkhäuserANHA.pdf).
