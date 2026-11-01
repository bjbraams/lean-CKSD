# Synopsis: Nonparametric, semiparametric, and robust inference

Part of the [mathematical synopsis series](SYNOPSIS.md).
[Bibliographical scope and references](CKSD-bib.md#cks-104).

This synopsis follows Section 104. Subdivision 104A is rank methods, smoothing,
shape constraints, and minimax rates. Subdivision 104B is semiparametric
efficiency and missing data. Subdivision 104C is robust estimation.
Subdivision 104D is functional data. Parametric efficiency is
[SYNOPSIS103](SYNOPSIS103.md), items 9–12. The empirical-process limit and the
Dvoretzky–Kiefer–Wolfowitz inequality are
[CKMA SYNOPSIS06](../lean-CKMA/SYNOPSIS06.md), item 59, and
[CKMA SYNOPSIS07](../lean-CKMA/SYNOPSIS07.md), item 39. High-dimensional
penalties and learning bounds are in Section 107. Nonparametric priors are in
Section 105.

Numbered definitions and results have stable identifiers. Additions take the
next free number and are placed beside related material; numbers need not
increase in reading order. Proofs are outside the scope of this synopsis.

<a id="synopsis-104a"></a>

## 104A. Ranks, Smoothing, Shape Constraints, and Minimax Estimation

Throughout this subdivision, $X_1,\ldots,X_n$ are independent copies of a real
random variable with distribution function $F$ and, when a density exists,
density $f$. The empirical distribution function is $F_n$.

* **1. Kolmogorov–Smirnov statistic.** If $F$ is continuous, the law of
  $\sup_x|F_n(x)-F(x)|$ does not depend on $F$. By the empirical-process
  limit,
  $$\sqrt n\sup_x|F_n(x)-F(x)|\Rightarrow\sup_{t\in[0,1]}|B^0(t)|,$$
  and for $x>0$
  $$P\bigl(\sup_t|B^0(t)|\le x\bigr)
  =1-2\sum_{k=1}^\infty(-1)^{k-1}e^{-2k^2x^2}.$$
  The Dvoretzky–Kiefer–Wolfowitz inequality supplies the corresponding
  finite-sample tail bound.

* **2. Linear rank statistics.** Let the observations be continuous and
  independent, and let $R_i$ be the rank of the $i$th observation in the
  pooled sample. Under a null hypothesis that makes the vector of ranks
  uniform on the permutations, every rank statistic has a distribution free
  of the unknown continuous law. For scores $a_n(i)$ and regression constants
  $c_{n,i}$ satisfying the usual growth and nondegeneracy conditions, the
  Hájek projection of the linear rank statistic
  $S_n=\sum_i c_{n,i}a_n(R_i)$ is asymptotically normal under the null and
  under contiguous location alternatives. In the two-sample shift problem
  the Wilcoxon rank-sum test is the locally most powerful rank test for the
  logistic shift, and its Pitman efficiency relative to the two-sample $t$
  test, at a normal shift, equals $3/\pi$.

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
  continuously differentiable, with $f$ and $f''$ square-integrable and $f(x)>0$.
  If $h\to0$, $nh\to\infty$, and $nh^5=O(1)$, then
  $$\sqrt{nh}\Bigl(\hat f_h(x)-f(x)-\tfrac12 h^2\mu_2(K)f''(x)\Bigr)
  \Rightarrow N\bigl(0,R(K)f(x)\bigr).$$
  The asymptotic mean integrated squared error is
  $$\tfrac14 h^4\mu_2(K)^2\int(f'')^2+R(K)/(nh),$$
  and the bandwidth of exact order $n^{-1/5}$ minimizes the displayed
  expression. The resulting optimal rate is of order $n^{-4/5}$.

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
  Assume a locally bounded conditional $(2+\delta)$ moment of $Y$ for
  some $\delta>0$, and a nonnegative bounded symmetric compactly supported
  probability kernel positive near zero. If $h\to0$, $nh\to\infty$, and
  $nh^5=O(1)$, the local linear estimator satisfies
  $$\sqrt{nh}\Bigl(\hat m_h(x)-m(x)-\tfrac12 h^2\mu_2(K)m''(x)\Bigr)
  \Rightarrow N\Bigl(0,\frac{R(K)\sigma^2(x)}{f_X(x)}\Bigr).$$
  If in addition $f_X$ and $m$ are continuously differentiable at $x$, the
  Nadaraya–Watson estimator satisfies the same limit with the bias
  $\tfrac12 h^2\mu_2(K)m''(x)$ replaced by
  $$\tfrac12 h^2\mu_2(K)\Bigl(m''(x)+2m'(x)\frac{f_X'(x)}{f_X(x)}\Bigr).$$
  At a boundary point the local linear bias remains of order $h^2$, while the
  Nadaraya–Watson bias is of order $h$.

* **7. Stone's theorem.** Assume $\mathbb E Y^2<\infty$. For kernel
  regression with a nonnegative bounded compactly supported kernel
  bounded below by a positive constant in a neighborhood of zero,
  $h\to0$ and $nh^d\to\infty$ imply
  $$\mathbb E\bigl[(\hat m_n(X)-m(X))^2\bigm|X_1,Y_1,\ldots,X_n,Y_n\bigr]
  \to0$$
  in probability, for every distribution of $(X,Y)$ on $\mathbb R^d\times\mathbb R$.
  The same universal $L^2$ consistency holds for $k$-nearest-neighbor
  regression when $k\to\infty$ and $k/n\to0$.

Let $\mathcal H$ be a reproducing-kernel Hilbert space of real functions on
a set $\mathcal X$, with kernel $K$. A loss $L(y,u)$ is evaluated only through
the predicted value $u$.

* **8. Representer theorem.** A minimizer of
  $$\frac1n\sum_{i=1}^n L(Y_i,f(X_i))+\lambda\|f\|_{\mathcal H}^2,
  \qquad\lambda>0,$$
  over $f\in\mathcal H$, has the form
  $f(\cdot)=\sum_{i=1}^n\alpha_i K(X_i,\cdot)$. In particular, the smoothing
  spline
  $$\sum_{i=1}^n(Y_i-f(x_i))^2+\lambda\int(f'')^2$$
  on the Sobolev space of square-integrable second derivatives has a
  minimizer that is a natural cubic spline with knots at the design points
  $x_i$.

In the **Gaussian sequence model**, one observes
$Y_i=\theta_i+\varepsilon\xi_i$ for $i\ge1$, with $\xi_i$ independent standard
normal. The white-noise model $dY(t)=f(t)\,dt+\varepsilon\,dW(t)$ on $[0,1]$
is equivalent to a sequence model through an orthonormal basis.

* **9. Pinsker's theorem and the Sobolev rate.** For the ellipsoid
  $\sum_{j\ge1}a_j^2\theta_j^2\le R$ with $a_j$ regularly varying of order
  $\beta>0$, the minimax mean squared error among all estimators is
  asymptotic, as $\varepsilon\to0$, to the minimax risk among linear
  estimators. A linear shrinkage filter attains the asymptotic constant.
  For a Sobolev ball of smoothness $\beta$ and radius $R$ in the white-noise
  model, this risk is of exact order
  $R^{1/(2\beta+1)}\varepsilon^{4\beta/(2\beta+1)}$. With
  $\varepsilon=n^{-1/2}$ the squared-error rate is
  $n^{-2\beta/(2\beta+1)}$.

* **10. Soft-threshold oracle inequality.** In the finite sequence model
  $Y_i=\theta_i+\sigma\xi_i$, $i=1,\ldots,n$, let $\hat\theta$ be coordinatewise
  soft thresholding at $\lambda=\sigma\sqrt{2\log n}$. Then
  $$\mathbb E\|\hat\theta-\theta\|^2
  \le(2\log n+1)\Bigl(\sigma^2+\sum_{i=1}^n\min(\theta_i^2,\sigma^2)\Bigr).$$
  The estimator therefore tracks, up to the factor $2\log n+1$, the ideal
  risk of an oracle that retains only those coordinates larger than the
  noise level.

* **11. Grenander estimator.** Let $f$ be decreasing and positive on
  $[0,\infty)$, with $f'(x_0)<0$ and $f$ continuous at $x_0>0$. The maximum
  likelihood estimator $\hat f_n$ is the left slope of the least concave
  majorant of $F_n$. Then
  $$n^{1/3}\bigl(\hat f_n(x_0)-f(x_0)\bigr)
  \Rightarrow\bigl|4f(x_0)f'(x_0)\bigr|^{1/3}Z,$$
  where $Z=\mathop{\mathrm{argmax}}_{t\in\mathbb R}\bigl(W(t)-t^2\bigr)$ and
  $W$ is standard two-sided Brownian motion. The limit law is Chernoff's
  distribution up to the deterministic scale displayed above.

Let $K\subset\mathbb R^p$ be a closed polyhedral convex cone and let
$Y\sim N_p(\mu,I_p)$. Write $P_K$ for metric projection onto $K$.

* **12. Chi-bar-squared limit.** The likelihood-ratio statistic for testing
  $\mu=0$ against $\mu\in K$ equals $\|P_KY\|^2$. Under the null its law is
  the mixture $\sum_{j=0}^p w_j\chi^2_j$, where $w_j$ is the probability that
  $P_KY$ lies in the relative interior of a $j$-dimensional face of $K$.
  The same mixture limit, with weights determined by the cone of feasible
  directions after whitening by the information matrix, holds for
  regular fixed-dimensional likelihood-ratio tests with polyhedral tangent
  cones. For Gaussian monotone regression at a fixed finite design,
  the corresponding cone projection gives the finite-sample mixture;
  an increasing-dimensional problem needs its own asymptotic analysis.

Testing $f=0$ in the white-noise model against a smoothness class at a
positive $L^2$ separation is a different problem from estimating $f$.

* **13. Nonparametric detection boundary.** In the white-noise model, the
  minimax separation $\rho_n$ for testing $f=0$ against the alternative
  that $f$ lies in a Sobolev or Hölder ball of smoothness $\beta$ and
  $\|f\|_2\ge\rho_n$ is of order $n^{-2\beta/(4\beta+1)}$. At smaller
  orders no test can separate zero uniformly from all alternatives at that
  separation. At sufficiently larger orders uniformly consistent tests
  exist. The detection separation is smaller than the $L^2$ estimation
  error rate $n^{-\beta/(2\beta+1)}$ of item 9.

### Rank scores, rank correlation, and goodness of fit

Let $U_{N(1)}<\cdots<U_{N(N)}$ be the order statistics of $N$ independent
uniform variables on $[0,1]$. A measurable, not almost everywhere constant
function $\varphi$ on $(0,1)$ with $\int_0^1\varphi^2<\infty$ is a
**score-generating function**; it generates the **exact scores**
$a_N(i)=\mathbb E\varphi(U_{N(i)})$ and the **approximate scores**
$\varphi(i/(N+1))$. Write $\bar c_N$ and $\bar a_N$ for the averages of the
regression constants and of the scores.

* **32. Score-generating functions and locally most powerful rank tests.**
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
  test of $\theta=0$ against small $\theta>0$ rejects for large $T_N$ with
  exact scores generated by
  $$\varphi_f(u)=-\frac{f'}{f}\bigl(F^{-1}(u)\bigr).$$
  For the logistic density this gives the Wilcoxon scores $i$; for the
  normal density it gives the normal scores
  $\mathbb E\Phi^{-1}(U_{N(i)})$, of which
  $\Phi^{-1}(i/(N+1))$ are the van der Waerden approximations. For the
  scale family $e^{-\theta}f(e^{-\theta}x)$ the generating function is
  $-1-F^{-1}(u)\,(f'/f)(F^{-1}(u))$; for proportional-hazards alternatives
  it gives the log-rank (Savage) scores of SYNOPSIS108, item 28.

* **33. Asymptotic optimality and efficiencies of rank tests.** Let
  $X_1,\ldots,X_m$ have density $f(x-\mu)$ and $Y_1,\ldots,Y_n$ density
  $f(x-\nu)$, all independent, with $f$ of finite Fisher information
  $I_f$, $N=m+n$, and $m/N\to\lambda\in(0,1)$. For local alternatives
  $\nu-\mu=h/\sqrt N$, the two-sample rank test with scores generated by
  $\varphi_f$ of item 32 has asymptotic power
  $1-\Phi\bigl(z_\alpha-h\sqrt{\lambda(1-\lambda)I_f}\bigr)$, the largest
  attainable by any asymptotically level-$\alpha$ test of $\nu=\mu$ against
  $\nu>\mu$, even when $f$ is known. Thus the Wilcoxon test is asymptotically optimal for the
  logistic shift and the normal-scores test for the normal shift. For a
  symmetric $f$ of finite Fisher information, the signed-rank statistic
  $\sum_i\mathop{\mathrm{sign}}(X_i)\,a_n(R_i^+)$, with $R_i^+$ the rank of
  $|X_i|$ and exact scores generated by
  $-(f'/f)\bigl((F^+)^{-1}(u)\bigr)$, $F^+=2F-1$ on $[0,\infty)$, gives an
  asymptotically optimal test of the center of symmetry; the scores are
  unchanged within a scale family. The Pitman efficiencies of the sign and
  Wilcoxon tests relative to the $t$ test, including the Hodges–Lehmann
  bound $108/125$, are SYNOPSIS103, item 43. The efficiency of the
  normal-scores test relative to the $t$ test is at least $1$ for every
  $f$ of finite variance, with equality at the normal law
  (Chernoff–Savage). The general theory of Pitman efficiency is
  SYNOPSIS103, item 42.

For independent copies of a pair $(X,Y)$ with continuous marginal laws,
**Kendall's tau** is $\tau=2P\bigl((X_2-X_1)(Y_2-Y_1)>0\bigr)-1$, estimated by
$$\hat\tau_n=\binom n2^{-1}\sum_{i<j}
\mathop{\mathrm{sign}}\bigl((X_j-X_i)(Y_j-Y_i)\bigr).$$
**Spearman's rho** $r_s$ is the ordinary sample correlation of the two rank
vectors, $r_s=1-6\sum_i(R_i-S_i)^2/\bigl(n(n^2-1)\bigr)$.

* **34. Rank tests of independence.** The statistic $\hat\tau_n$ is a
  $U$-statistic of order $2$ with bounded kernel. By SYNOPSIS103, item 6,
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
  Since $\tau=0$ does not imply independence, the test based on
  $\hat\tau_n$ is consistent against alternatives with $\tau\ne0$, not against
  all dependent alternatives; the same restriction applies to $r_s$ and the
  population rank correlation.

* **35. Cramér–von Mises and two-sample Kolmogorov–Smirnov limits.** If $F$
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
  against every alternative. When a parameter of a composite null family is
  estimated by an asymptotically linear estimator, the empirical process
  with estimated parameter converges to a Gaussian process whose covariance
  involves the influence function of that estimator. The resulting limits
  of the Kolmogorov–Smirnov and Cramér–von Mises statistics are no longer
  distribution-free.

### Exact ranks, smoothing bias, and shape constraints

* **22. Sign test.** For independent continuous observations with median
  $\theta_0$, $\sum_i1_{\{X_i>\theta_0\}}\sim\mathop{\mathrm{Bin}}(n,1/2)$.
  Binomial tails give exact or conservative tests of the median without a
  symmetry assumption. Inversion is the quantile interval in SYNOPSIS101,
  item 18. Symmetry is needed for the signed-rank procedure below.

* **23. Wilcoxon sampling laws.** Under a continuous distribution symmetric
  about zero, the signs are independent fair signs and independent of the
  absolute values. Thus the positive signed-rank sum has the law
  $\sum_{j=1}^n jB_j$ for independent Bernoulli$(1/2)$ variables, with
  mean $n(n+1)/4$ and variance $n(n+1)(2n+1)/24$.
  For independent samples of sizes $m,n$ from a common continuous law,
  $U=\sum_{i,j}1_{\{X_i<Y_j\}}$ has mean $mn/2$ and variance
  $mn(m+n+1)/12$. Both centered, variance-normalized statistics tend to
  $N(0,1)$, in the second case when $m/(m+n)\to\lambda\in(0,1)$.

* **24. Kruskal–Wallis test.** For $k$ independent samples from a common
  continuous law, let $R_j$ be the sum of pooled ranks in group $j$, of
  size $n_j$, and put $N=\sum_jn_j$. For fixed $k$ and
  $n_j/N\to\lambda_j>0$,
  $$\frac{12}{N(N+1)}\sum_{j=1}^k\frac{R_j^2}{n_j}-3(N+1)
  \Rightarrow\chi^2_{k-1}.$$
  Its finite-sample permutation law is distribution-free. The statistic
  tests equality of distributions; a location interpretation requires a
  common-shape shift model.

* **25. Isotonic least squares.** For observations $y_i$ at ordered design
  points and weights $w_i>0$, the minimizer of
  $\sum_iw_i(y_i-\theta_i)^2$ over $\theta_1\le\cdots\le\theta_n$ is unique
  and satisfies
  $$\hat\theta_i=\max_{a\le i}\min_{b\ge i}
  \frac{\sum_{j=a}^bw_jy_j}{\sum_{j=a}^bw_j}.$$
  It is the vector of successive slopes of the greatest convex minorant
  of the cumulative-sum diagram
  $(\sum_{j\le i}w_j,\sum_{j\le i}w_jy_j)$, including $(0,0)$.
  Pooling adjacent blocks whose weighted means violate monotonicity
  computes this projection.

* **26. Hölder regression rates.** In Gaussian regression on $[0,1]^d$
  with fixed positive noise variance and a design density bounded above and
  below by positive constants, the minimax integrated squared error over
  a fixed Hölder ball of smoothness $\beta>0$ is of order
  $n^{-2\beta/(2\beta+d)}$. Boundary-adapted local polynomials of degree
  at least $\lceil\beta\rceil-1$, with bandwidth of order
  $n^{-1/(2\beta+d)}$, attain this order. Under the same regular design
  conditions the minimax expected squared supremum error is of order
  $(\log n/n)^{2\beta/(2\beta+d)}$. The testing reductions in SYNOPSIS107,
  items 14 and 15, supply matching lower bounds.

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

* **36. Cross-validation.** If $\int f^2<\infty$ and
  $\iint|K((x-z)/h)|f(z)f(x)\,dz\,dx<\infty$, then for every $h>0$
  $$\mathbb E\mathop{\mathrm{CV}}(h)
  =\mathbb E\int(\hat f_h-f)^2-\int f^2.$$
  Minimizing $\mathop{\mathrm{CV}}$ therefore targets the mean integrated
  squared error. For a bounded density and a kernel satisfying Stone's
  regularity conditions, the cross-validated bandwidth $\hat h$ is
  asymptotically optimal:
  $$\frac{\int(\hat f_{\hat h}-f)^2}{\inf_{h>0}\int(\hat f_h-f)^2}\to1
  \quad\hbox{almost surely}.$$
  Under second-order smoothness, $\hat h$ approaches the MISE-optimal
  bandwidth only at relative rate $n^{-1/10}$. For a linear smoother whose
  leave-one-out fit $\hat m_{(-i)}$ is obtained by setting the weight of the
  $i$th observation to zero and renormalizing the remaining weights in row
  $i$, the leave-one-out score is
  $$\frac1n\sum_{i=1}^n\bigl(Y_i-\hat m_{(-i)}(x_i)\bigr)^2
  =\frac1n\sum_{i=1}^n\left(\frac{Y_i-\hat m(x_i)}{1-L_{ii}}\right)^2.$$
  Kernel, local polynomial, and spline smoothers satisfy this
  leave-one-out identity.

Let $\hat\beta(x_0)$ be the coefficient vector of the kernel-weighted
least-squares fit of a polynomial of degree $p$ in $X_i-x_0$, and estimate
$m^{(\nu)}(x_0)$, $0\le\nu\le p$, by $\hat m_\nu(x_0)=\nu!\,\hat\beta_\nu$. With
$\mu_j=\int u^jK(u)\,du$ and $S=(\mu_{j+l})_{0\le j,l\le p}$, the
**equivalent kernel** is
$$K_\nu^*(t)=e_{\nu+1}^\top S^{-1}(1,t,\ldots,t^p)^\top K(t),$$
which satisfies $\int t^qK_\nu^*(t)\,dt=\delta_{\nu q}$ for $0\le q\le p$.

* **37. Local polynomial regression.** Let $f_X(x_0)>0$, let $f_X$,
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
  $nh^3\to\infty$, the leading bias is of order $h^{p+2-\nu}$ and involves
  $f_X'(x_0)/f_X(x_0)$. Passing from an even $p-\nu$ to the next odd
  degree leaves the asymptotic variance unchanged. Odd $p-\nu$ is therefore
  preferred, usually $p=\nu+1$. At a boundary point $x_0=ch$ of the support
  of the design, the same orders of bias and variance hold with $S$ replaced
  by the truncated moment matrix $\bigl(\int_{-c}^\infty u^{j+l}K\bigr)$. The
  method thus corrects boundary bias automatically. Item 6 is the case
  $p=1$, $\nu=0$, and the Nadaraya–Watson estimator is $p=\nu=0$.

For design points $a<t_1<\cdots<t_n<b$, let $Q$ and $R$ be the
$n\times(n-2)$ and $(n-2)\times(n-2)$ band matrices of the
**value–second-derivative representation** of natural cubic splines with
knots $t_i$. For such a spline $g$, with
$\mathbf g=(g(t_1),\ldots,g(t_n))^\top$, the penalty is
$\int(g'')^2=\mathbf g^\top QR^{-1}Q^\top\mathbf g$.

* **38. Smoothing splines as linear smoothers.** Let $n\ge3$ and $\alpha>0$.
  The unique minimizer of
  $$\sum_{i=1}^n\bigl(Y_i-g(t_i)\bigr)^2+\alpha\int_a^b g''(t)^2\,dt$$
  over functions with absolutely continuous first derivative and
  square-integrable second derivative is the natural cubic spline with
  values $(I+\alpha QR^{-1}Q^\top)^{-1}Y$ at the knots. It is a linear
  smoother with hat matrix $A(\alpha)=(I+\alpha QR^{-1}Q^\top)^{-1}$, so item
  36 gives
  $$\mathop{\mathrm{CV}}(\alpha)
  =\frac1n\sum_{i=1}^n\left(\frac{Y_i-\hat g(t_i)}{1-A_{ii}(\alpha)}\right)^2.$$
  Suppose that $n$ is large, the design points have a smooth local density
  $f$, $s$ is away from the ends, and $\alpha$ is neither too small nor too
  large. Then $\hat g(s)=n^{-1}\sum_iY_iG(s,t_i)$, where the weight
  function satisfies the approximation
  $$G(s,t)\approx\frac1{f(t)h(t)}\,\kappa\Bigl(\frac{s-t}{h(t)}\Bigr),
  \qquad h(t)=\Bigl(\frac{\alpha}{nf(t)}\Bigr)^{1/4},$$
  $$\kappa(u)=\tfrac12e^{-|u|/\sqrt2}\sin\bigl(|u|/\sqrt2+\pi/4\bigr).$$
  The kernel $\kappa$ has Fourier transform $1/(1+\omega^4)$; it is a kernel
  of order four. The local bandwidth varies as the inverse fourth root of
  the design density.

A **kernel of order** $\ell\ge1$ is a function $K$ with $\int K=1$ and
$\int u^jK(u)\,du=0$ for $1\le j\le\ell$. For $\beta>0$, let $\ell$ be the
largest integer strictly smaller than $\beta$. The **Hölder density class**
$\mathcal P(\beta,L)$ is the set of probability densities on $\mathbb R$ that
are $\ell$ times differentiable with
$|f^{(\ell)}(x)-f^{(\ell)}(x')|\le L|x-x'|^{\beta-\ell}$.

* **39. Minimax rates of density estimation.** Let $K$ be a kernel of order
  $\ell$ with $\int K^2<\infty$ and $\int|u|^\beta|K(u)|\,du<\infty$, and let
  $h=c\,n^{-1/(2\beta+1)}$ for fixed $c>0$. Then
  $$\sup_{x_0\in\mathbb R}\ \sup_{f\in\mathcal P(\beta,L)}
  \mathbb E\bigl(\hat f_h(x_0)-f(x_0)\bigr)^2\le Cn^{-2\beta/(2\beta+1)},$$
  and no estimator achieves a faster order uniformly over
  $\mathcal P(\beta,L)$, either at a fixed point or in integrated squared
  error. For an integer $m\ge1$, let $\mathcal F_{m,M}$ be the class of
  densities with $m$ continuous derivatives and $\int(f^{(m)})^2\le M$.
  Kernels of order $m-1$ with $\int|y|^m|K(y)|\,dy<\infty$ and bandwidth
  $n^{-1/(2m+1)}$ give
  $$\sup_{f\in\mathcal F_{m,M}}\mathbb E\int(\hat f_h-f)^2
  \le C_{m,M}n^{-2m/(2m+1)}.$$
  Assouad's lemma, applied to $2^{r_n}$ local perturbations with
  $r_n\asymp n^{1/(2m+1)}$, gives a matching lower bound
  $D_{m,M}n^{-2m/(2m+1)}$ for every estimator. Kernels of order at least
  two are not nonnegative; the rate gain beyond $n^{-4/5}$ in item 4
  requires them.

### Risk bounds under shape constraints

* **40. Risk of isotonic regression.** Let $Y_i=\theta_i^*+\varepsilon_i$ for
  $i=1,\ldots,n$, with $\theta_1^*\le\cdots\le\theta_n^*$ and independent
  errors of mean zero and variance one. Let $\hat\theta$ be the
  isotonic least-squares estimator of item 25 with unit weights. There is a
  universal constant $C$ such that
  $$\frac1n\mathbb E\|\hat\theta-\theta^*\|^2
  \le C\left\{\Bigl(\frac{\theta_n^*-\theta_1^*}{n}\Bigr)^{2/3}
  +\frac{\log(en)}n\right\}.$$
  In particular the worst-case risk over sequences with
  $\|\theta^*\|_\infty\le1$ is of order $n^{-2/3}$, the minimax order for
  this class. For constant $\theta^*$ the risk is of the nearly parametric
  order $\log(en)/n$, without any tuning parameter.

Let $\mathcal F_d$ be the class of upper semicontinuous log-concave
densities on $\mathbb R^d$. The squared Hellinger distance is
$H^2(f,g)=\int(\sqrt f-\sqrt g)^2$.

* **41. Log-concave maximum likelihood.** Let $P$ be a probability measure on
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
  from $f_0\in\mathcal F_d$,
  $$\sup_{f_0\in\mathcal F_d}\mathbb E H^2(\hat f_n,f_0)\le C_d\cdot
  \begin{cases}n^{-4/5},&d=1,\\ n^{-2/(d+1)}\log n,&d\ge2,\end{cases}$$
  and no estimator improves on these orders apart from the logarithm.
  The estimator involves no smoothing parameter.

<a id="synopsis-104b"></a>

## 104B. Semiparametric Models and Missing Data

A **semiparametric model** is a family $\{P_{\theta,\eta}\}$ in which $\theta$
is a Euclidean parameter and the nuisance parameter $\eta$ ranges over an
infinite-dimensional set. A parametric submodel $t\mapsto P_{\theta,\eta_t}$
that varies only the nuisance parameter has a nuisance score. The
**nuisance tangent space** is the closed linear span of the nuisance scores
of smooth finite-dimensional submodels. The **efficient score** $\tilde\ell_\theta$
is the residual of the ordinary score for $\theta$ after orthogonal projection
onto that tangent space, and the **efficient information** is
$\tilde I(\theta)=\mathbb E[\tilde\ell_\theta\tilde\ell_\theta^\top]$.

* **14. Semiparametric convolution bound.** Assume local asymptotic normality
  of every regular finite-dimensional submodel, nonsingular efficient
  information, and the usual differentiability of the parameter along those
  submodels. Every regular estimator sequence of $\theta$ has a limit law
  equal to the convolution of $N(0,\tilde I(\theta)^{-1})$ with some
  probability measure on the parameter space. An estimator is asymptotically
  linear with influence function equal to $\tilde I(\theta)^{-1}\tilde\ell_\theta$
  if and only if it attains this bound. The ordinary parametric bound of
  SYNOPSIS103, item 11, is the case of a finite-dimensional nuisance
  parameter.

Let $Y$ be a response, let $X$ be covariates that are always observed, and
let $R$ indicate whether $Y$ is observed. The observations are independent
copies of $(R,X,RY)$. The response is **missing at random** when
$P(R=1\mid X,Y)=P(R=1\mid X)$. It is **missing completely at random** when
$R$ is independent of $(X,Y)$. Write $\pi(x)=P(R=1\mid X=x)$ and
$m(x)=\mathbb E[Y\mid R=1,X=x]$.

* **15. Ignorability.** Under missingness at random, the density of the
  observed data factors into a part that depends on the law of $(X,Y)$ and a
  part that depends on the missingness mechanism. If those two parameters
  are variation-independent, the maximizer of the observed-data likelihood
  for the law of $(X,Y)$ does not depend on the missingness parameter. The
  mechanism is then ignorable for likelihood inference.

For a complete-data density $f(x\mid\theta)$ and observed data $Y=t(X)$, the
**EM iteration** from $\theta'$ maximizes
$Q(\theta\mid\theta')=\mathbb E_{\theta'}[\log f(X\mid\theta)\mid Y]$ and
sets the next value equal to that maximizer.

* **16. Monotonicity of EM.** The observed-data log-likelihood at the new
  value is at least the observed-data log-likelihood at $\theta'$. A fixed
  point of a continuous EM map at which $Q$ has a unique maximizer is a
  stationary point of the observed-data likelihood.

* **17. Double robustness for a missing mean.** Under missingness at random
  and $\pi_0(X)\ge\delta>0$, the estimating function
  $$\varphi_{m,\pi}(R,X,Y)
  =\frac{RY}{\pi(X)}-\frac{R-\pi(X)}{\pi(X)}m(X)$$
  has expectation $\mathbb E Y$ as soon as either $\pi=\pi_0$, with $m$ any
  square-integrable function, or $m(x)=\mathbb E[Y\mid X=x]$, with $\pi$ any
  measurable function bounded away from zero. The estimator obtained by
  substituting estimators of $m$ and $\pi$ and taking the sample average is
  therefore consistent when at least one of the two fitted models is
  correct. If both are correct and converge quickly enough, the estimator
  is asymptotically linear with the efficient influence function for
  $\mathbb E Y$.

### Pathwise derivatives and orthogonal estimation

For a scalar parameter $\psi(P)$, let $\mathcal T\subset L^2_0(P)$ be the
closed tangent space of scores of differentiable submodels. The parameter
is **pathwise differentiable** if its derivative along every score $s$ is
$\dot\psi_P(s)=P(\phi s)$ for some $\phi\in L^2_0(P)$. The unique such
representative in $\mathcal T$ is the **canonical gradient**.

* **27. Canonical gradient and efficiency.** If a regular asymptotically
  linear estimator has influence function $\phi$, its projection onto
  $\mathcal T$ is the canonical gradient $\phi_{\mathrm{eff}}$. Hence
  $$P\phi^2=P\phi_{\mathrm{eff}}^2
  +P(\phi-\phi_{\mathrm{eff}})^2.$$
  The efficient variance bound is $P\phi_{\mathrm{eff}}^2$. In the
  unrestricted model, the mean has canonical gradient $x-PX$, and the
  $p$-quantile with positive density has gradient
  $(p-1_{\{x\le q_p\}})/f(q_p)$. A derivative that has no continuous
  $L^2$ representation precludes regular estimation at rate $\sqrt n$.

* **28. Cross-fitted estimation of a missing mean.** Use a fixed finite
  number of folds, evaluating the estimating function in item 17 on each
  fold with nuisance estimates trained on the other folds. Suppose
  $Y\in L^2$, the true and fitted response probabilities are bounded below
  by $\delta>0$, both nuisance estimates are $L^2$ consistent, and
  $$\|\hat m-m_0\|_2\,\|\hat\pi-\pi_0\|_2=o_P(n^{-1/2}).$$
  If the fitted estimating functions also converge in $L^2$ to the true
  one, then
  $$\sqrt n(\hat\mu-\mu)
  =n^{-1/2}\sum_{i=1}^n
  \left[m_0(X_i)+\frac{R_i(Y_i-m_0(X_i))}{\pi_0(X_i)}-\mu\right]+o_P(1).$$
  The variance is the efficient bound of item 27. Conditional second-moment
  bounds on $Y$ and bounded or suitably truncated regressions are useful
  sufficient conditions for the additional $L^2$ convergence. Sample
  splitting avoids requiring a Donsker class for the fitted nuisances.

* **29. Partially linear regression.** Suppose
  $Y=D^\top\beta+g(X)+\varepsilon$, $\mathbb E[\varepsilon\mid D,X]=0$,
  and $\mathbb E[\varepsilon^2\mid D,X]=\sigma^2\in(0,\infty)$. Write
  $V=D-\mathbb E[D\mid X]$ and assume $Q=\mathbb E[VV^\top]$ is positive
  definite. Then
  $$\beta=Q^{-1}\mathbb E[V(Y-\mathbb E[Y\mid X])].$$
  In the model imposing the conditional mean restriction, with conditional
  variance unrestricted away from the true law, the efficient influence
  function at this homoscedastic law is $Q^{-1}V\varepsilon$, with
  covariance $\sigma^2Q^{-1}$. Residualizing both $Y$ and $D$
  and fitting least squares attains this bound under consistent nuisance
  estimation and appropriate product-rate and moment conditions, using
  cross-fitting as in item 28.

### Adaptation, missing information, and multiple imputation

An estimator is **adaptive** in a semiparametric model if it attains, at
every law of the model, the information bound of the parametric submodel in
which the nuisance parameter is known. Adaptation requires that the score for
$\theta$ be orthogonal to the nuisance tangent space, so that the efficient
score of item 14 equals the ordinary score.

* **42. Adaptive estimation of a center of symmetry.** Let the observations
  have density $\eta(x-\theta)$, where $\eta$ ranges over all densities
  symmetric about zero that are absolutely continuous with finite Fisher
  information $I_\eta=\int(\eta'/\eta)^2\eta$. Nuisance scores are functions
  of $|x-\theta|$, while the location score $-(\eta'/\eta)(x-\theta)$ is odd
  about $\theta$. Thus the efficient score is the ordinary score and the
  efficient information is $I_\eta$. There are estimators $\hat\theta_n$, not
  depending on $\eta$, such that
  $$\sqrt n(\hat\theta_n-\theta)\Rightarrow N(0,I_\eta^{-1})$$
  regularly at every such $\eta$. One construction starts from a discretized
  $\sqrt n$-consistent location estimator. It then takes one Newton step
  on an estimated efficient score, formed from a truncated kernel estimate
  of $g'/g$ for the density $g$ of $|X_i-\theta|$, extended as an odd
  function of $x-\theta$. If $\eta$ is only required to have median zero,
  with a positive continuous density there, the information bound drops
  to $4\eta(0)^2$, the bound for the median in items 27 and 30.

For the EM iteration of item 16, let $\theta^*$ be an interior limit point
at which the observed-data likelihood is twice differentiable and
differentiation may be passed under the conditional expectations. Define
the **complete information** $i_{\mathrm{com}}=-D^{20}Q(\theta^*\mid\theta^*)$,
the **observed information** $i_{\mathrm{obs}}$ (minus the Hessian of the
observed-data log-likelihood at $\theta^*$), and the **missing
information** $i_{\mathrm{mis}}=i_{\mathrm{com}}-i_{\mathrm{obs}}$.

* **43. Missing information and the rate of EM.** The missing information is
  the conditional covariance of the complete-data score given the observed
  data, at $\theta^*$; hence $i_{\mathrm{mis}}$ is positive semidefinite. At a
  stationary point, Louis's formula reads
  $$i_{\mathrm{obs}}=i_{\mathrm{com}}
  -\mathbb E_{\theta^*}\bigl[S_c(\theta^*)S_c(\theta^*)^\top\bigm|Y_{\mathrm{obs}}\bigr],$$
  where $S_c$ is the complete-data score. If $i_{\mathrm{com}}$ and
  $i_{\mathrm{obs}}$ are positive definite and the EM map $M$ is
  differentiable at $\theta^*$, then
  $$DM(\theta^*)=i_{\mathrm{com}}^{-1}i_{\mathrm{mis}}
  =I-i_{\mathrm{com}}^{-1}i_{\mathrm{obs}}.$$
  Its eigenvalues, the **fractions of missing information**, lie in $[0,1)$.
  Iterates near $\theta^*$ converge linearly, with rate given by the
  largest eigenvalue. EM is slow exactly when some parameter combination
  is poorly informed by the observed data. Expanding the parameter space
  so as to lower the fraction of missing information accelerates the
  iteration.

Let $Y_{\mathrm{mis}}^{(1)},\ldots,Y_{\mathrm{mis}}^{(D)}$ be independent draws
from the posterior predictive law of the missing values given the observed
data. For a scalar estimand, let $\hat\theta_d$ and $V_d$ be the
complete-data posterior mean and variance computed from the $d$th completed
data set. Put
$\bar\theta=D^{-1}\sum_d\hat\theta_d$, $\bar V=D^{-1}\sum_dV_d$, and
$B=(D-1)^{-1}\sum_d(\hat\theta_d-\bar\theta)^2$.

* **44. Multiple-imputation combining rules.** The identities
  $$\mathbb E(\theta\mid Y_{\mathrm{obs}})
  =\mathbb E\bigl[\mathbb E(\theta\mid Y_{\mathrm{obs}},Y_{\mathrm{mis}})
  \bigm|Y_{\mathrm{obs}}\bigr],$$
  $$\mathop{\mathrm{Var}}(\theta\mid Y_{\mathrm{obs}})
  =\mathbb E\bigl[\mathop{\mathrm{Var}}(\theta\mid Y_{\mathrm{obs}},Y_{\mathrm{mis}})
  \bigm|Y_{\mathrm{obs}}\bigr]
  +\mathop{\mathrm{Var}}\bigl[\mathbb E(\theta\mid Y_{\mathrm{obs}},Y_{\mathrm{mis}})
  \bigm|Y_{\mathrm{obs}}\bigr]$$
  are approximated by $\bar\theta$ and by the total variance
  $T=\bar V+(1+D^{-1})B$. The factor $1+D^{-1}$ accounts for the finite
  number of imputations. Rubin's rules use a $t$ reference distribution for
  $(\theta-\bar\theta)/\sqrt T$ with
  $$\nu=(D-1)\Bigl(1+\frac{D\bar V}{(D+1)B}\Bigr)^2$$
  degrees of freedom. The ratio $(1+D^{-1})B/T$ estimates the fraction of
  missing information of item 43. For a vector estimand the squared
  deviations are replaced by outer products. The rules approximate a
  posterior from a model in which imputer and analyst agree. Frequentist
  validity has been shown for several imputation methods under
  missingness at random. When the imputation model and the analysis model
  are incompatible, the resulting intervals are usually, but not always,
  conservative.

<a id="synopsis-104c"></a>

## 104C. Robust Statistics

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

* **18. M-estimators and the Huber minimax property.** An $M$-functional of
  location defined by $\int\psi(x-\theta)\,dF(x)=0$, with $\psi$ odd and
  $\int\psi'\,dF\neq0$, has influence function
  $\psi(x-\theta)/\int\psi'\,dF$. For a location sample its estimator is
  asymptotically normal with variance
  $\mathbb E\psi(X-\theta)^2/(\mathbb E\psi'(X-\theta))^2$, under the
  standard Lipschitz and nondegeneracy conditions of SYNOPSIS103, item 4.
  Among Fisher-consistent location functionals whose gross-error sensitivity
  at the standard normal law is at most a prescribed bound, the asymptotic
  variance at that law is minimized by Huber's clipped score
  $\psi_k(u)=\max(-k,\min(k,u))$ for a clip $k$ determined by the bound.
  The same score is minimax for asymptotic variance over
  $\varepsilon$-contamination neighborhoods of the normal law.

* **19. Breakdown points.** The sample mean has replacement breakdown
  point $1/n$ at a sample of size $n$, tending to zero as $n\to\infty$. The
  sample median of a one-dimensional sample of size $n=2m+1$ has breakdown
  point $(m+1)/n$, which tends to $1/2$. Ordinary least squares has
  breakdown point $1/n$. The least-median-of-squares regression estimator
  has breakdown point that tends to $1/2$ as $n\to\infty$ with the number of
  covariates fixed.

* **30. Influence of a median and a contamination bound.** If $F$ has
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
  Extreme contaminating distributions approach these bounds. Bounded
  local influence and a positive breakdown point describe different
  aspects of robustness.

### Von Mises expansions and regression $M$-estimators

* **45. Influence function and asymptotic variance.** Let $T$ be defined on
  distribution functions on $\mathbb R$. Suppose $T$ is Hadamard
  differentiable at $F$ for the supremum norm, with a derivative $T_F'$ that
  is a continuous linear map on all bounded functions. Then the influence
  function is $\mathop{\mathrm{IF}}(x;T,F)=T_F'(1_{[x,\infty)}-F)$, it has mean
  zero under $F$, and, by SYNOPSIS103, item 26, and linearity of $T_F'$,
  $$\sqrt n\bigl(T(F_n)-T(F)\bigr)
  =\frac1{\sqrt n}\sum_{i=1}^n\mathop{\mathrm{IF}}(X_i;T,F)+o_P(1)
  \Rightarrow N\Bigl(0,\int\mathop{\mathrm{IF}}(x;T,F)^2\,dF(x)\Bigr),$$
  provided the second moment is finite. If $T$ is differentiable only
  tangentially to a subspace carrying the limit $B^0\circ F$, as for
  quantiles, the limit is still the centered normal law
  $T_F'(B^0\circ F)$. In the usual examples its variance is again the
  second moment of the influence function computed as a directional
  derivative. The asymptotic variance of a
  plug-in estimator is thus the second moment of its influence function.
  Its gross-error sensitivity, the supremum of $|\mathop{\mathrm{IF}}|$,
  bounds to first order the asymptotic bias caused by a small fraction
  $\varepsilon$ of contamination, at $\varepsilon$ times that supremum. Items 18 and 30 are instances. When
  Hadamard differentiability fails, the same expansion is a heuristic for
  the limit law, to be confirmed by direct arguments.

Consider the linear model $Y_i=x_i^\top\beta+\varepsilon_i$ with fixed design
rows $x_i\in\mathbb R^p$, the first coordinate equal to one, and independent
errors with distribution function $F$. A **regression $M$-estimator** with
score $\psi=\rho'$ minimizes $\sum_i\rho(Y_i-x_i^\top t)$; its studentized
version minimizes $\sum_i\rho\bigl((Y_i-x_i^\top t)/S_n\bigr)$ for a
regression-invariant, scale-equivariant scale statistic $S_n$.

* **46. Asymptotics of regression $M$-estimators.** Assume that
  $n^{-1}\sum_ix_ix_i^\top\to Q$ positive definite, with the moment bounds
  on the rows used by Jurečková and Sen. Assume also that
  $t\mapsto\int\rho(z-t)\,dF(z)$ has a unique minimum at $0$, so that
  $\mathbb E\psi(\varepsilon)=0$. Let $\psi$ be decomposable into smooth,
  piecewise linear, and monotone step parts, with the matching smoothness
  of $F$ near the kinks and jumps of $\psi$. Let
  $\gamma=-\frac d{dt}\mathbb E\psi(\varepsilon-t)\big|_{t=0}\neq0$. Then a
  $\sqrt n$-consistent $M$-estimator satisfies
  $$\sqrt n(\hat\beta_n-\beta)
  =\frac{Q^{-1}}{\gamma\sqrt n}\sum_{i=1}^nx_i\psi(\varepsilon_i)+o_P(1)
  \Rightarrow N\Bigl(0,\frac{\mathbb E\psi(\varepsilon)^2}{\gamma^2}Q^{-1}\Bigr).$$
  The scalar factor is the location variance of item 18. With a scale
  statistic $S_n$ satisfying $\sqrt n(S_n-S)=O_P(1)$, the same holds with
  $\psi(\cdot/S)$ in place of $\psi$, except for an additional term in the
  intercept proportional to $S_n/S-1$. The slope coordinates are
  unaffected by studentization. Least squares is the case $\psi(u)=u$.
  Bounded $\psi$ limits the influence of large residuals but not of
  high-leverage design points. When whole pairs $(x_i,Y_i)$ may be replaced,
  the least-absolute-deviation and other $M$-estimators of regression have
  breakdown point $1/n$, in contrast with the least-median-of-squares
  estimator of item 19.

<a id="synopsis-104d"></a>

## 104D. Functional Data Analysis

Let $X$ be a random element of a separable Hilbert space $H$ with
$\mathbb E\|X\|^2<\infty$, mean $\mu$, and covariance operator
$C=\mathbb E[(X-\mu)\otimes(X-\mu)]$. Then $C$ is compact, self-adjoint,
nonnegative, and trace-class. Its eigenvalues and orthonormal eigenfunctions
are $(\lambda_j,\varphi_j)$.

* **20. Karhunen–Loève expansion and the Hilbertian central limit theorem.**
  For each positive eigenvalue, set
  $\xi_j=\langle X-\mu,\varphi_j\rangle/\sqrt{\lambda_j}$.
  These variables are uncorrelated with mean $0$ and variance $1$, and
  $$X=\mu+\sum_{j\ge1}\sqrt{\lambda_j}\,\xi_j\varphi_j,$$
  where only positive eigenvalues are included, with convergence in $L^2$
  and almost surely in $H$. For independent copies,
  $\sqrt n\,(\bar X_n-\mu)$ converges in law in $H$ to the centered Gaussian
  random element with covariance operator $C$.

* **21. Principal components of the empirical covariance.** Let $\hat C_n$ be
  the empirical covariance and let $\hat\lambda_j$ and $\hat\varphi_j$ be its
  eigenvalues and eigenfunctions. If $\lambda_j$ is simple and positive and
  $\mathbb E\|X\|^4<\infty$, then
  $$\sqrt n\,(\hat\lambda_j-\lambda_j)
  \Rightarrow N\bigl(0,\mathop{\mathrm{Var}}(\langle X-\mu,\varphi_j\rangle^2)\bigr).$$
  For a Gaussian $X$ the asymptotic variance equals $2\lambda_j^2$. The
  empirical eigenfunction, multiplied by a sign so that
  $\langle\hat\varphi_j,\varphi_j\rangle\ge0$, satisfies
  $\|\hat\varphi_j-\varphi_j\|=O_P(n^{-1/2}/\delta_j)$, where
  $\delta_j$ is the distance from $\lambda_j$ to the rest of the spectrum.
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
  $\lambda_k>\lambda_{k+1}$, that subspace is unique. This reconstruction
  characterization does not require Gaussian observations.

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

* **47. Prediction rates in functional linear regression.** Assume
  $V_k=O(k^{-\alpha})$ for some $\alpha>0$. Assume also a fourth-moment
  condition on the principal-component scores $Z_j=\langle X,\varphi_j\rangle$:
  $\mathop{\mathrm{Var}}(Z_jZ_k)\le c\,\lambda_j\lambda_k$ for all $j,k$ and
  a constant $c$. With
  $\eta=n^{-(2q+\alpha+1)/(2q+\alpha+2)}$, the prediction error for an
  independent new $X$ satisfies
  $$\mathbb E_{\varepsilon,X}\bigl(\langle X,\hat\beta_\eta\rangle
  -\langle X,\beta\rangle\bigr)^2
  =O_P\bigl(n^{-(2q+\alpha+1)/(2q+\alpha+2)}+n^{-(\alpha+1)/2}\bigr).$$
  For $\alpha\ge1$, the first term dominates. Over models with
  $\|\beta\|_{W_q}\le1$ and $V_k\le k^{-\alpha}$, no estimator has a
  smaller order of worst-case prediction risk, so the penalized estimator is
  rate optimal. For Brownian-motion covariates, $\lambda_j=4/((2j-1)\pi)^2$,
  $\alpha=1$, and the rate is $n^{-(2q+2)/(2q+3)}$. The rate concerns the
  prediction functional $\langle X,\beta\rangle$. Recovering $\beta$ itself
  in $L^2$ is an ill-posed inverse problem, because the covariance operator
  has an unbounded inverse on its range.

## Reference guide

### Correspondence with the subdivisions

- **[104A](#synopsis-104a)**: Wand and Jones, Fan and Gijbels, Wahba,
  Groeneboom and Jongbloed, Johnstone's Gaussian-sequence draft, the
  wavelet monograph of Härdle, Kerkyacharian, Picard, and Tsybakov, and
  Ingster and Suslina carry the smoothing expansions, the representer
  theorem, shape-constrained limits, and the sequence-model minimax theory.
  Rank asymptotics are the subject of Hájek, Šidák, and Sen, and of
  van der Vaart, Chapters 13–15. Samworth and Shah give the finite-sample
  shape-constrained risk bounds.
- **[104B](#synopsis-104b)**: Bickel, Klaassen, Ritov, and Wellner, Kosorok,
  Little and Rubin, and van der Laan and Robins carry efficiency bounds,
  ignorability, EM, and double robustness.
- **[104C](#synopsis-104c)**: Jurečková and Sen develop the asymptotics of
  $M$-estimators. Huber and Ronchetti, and Hampel, Ronchetti, Rousseeuw,
  and Stahel, are the organizing monographs for influence functions and
  breakdown.
- **[104D](#synopsis-104d)**: Hsing and Eubank develop the Hilbert-space
  geometry, the covariance operator, and the asymptotics of functional
  principal components.

### Source comparisons and local copies

Hollander, Wolfe, and Chicken, Chapters 3, 4, and 6, provide the exact
sign and rank procedures and the several-sample comparison added here.
Robertson, Wright, and Dykstra, Section 1.2 and the max–min formulas of
Section 1.4, give the cumulative-sum and pooling descriptions of isotonic
regression. Wand–Jones and Fan–Gijbels supply the bias expansions; the
bandwidth conditions now ensure that replacing the exact bias by its
leading term is legitimate in the normal limit. Tsybakov's full text is
available in `ReferencesSuppl`; its regression upper and lower bound
chapters were consulted, including the supremum-norm comparison in
Corollary 2.5. Item 26 records the corresponding dimension-dependent
Hölder rates. Hsing–Eubank, Chapters 1 and 9, supplies the reconstruction
interpretation and the spectral perturbation framework.

Items 27–29 make the semiparametric geometry operational: representing
derivatives in $L^2$, projecting out nuisance regressions, and controlling
the product remainder after sample splitting. They give explicit
conditions for the efficiency claims in items 14 and 17, rather than
treating consistency of fitted nuisances alone as sufficient for a
central limit theorem.

The kernel expansions of items 4 and 6 are the interior-point formulae of
Wand and Jones and of Fan and Gijbels. Item 8 is the Kimeldorf–Wahba
representer theorem, as used throughout Wahba's spline monograph. Items 9
and 10 follow Johnstone's chapters on Pinsker's theorem and on thresholding.
Item 11 is the pointwise limit in Groeneboom and Jongbloed. Item 13 is the
Sobolev detection boundary of Ingster and Suslina. Item 12 is the cone
mixture of Robertson, Wright, and Dykstra.

Lehmann's *Nonparametrics*, Silverman's density monograph, and the
Györfi, Kohler, Krzyżak, and Walk distribution-free regression monograph
were not located in the local reference directories. Hájek, Šidák, and Sen is present as a DjVu file
and was not text-extracted. Huber and Ronchetti, and Hampel, Ronchetti,
Rousseeuw, and Stahel, are also absent locally; items 18 and 19 are the
forms used by Jurečková and Sen and by the robust chapters of the general
inference texts. Tsiatis's missing-data monograph is absent locally; item 17
is the augmented inverse-probability function of that book and of van der
Laan and Robins.

Items 32–47 were added from the following passages. The rank items 32–35
follow van der Vaart, Theorem 13.5, Section 13.3 and Examples 13.13–13.22,
Corollary 15.10 and Example 15.15, Table 14.2 with Problem
14.8, Examples 12.5 and 12.13, and Corollary 19.21 and Theorem 19.23. The
exact null moments of Kendall's and Spearman's statistics and the two-sample
Kolmogorov–Smirnov limit are those of Hollander, Wolfe, and Chicken, Sections
5.4, 8.1, and 8.5; the Chernoff–Savage bound is quoted there. Item 36 follows
Tsybakov, Proposition 1.9, Wasserman, Theorems 5.34, 6.34, and 6.37, and
Wand–Jones, Section 3.8. Item 37 is Fan–Gijbels, Theorems 3.1 and 3.2 with
Sections 3.2.2 and 3.3. Item 38 is Green–Silverman, Theorems 2.4 and 3.1 and
Section 3.7, on Silverman's equivalent kernel; Tsybakov, Section 1.3,
supplies its Fourier transform. Item 39 combines Tsybakov, Theorem 1.1 and
Exercises 2.8 and 2.10, with van der Vaart, Theorems 24.2 and 24.4. Items
40 and 41 are Samworth and Shah, Theorems 9.39, 9.15, and 9.26, with the
tent-function description of Section 9.2. Item 42 is van der Vaart, Example
25.27 and Section 25.8.1. Items 43 and 44 are Little and Rubin, Sections
8.4.3 and 10.2, including equations (8.27)–(8.30) and (10.13)–(10.15).
Item 45 follows van der Vaart, Section 20.1. Item 46 is Jurečková and Sen,
Theorems 5.5.1–5.5.3, with the breakdown remarks of their Section 4.8. Item 47 is
Hsing and Eubank, Theorems 11.2.7 and 11.3.1. Hampel's general optimal
bounded-influence estimator is not stated, because the Hampel–Ronchetti–
Rousseeuw–Stahel monograph is not available locally. Item 18 records its
location case.

Local texts directly consulted for this selection:

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
- [Bickel, Klaassen, Ritov, and Wellner, *Efficient and Adaptive Estimation for Semiparametric Models*](../lean-CKMA/References/BickelKlaassenRitovWellner1993EfficientAdaptiveEstimationSemiparametricModels-JohnsHopkins.MathSci.pdf).
- [Kosorok, *Introduction to Empirical Processes and Semiparametric Inference*](../lean-CKMA/References/Kosorok2008IntroductionEmpiricalProcessesSemiparametricInference-Springer.SSS.pdf).
- [Little and Rubin, *Statistical Analysis with Missing Data*](../lean-CKMA/References/LittleRubin2020StatisticalAnalysisMissingData3rdEd-Wiley.SerProbStat.pdf).
- [van der Laan and Robins, *Unified Methods for Censored Longitudinal Data and Causality*](../lean-CKMA/References/VanDerLaanRobins2003UnifiedMethodsCensoredLongitudinalDataCausality-Springer.SSS.pdf).
- [Jurečková and Sen, *Robust Statistical Procedures*](../lean-CKMA/References/JurečkováSen1996RobustStatisticalProceduresAsymptoticsInterrelations-Wiley.SerProbStat.pdf).
- [Hsing and Eubank, *Theoretical Foundations of Functional Data Analysis*](../lean-CKMA/References/HsingEubank2015TheoreticalFoundationsFunctionalDataAnalysisIntroductionLinearOperators-Wiley.SerProbStat.pdf).
- [Hájek, Šidák, and Sen, *Theory of Rank Tests*](../lean-CKMA/References/HájekŠidákSen1999TheoryRankTests2ndEd-AcademicPress.djvu).
- [van der Vaart, *Asymptotic Statistics*](../lean-CKMA/References/VanDerVaart1998AsymptoticStatistics-CambridgeSerStatProbMath03.pdf).
- [Wasserman, *All of Nonparametric Statistics*](../lean-CKMA/ReferencesSuppl/Wasserman2006NonparametricStatistics-SpringerSTS.pdf).
- [Green and Silverman, *Nonparametric Regression and Generalized Linear Models*](../lean-CKMA/References/GreenSilverman1994NonparametricRegressionGeneralizedLinearModelsRoughnessPenaltyApproach-ChapmanHall.MSAP58.pdf).
- [Samworth and Shah, *Modern Statistical Methods and Theory*](../lean-CKMA/References/SamworthShah2026ModernStatisticalMethodsTheoryIntroductionNonparametricHighDimensionalStatistics-Cambridge.SerStatProbMat.pdf).
