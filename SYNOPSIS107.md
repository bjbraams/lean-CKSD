# Synopsis: High-dimensional statistics and statistical learning

Part of the [mathematical synopsis series](SYNOPSIS.md).
[Bibliographical scope and references](CKSD-bib.md#cks-107).

This synopsis follows Section 107. Subdivision 107A is sparsity, minimax
lower bounds, sparse recovery, model selection, multiple testing,
low-rank and graphical-model estimation, and high-dimensional covariance
and principal components. Subdivision 107B is uniform convergence,
margins and surrogate losses, stability, kernels, nearest neighbours,
online prediction, and conformal prediction. Soft thresholding is
[SYNOPSIS104](SYNOPSIS104.md), item 10.
The Sauer–Shelah bound, uniform deviations for VC classes, covariance
estimation, the restricted isometry property, the Marchenko–Pastur law, and
the Tracy–Widom law of the Gaussian unitary ensemble are
[CKMA SYNOPSIS07](../lean-CKMA/SYNOPSIS07.md), items 35, 37, 46, 48, 51, and
69. The representer theorem is SYNOPSIS104, item 8. Bonferroni's method is
[SYNOPSIS102](SYNOPSIS102.md), item 15.

Numbered definitions and results have stable identifiers. Additions take the
next free number and are placed beside related material; numbers need not
increase in reading order. Proofs are outside the scope of this synopsis.

<a id="synopsis-107a"></a>

## 107A. High-Dimensional and Large-Scale Inference

In the Gaussian sequence model, one observes $Y=\theta+\sigma\xi$ in
$\mathbb R^p$, with $\xi$ standard normal.

* **1. Sparse minimax rate.** Over the class of vectors with at most $s$
  nonzero coordinates, $1\le s\le p/2$, the minimax mean squared error is of
  order $\sigma^2 s\log(p/s)$. When $s$ is known, soft thresholding
  at a level of order $\sigma\sqrt{\log(p/s)}$ attains this order.
  The universal threshold $\sigma\sqrt{2\log p}$ instead gives the
  bound of order $\sigma^2s\log p$ from SYNOPSIS104, item 10; it is
  rate optimal when $\log(p/s)$ is comparable to $\log p$.

Let $Y=X\beta+\varepsilon$ with $X$ an $n\times p$ design and with
$\varepsilon\in\mathbb R^n$. The **lasso** is any minimizer
$$\hat\beta\in\mathop{\mathrm{argmin}}_{\beta\in\mathbb R^p}
\Bigl(\frac1{2n}\|Y-X\beta\|_2^2+\lambda\|\beta\|_1\Bigr).$$
For an index set $S$ and a stretching factor $L>0$, the **compatibility
constant** is
$$\kappa^2(S,L)=\inf\Bigl\{
\frac{|S|\,\|X\delta\|_2^2}{n\|\delta_S\|_1^2}:
\delta\neq0,\;\|\delta_{S^c}\|_1\le L\|\delta_S\|_1\Bigr\}.$$

* **2. Lasso under compatibility.** Suppose $\beta$ is supported on $S$ and
  $$\lambda\ge\frac2n\|X^\top\varepsilon\|_\infty.$$
  If $\kappa(S,3)>0$, then every lasso solution satisfies
  $$\frac1n\|X(\hat\beta-\beta)\|_2^2
  \le\frac{9\lambda^2|S|}{4\kappa^2(S,3)}$$
  and
  $$\|\hat\beta-\beta\|_1\le\frac{6\lambda|S|}{\kappa^2(S,3)}.$$
  The error $\hat\beta-\beta$ lies in the cone
  $\|\delta_{S^c}\|_1\le3\|\delta_S\|_1$. A restricted-eigenvalue lower bound
  on $\|X\delta\|_2/(\sqrt n\,\|\delta\|_2)$ over that cone gives an $\ell^2$
  estimation bound of order $\lambda\sqrt{|S|}$. For a design with
  independent centered sub-Gaussian entries, the restricted isometry property
  of CKMA SYNOPSIS07, item 48, supplies such a bound with high probability
  once $n$ is at least a constant multiple of $|S|\log(ep/|S|)$. If the
  columns satisfy $\|X_{\cdot j}\|_2^2/n\le1$ and the errors are
  $N(0,\sigma^2)$, a choice of $\lambda$ of order $\sigma\sqrt{(\log p)/n}$
  meets the noise condition with high probability.

Let $(S_m)$ be a countable collection of linear subspaces of the regression
space, of dimensions $d_m$, and let $\hat f_m$ be the orthogonal projection
of $Y$ onto $S_m$. Write $\|\cdot\|_n$ for the norm
$\|v\|_n^2=n^{-1}\|v\|_2^2$.

* **3. Penalized model selection.** In the Gaussian regression model with
  error variance $\sigma^2$, let $(\pi_m)$ be positive weights with
  $\sum_m\pi_m\le1$. For a sufficiently large universal constant
  $\kappa$, take
  $$\mathop{\mathrm{pen}}(m)\ge\kappa\frac{\sigma^2}n\bigl(d_m+\log(1/\pi_m)\bigr).$$
  The penalized selector $\hat m$ minimizing
  $\|Y-\hat f_m\|_n^2+\mathop{\mathrm{pen}}(m)$ obeys
  $$\mathbb E\|\hat f_{\hat m}-f\|_n^2
  \le C(\kappa)\inf_m\Bigl(
  \inf_{g\in S_m}\|g-f\|_n^2+\mathop{\mathrm{pen}}(m)\Bigr),$$
  where the constant $C(\kappa)$ depends only on $\kappa$.

* **4. AIC and BIC.** In a regular parametric model of dimension $k$ that
  contains the true distribution, compare the maximized training
  log-likelihood with the log-likelihood of an independent sample of the
  same size, evaluated at the training estimate. Under the regularity and
  moment conditions for taking expectations of the likelihood expansion,
  the expected training excess is $k+o(1)$.
  Akaike's criterion $-2\ell_n(\hat\theta)+2k$ corrects
  the maximized log-likelihood by this optimism. In a finite nested list of
  regular models of fixed dimension, one of which is the smallest model
  containing the truth, the probability that the Akaike selector returns a
  strictly larger model stays positive as $n\to\infty$. The Bayes information
  criterion of SYNOPSIS105, item 5, $-2\ell_n(\hat\theta)+k\log n$, selects
  that smallest true model with probability tending to one.

Let $p_{(1)}\le\cdots\le p_{(m)}$ be ordered $p$-values for $m$ hypotheses,
of which $m_0$ are true nulls, each with a valid $p$-value, and let $V$ and $R$ be the numbers of false
and of all rejections.

* **5. Benjamini–Hochberg procedure.** Fix $\alpha\in(0,1)$ and let
  $k=\max\{i:p_{(i)}\le i\alpha/m\}$, with $k=0$ when the set is empty. Reject
  the hypotheses attached to $p_{(1)},\ldots,p_{(k)}$. If the null $p$-values
  are independent of each other and of the non-null $p$-values, or if the
  vector of $p$-values is positively regression dependent on the subset of
  null coordinates, then the false-discovery rate satisfies
  $$\mathbb E\Bigl[\frac{V}{\max(R,1)}\Bigr]\le\alpha\frac{m_0}m\le\alpha.$$

Let $X$ be an $n\times p$ matrix with independent standard normal entries, and
let $\ell_{\max}$ be the largest eigenvalue of the sample covariance
$n^{-1}X^\top X$. Write $y$ for a limit of $p/n$ in $(0,\infty)$.

* **6. Tracy–Widom law and spiked covariance.** As $n,p\to\infty$ with
  $p/n\to y$,
  $$\frac{\ell_{\max}-\mu_{n,p}}{\sigma_{n,p}}\Rightarrow F_1,$$
  where $F_1$ is the Tracy–Widom law of the Gaussian orthogonal ensemble,
  $$\mu_{n,p}=\frac{\bigl(\sqrt{n-1}+\sqrt p\bigr)^2}n,$$
  and
  $$\sigma_{n,p}
  =\frac{\bigl(\sqrt{n-1}+\sqrt p\bigr)
  \bigl((n-1)^{-1/2}+p^{-1/2}\bigr)^{1/3}}n.$$
  The bulk of the spectrum converges to the Marchenko–Pastur law on
  $[(1-\sqrt y)^2,(1+\sqrt y)^2]$, by CKMA SYNOPSIS07, item 51. The edge law
  $F_2$ of the Gaussian unitary ensemble is CKMA SYNOPSIS07, item 69. In
  Johnstone's spiked model, the population covariance has one eigenvalue
  $\alpha$ and the remaining eigenvalues equal to $1$. The corresponding
  sample eigenvalue converges almost surely to $(1+\sqrt y)^2$ when
  $1<\alpha\le1+\sqrt y$, and to $\alpha+y\alpha/(\alpha-1)$ when
  $\alpha>1+\sqrt y$.

### Lower bounds, regularization, and multiplicity

* **14. Le Cam's two-point method.** If two parameters are at metric
  distance at least $2s$, then every estimator satisfies
  $$\max_{j=0,1}P_j(d(\hat\theta,\theta_j)\ge s)
  \ge\tfrac12(1-\|P_0-P_1\|_{\mathrm{TV}}).$$
  For any nonnegative increasing loss $\ell$, this gives a minimax risk
  lower bound $\ell(s)(1-\|P_0-P_1\|_{\mathrm{TV}})/2$.
  The probabilities here are the full observation laws; for $n$
  independent observations the KL divergence used to bound total
  variation is $n$ times the one-observation divergence.

* **15. Fano's method.** Let $\theta_1,\ldots,\theta_M$ be $2s$-separated,
  $M\ge2$, with observation laws $P_j$. For a uniform index $J$ and
  data $X\mid J=j\sim P_j$, every estimator satisfies
  $$\sup_jP_j(d(\hat\theta,\theta_j)\ge s)
  \ge1-\frac{I(J;X)+\log2}{\log M}.$$
  With $\bar P=M^{-1}\sum_jP_j$,
  $$I(J;X)=\frac1M\sum_jD(P_j\|\bar P)
  \le\frac1M\sum_jD(P_j\|Q)$$
  for any reference law $Q$ for which the right side is finite.
  Large packings with small divergences yield the sparse rate of item 1
  and the nonparametric rates in SYNOPSIS104, item 26.

* **16. Lasso without a restricted eigenvalue.** Under the noise event
  of item 2, the basic inequality gives
  $$\frac1n\|X(\hat\beta-\beta)\|^2\le3\lambda\|\beta\|_1.$$
  This prediction bound does not require sparsity or compatibility.
  Compatibility converts the basic inequality into the faster
  $s\lambda^2$ rate of item 2. Small prediction error alone need not
  imply small coefficient error when the design has nearly dependent
  columns.

* **17. Orthogonal designs and soft thresholding.** If
  $X^\top X/n=I_p$, the lasso solution is
  $$\hat\beta_j=\mathop{\mathrm{sign}}(z_j)(|z_j|-\lambda)_+,
  \qquad z=X^\top Y/n.$$
  Ridge instead multiplies $z$ by $n/(n+\lambda)$ for the penalty
  convention of SYNOPSIS106, item 22. The coordinate calculation connects
  sparse regression to Gaussian sequence estimation; correlated designs
  require the cone conditions in item 2.

* **18. Debiased linear estimation.** In the Gaussian linear model let
  $\hat\Theta$ depend on $X$ and define
  $$\tilde\beta=\hat\beta+
  \hat\Theta X^\top(Y-X\hat\beta)/n.$$
  Then the exact decomposition is
  $$\sqrt n(\tilde\beta-\beta)
  =\hat\Theta X^\top\varepsilon/\sqrt n
  +\sqrt n(I-\hat\Theta\hat\Sigma)(\hat\beta-\beta),
  \qquad\hat\Sigma=X^\top X/n.$$
  If $\|\hat\Theta\hat\Sigma-I\|_{\max}
  \|\hat\beta-\beta\|_1=o_P(n^{-1/2})$, each remainder coordinate
  vanishes. Conditionally on $X$, the leading term is Gaussian with
  covariance $\sigma^2\hat\Theta\hat\Sigma\hat\Theta^\top$.
  Consistent variance estimates and variances bounded away from zero
  yield asymptotic coordinate confidence intervals. Suitable sparse
  designs often reduce the remainder condition to $s\log p=o(\sqrt n)$.

* **19. False-discovery control under arbitrary dependence.** Let
  $H_m=\sum_{j=1}^m1/j$. Replacing the Benjamini–Hochberg thresholds in
  item 5 by $i\alpha/(mH_m)$ controls the false-discovery rate at most
  $\alpha m_0/m$ for any joint distribution of valid null $p$-values.
  This is the Benjamini–Yekutieli correction. Family-wise error control
  under arbitrary dependence is SYNOPSIS102, items 23 and 24.

### Packings and hypercube lower bounds

Write $\rho(\omega,\omega')=\sum_{j=1}^m1_{\{\omega_j\ne\omega'_j\}}$ for the
**Hamming distance** on the hypercube $\Omega=\{0,1\}^m$.

* **22. Varshamov–Gilbert bound.** If $m\ge8$, there are points
  $\omega^{(0)},\ldots,\omega^{(M)}$ of $\{0,1\}^m$ with
  $\omega^{(0)}=(0,\ldots,0)$,
  $$\rho(\omega^{(j)},\omega^{(k)})\ge\frac m8
  \quad(0\le j<k\le M),\qquad M\ge2^{m/8}.$$
  Thus the hypercube contains exponentially many points at pairwise
  distance proportional to $m$. Indexing parameters by such points
  supplies the large separated families required in Fano's method,
  item 15.

* **23. Assouad's lemma.** Let $(P_\omega)_{\omega\in\Omega}$ be $2^m$
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
  two-point problems of the kind in item 14.

Let $Y=X\beta+\varepsilon$ with $\varepsilon\sim N(0,\sigma^2I_n)$ and a fixed
$n\times p$ design. For an integer $D_{\max}\le p/5$ let
$\underline c_X$ and $\overline c_X$ be the infimum and supremum of
$\|X\beta\|_2/\|\beta\|_2$ over nonzero $\beta$ with at most $2D_{\max}$
nonzero coordinates, and let
$V_D(X)=\{X\beta:\beta\text{ has exactly }D\text{ nonzero coordinates}\}$.

* **24. Minimax risk of sparse regression.** For $1\le D\le D_{\max}$,
  $$\inf_{\hat f}\sup_{f\in V_D(X)}E_f\|\hat f-f\|_2^2
  \ge\frac e{4(2e+1)^2}\Bigl(\frac{\underline c_X}{\overline c_X}\Bigr)^2
  D\log\Bigl(\frac p{5D}\Bigr)\sigma^2,$$
  the infimum running over all estimators. Penalized model selection over
  all coordinate subsets, item 3 with weights decreasing in the subset
  size, attains the order $D\log(p/D)\sigma^2$. When the restricted
  isometry ratio stays bounded away from zero, the sparse rate of item 1
  is therefore the minimax prediction rate in the regression model as well.

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

* **25. Restricted nullspace and exact recovery.** The following are
  equivalent: for every $\beta$ supported in $S$, basis pursuit with
  $y=X\beta$ has the unique solution $\beta$; and $X$ has the restricted
  nullspace property with respect to $S$. If
  $\delta_{2s}(n^{-1/2}X)<1/3$, the restricted nullspace property holds for
  every $S$ with $|S|\le s$, so every $s$-sparse vector is recovered from
  its noiseless measurements. By CKMA SYNOPSIS07, item 48, this holds with
  high probability for independent centered unit-variance sub-Gaussian
  entries once $n\ge Cs\log(ep/s)$.

Write $\sigma_s(\beta)_1=\min\{\|\beta-b\|_1:b\text{ has at most }s
\text{ nonzero coordinates}\}$ for the $\ell^1$ error of best $s$-term
approximation.

* **26. Stable recovery under restricted isometry.** Let $A$ be an
  $n\times p$ matrix with
  $$\delta_{2s}(A)<\frac4{\sqrt{41}}\approx0.6246.$$
  For every $\beta\in\mathbb R^p$ and $y$ with $\|A\beta-y\|_2\le\eta$, every
  minimizer $\beta^\sharp$ of $\|b\|_1$ subject to $\|Ab-y\|_2\le\eta$
  satisfies
  $$\|\beta^\sharp-\beta\|_1\le C\sigma_s(\beta)_1+D\sqrt s\,\eta,
  \qquad
  \|\beta^\sharp-\beta\|_2\le\frac C{\sqrt s}\sigma_s(\beta)_1+D\eta,$$
  with constants $C,D$ depending only on $\delta_{2s}(A)$. The guarantee
  is uniform over all signals, degrades gracefully for approximately sparse
  vectors, and reduces to exact recovery when $\eta=0$ and $\beta$ is
  $s$-sparse.

In the setting of item 2, the design satisfies the **restricted eigenvalue
condition** over $S$ with constants $(\kappa,L)$, $\kappa>0$, if
$n^{-1}\|X\delta\|_2^2\ge\kappa\|\delta\|_2^2$ for every
$\delta\in\mathcal C_L(S)$.

* **27. Lasso error in Euclidean norm.** Let $\beta$ be supported on $S$
  with $|S|=s$, let the restricted eigenvalue condition hold over $S$ with
  constants $(\kappa,3)$, and let
  $\lambda\ge2n^{-1}\|X^\top\varepsilon\|_\infty$. Then every lasso
  solution satisfies
  $$\|\hat\beta-\beta\|_2\le\frac{3\sqrt s\,\lambda}\kappa.$$
  The restricted eigenvalue condition with constants $(\kappa,3)$ implies
  $\kappa^2(S,3)\ge\kappa$ in item 2, since
  $\|\delta_S\|_1^2\le s\|\delta\|_2^2$. With $\lambda$ of order
  $\sigma\sqrt{(\log p)/n}$, the squared error is of order
  $\sigma^2s(\log p)/n$, matching items 1 and 24 up to the logarithmic
  factor.

* **28. Support recovery under mutual incoherence.** Let $\beta$ be
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
  $c_{\min}^{-1/2}\sigma(\sqrt{2(\log s)/n}+\delta)$. The incoherence
  condition bounds the $\ell^1$ norm of the least-squares coefficients of
  each inactive column on the active ones; it is a stronger requirement
  than the restricted eigenvalue condition of item 27.

### Low-rank and structured covariance estimation

For matrices write $\|\cdot\|_{\mathrm{op}}$, $\|\cdot\|_F$, and
$\|\cdot\|_{\mathrm{nuc}}$ for the operator, Frobenius, and nuclear
(trace) norms, and $\|M\|_{\max}=\max_{j,k}|M_{jk}|$. In **trace
regression** one observes $y_i=\mathop{\mathrm{tr}}(X_i^\top\Theta^*)+w_i$,
$i=1,\ldots,n$, for an unknown $d_1\times d_2$ matrix $\Theta^*$.

* **29. Nuclear-norm penalized trace regression.** Let the $X_i$ have
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
  The rate $r(d_1+d_2)/n$ counts the degrees of freedom of a rank-$r$
  matrix. The nuclear norm plays the role of the $\ell^1$ norm, and
  singular values that of coefficients.

Let $x_1,\ldots,x_n$ be independent copies of a centered random vector in
$\mathbb R^p$ with covariance $\Sigma$, and let
$\hat\Sigma=n^{-1}\sum_ix_ix_i^\top$. The **hard-threshold operator**
$T_\lambda$ replaces each entry $u$ of a matrix by $u1_{\{|u|>\lambda\}}$.
Let $A$ be the $0$–$1$ matrix with $A_{jk}=1$ exactly when
$\Sigma_{jk}\ne0$.

* **30. Thresholded covariance estimation.** If
  $\|\hat\Sigma-\Sigma\|_{\max}\le\lambda$, then
  $$\|T_\lambda(\hat\Sigma)-\Sigma\|_{\mathrm{op}}
  \le2\lambda\|A\|_{\mathrm{op}}\le2s\lambda,$$
  where $s$ is the largest number of nonzero entries in a row of $\Sigma$.
  If each coordinate of $x_i$ is $\sigma$-sub-Gaussian and $n>\log p$, the
  choice $\lambda=\sigma^2(8\sqrt{(\log p)/n}+\delta)$ makes this event hold
  with probability at least $1-8e^{-n\min(\delta,\delta^2)/16}$. Thus a
  row-sparse covariance is estimated in operator norm at rate
  $s\sqrt{(\log p)/n}$, while the sample covariance itself needs $n$ of
  order $p$, by CKMA SYNOPSIS07, item 46. This is the thresholding
  estimator of Bickel and Levina.

For a centered Gaussian vector with covariance $\Sigma$ and **precision
matrix** $\Theta=\Sigma^{-1}$, the conditional-independence graph of
SYNOPSIS106, item 12, has an edge $\{j,k\}$ exactly when $\Theta_{jk}\ne0$.
The **neighbourhood** $N(j)$ of $j$ is the set of such $k$. The regression of
coordinate $j$ on the others has coefficients $-\Theta_{jk}/\Theta_{jj}$,
so its support is $N(j)$. **Neighbourhood selection** runs a lasso of each
coordinate on the others and joins the estimated neighbourhoods by the
"and" or the "or" rule. The **graphical lasso** minimizes
$$\mathop{\mathrm{tr}}(\Theta\hat\Sigma)-\log\det\Theta
+\lambda\sum_{j\ne k}|\Theta_{jk}|$$
over positive definite $\Theta$.

* **31. Gaussian graphical model selection.** Let the data be $n$
  independent $N(0,\Sigma)$ vectors in $\mathbb R^p$, with
  $\Sigma_{jj}\le1$, at most $m$ neighbours per vertex, and $n$ at least a
  constant multiple of $m\log p$. Suppose that for each $j$ the covariance
  $\Gamma$ of the coordinates other than $j$ satisfies
  $$\max_{k\notin N(j)}\|\Gamma_{kN(j)}\Gamma_{N(j)N(j)}^{-1}\|_1\le1-\alpha$$
  for some $\alpha\in(0,1]$, and that
  $\|\Sigma_{N(j)N(j)}^{-1}\|_{\infty\to\infty}\le b$ with $b\ge1$. With
  $\lambda=c_0\alpha^{-1}(\sqrt{(\log p)/n}+\delta)$, $0<\delta\le1$,
  neighbourhood selection by either rule includes no false edge and
  includes every edge with $|\Theta_{jk}|\ge7b\lambda$, with probability
  at least $1-c_2\exp(-c_3n\min(\delta^2,1/m))$; the constants are
  universal. For the graphical lasso with sub-Gaussian coordinates and
  $\lambda$ of order $\sigma^2\sqrt{(\log p)/n}$, the Frobenius error
  $\|\hat\Theta-\Theta\|_F^2$ is with high probability at most a constant
  times $(\|\Theta\|_{\mathrm{op}}+1)^4mp\lambda^2$, once $n$ is large
  enough. This is the high-dimensional analogue of the covariance
  likelihood of SYNOPSIS106, item 25.

### Principal components in high dimensions

* **32. Perturbation of the leading eigenvector.** Let $\Sigma$ be
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

* **33. Spiked sample eigenvectors.** In the spiked model of item 6 with a
  single spike $\alpha>1+\sqrt y$ in the direction $e_1$, let $\hat u$ be a
  unit eigenvector of the sample covariance for its largest eigenvalue.
  Almost surely,
  $$\langle\hat u,e_1\rangle^2\to
  \frac{(\alpha-1)^2-y}{(\alpha-1)(\alpha-1+y)}.$$
  The limit is strictly less than one when $y>0$, and it tends to zero as
  $\alpha$ decreases to the threshold $1+\sqrt y$ at which the sample
  eigenvalue of item 6 separates from the bulk. Thus classical principal
  components are inconsistent when $p/n$ has a positive limit, and
  consistency requires additional structure, such as sparsity of the
  leading eigenvector.

<a id="synopsis-107b"></a>

## 107B. Statistical Learning Theory

Let $(X,Y),(X_1,Y_1),\ldots$ be independent and identically distributed, and
let $\mathcal F$ be a class of measurable decision functions. Write
$R(f)=\mathbb E[L(Y,f(X))]$ and
$R_n(f)=n^{-1}\sum_{i=1}^n L(Y_i,f(X_i))$ for a loss $L$ bounded in $[0,1]$.
The **VC dimension** of a class of binary classifiers is the largest number of
points that the class can shatter, as in CKMA SYNOPSIS07, item 35.

* **7. Fundamental theorem of statistical learning.** For binary
  classification under $0$–$1$ loss, the following are equivalent: the VC
  dimension $v$ is finite; the class is PAC learnable in the realizable case;
  the class is agnostic PAC learnable. In the agnostic case the sample size
  sufficient and necessary for excess risk at most $\varepsilon$, with
  probability at least $1-\delta$, is of order
  $(v+\log(1/\delta))/\varepsilon^2$. In the realizable case the
  corresponding sample size is of order $(v+\log(1/\delta))/\varepsilon$.
  For an empirical-risk minimizer $\hat f$ over a class of VC dimension $v$,
  there is a universal constant $C$ such that, with probability at least
  $1-\delta$,
  $$R(\hat f)\le R_n(\hat f)
  +C\sqrt{\frac{v\log n+\log(1/\delta)}n}.$$
  The uniform deviation behind this bound is CKMA SYNOPSIS07, item 37.

The **empirical Rademacher complexity** of a class $\mathcal F$ on a sample
$x_1,\ldots,x_n$ is
$$\widehat{\mathop{\mathrm{Rad}}}_n(\mathcal F)
=\mathbb E_\sigma\Bigl[\sup_{f\in\mathcal F}
n^{-1}\sum_{i=1}^n\sigma_i f(x_i)\Bigr],$$
where the $\sigma_i$ are independent Rademacher signs.

* **8. Rademacher bound.** For a class of functions with values in $[0,1]$,
  $$\mathbb E\sup_{f\in\mathcal F}|(P_n-P)f|
  \le2\,\mathbb E\,\widehat{\mathop{\mathrm{Rad}}}_n(\mathcal F).$$
  With probability at least $1-\delta$,
  $$\sup_{f\in\mathcal F}|(P_n-P)f|
  \le2\,\mathbb E\,\widehat{\mathop{\mathrm{Rad}}}_n(\mathcal F)
  +\sqrt{\frac{\log(2/\delta)}{2n}}.$$
  The same bound holds with the empirical complexity in place of its
  expectation, after adding a second term of order
  $\sqrt{\log(1/\delta)/n}$ that comes from the bounded-difference inequality
  for $\widehat{\mathop{\mathrm{Rad}}}_n(\mathcal F)$.

* **9. Rademacher complexity of a kernel ball.** Let $K$ be a positive
  definite kernel and let $\mathcal H$ be its reproducing-kernel Hilbert
  space. On the ball $\|f\|_{\mathcal H}\le B$,
  $$\widehat{\mathop{\mathrm{Rad}}}_n(\{f:\|f\|_{\mathcal H}\le B\})
  \le\frac Bn\sqrt{\sum_{i=1}^n K(x_i,x_i)}.$$
  A minimizer of empirical risk plus $\lambda\|f\|_{\mathcal H}^2$ has the
  finite expansion of SYNOPSIS104, item 8.

Consider sequential decisions against a sequence of convex losses
$\ell_t:\mathcal Z\to\mathbb R$, chosen by an adversary who may see the past
predictions. The **regret** after $T$ rounds relative to a comparison class
is the excess cumulative loss over the best fixed comparator in hindsight.

* **10. Online gradient descent.** Let the losses be convex and
  $G$-Lipschitz on a convex set of Euclidean diameter $D$. Online gradient
  descent with step size $\eta=D/(G\sqrt T)$ has regret at most $DG\sqrt T$
  against every fixed comparator in the set.

* **11. Hedge.** For $K$ actions and losses with values in $[0,1]$, the
  exponentially weighted forecaster, with learning rate of order
  $\sqrt{(\log K)/T}$, has regret at most $\sqrt{2T\log K}$ against the best
  fixed action.

Split the sample into a training part and a calibration part of size $n$, and
let $s$ be a score trained on the training part. Let
$S_1,\ldots,S_n$ be the calibration scores and let $S_{n+1}=s(X_{n+1},Y_{n+1})$.
Write $S_{(k)}$ for the $k$th smallest calibration score, and set
$S_{(k)}=+\infty$ when $k>n$.

* **12. Split conformal prediction.** Assume that the $n+1$ pairs are
  exchangeable and that the score is a function of the training part and of
  the pair at which it is evaluated. Let
  $k=\lceil(n+1)(1-\alpha)\rceil$ and let $C(x)=\{y:s(x,y)\le S_{(k)}\}$.
  Then
  $$\mathbb P\bigl(Y_{n+1}\in C(X_{n+1})\bigr)\ge1-\alpha.$$
  If the $n+1$ scores are almost surely distinct, the same probability is at
  most $1-\alpha+1/(n+1)$.

* **13. No free lunch.** Let the feature space be infinite. For every $n$,
  every classification rule based on a sample of size $n$, and every
  $\varepsilon>0$, there exists a distribution, with Bayes error equal to
  zero, under which the expected $0$–$1$ error of the rule is at least
  $1/2-\varepsilon$.

### Statistical targets in classification

* **20. Bayes classification risk.** For binary labels and
  $\eta(x)=P(Y=1\mid X=x)$, a risk-minimizing classifier is
  $g^*(x)=1_{\{\eta(x)\ge1/2\}}$. For every measurable classifier $g$,
  $$R(g)-R(g^*)=\mathbb E\bigl[|2\eta(X)-1|
  1_{\{g(X)\ne g^*(X)\}}\bigr].$$
  A plug-in classifier $\hat g=1_{\{\hat\eta\ge1/2\}}$ satisfies
  $R(\hat g)-R(g^*)\le2\mathbb E|\hat\eta(X)-\eta(X)|$, conditionally
  on independent training data. If
  $P(|\eta(X)-1/2|\le t)\le Ct^\alpha$ for all $t>0$ and
  $\|\hat\eta-\eta\|_\infty\le\delta$, the excess risk is at most
  $2C\delta^{\alpha+1}$. This margin assumption explains rates faster
  than a distribution-free risk bound.

* **21. Empirical risk minimization.** If $\hat f$ minimizes empirical risk
  over $\mathcal F$ up to error $\varepsilon_n$, then
  $$R(\hat f)-\inf_{f\in\mathcal F}R(f)
  \le2\sup_{f\in\mathcal F}|R_n(f)-R(f)|+\varepsilon_n.$$
  Thus the uniform deviations of items 7 and 8 control estimation error
  within a class. The difference between $\inf_{f\in\mathcal F}R(f)$ and
  the unrestricted Bayes risk is a separate approximation error.

### Margins, surrogate losses, and stability

For labels $Y\in\{-1,+1\}$ and a real-valued score $h$, write
$R(h)=P(Yh(X)\le0)$ for the misclassification risk of the sign of $h$. For
$\rho>0$ the **ramp loss** is $\Phi_\rho(u)=\min(1,\max(0,1-u/\rho))$, and
the **empirical margin loss** is
$\hat R_{n,\rho}(h)=n^{-1}\sum_i\Phi_\rho(Y_ih(X_i))$, which is at most the
fraction of sample points with $Y_ih(X_i)\le\rho$. Write
$\mathop{\mathrm{Rad}}_n(\mathcal H)
=\mathbb E\,\widehat{\mathop{\mathrm{Rad}}}_n(\mathcal H)$.

* **34. Margin bound.** Let $\mathcal H$ be a class of real-valued
  functions and fix $\rho>0$. With probability at least $1-\delta$, every
  $h\in\mathcal H$ satisfies
  $$R(h)\le\hat R_{n,\rho}(h)+\frac2\rho\mathop{\mathrm{Rad}}_n(\mathcal H)
  +\sqrt{\frac{\log(1/\delta)}{2n}},$$
  and also, with the empirical complexity on the sample,
  $$R(h)\le\hat R_{n,\rho}(h)
  +\frac2\rho\widehat{\mathop{\mathrm{Rad}}}_n(\mathcal H)
  +3\sqrt{\frac{\log(2/\delta)}{2n}}.$$
  The bound follows from item 8 applied to the ramp loss and the
  contraction principle of CKMA SYNOPSIS07, item 34. For the kernel ball
  $\|h\|_{\mathcal H}\le\Lambda$ with $K(x,x)\le r^2$, item 9 makes the
  complexity term at most $2\Lambda r/(\rho\sqrt n)$, free of the
  dimension of the feature space.

Let $\eta(x)=P(Y=1\mid X=x)$ and let $R^*$ be the Bayes risk of item 20.
For a convex nondecreasing $\Phi:\mathbb R\to[0,\infty)$ the **surrogate
risk** is $R_\Phi(h)=\mathbb E\,\Phi(-Yh(X))$, with infimum $R_\Phi^*$ over
measurable $h$, and the conditional surrogate risk is
$L_\Phi(x,u)=\eta(x)\Phi(-u)+(1-\eta(x))\Phi(u)$.

* **35. Comparison inequality for convex surrogates.** If $\Phi$ is
  differentiable at $0$ with $\Phi'(0)>0$, a minimizer of
  $u\mapsto L_\Phi(x,u)$ in $[-\infty,\infty]$ is positive exactly when $\eta(x)>1/2$ and is
  zero exactly when $\eta(x)=1/2$; thus minimizing the surrogate risk
  yields the Bayes classifier. If moreover there are $s\ge1$ and $c>0$ with
  $$\bigl|\eta(x)-\tfrac12\bigr|^s
  \le c^s\Bigl(L_\Phi(x,0)-\inf_uL_\Phi(x,u)\Bigr)$$
  for all $x$, then for every measurable $h$,
  $$R(h)-R^*\le2c\bigl(R_\Phi(h)-R_\Phi^*\bigr)^{1/s}.$$
  For the hinge loss $\Phi(u)=\max(0,1+u)$ one may take $s=1$, $c=1/2$,
  giving $R(h)-R^*\le R_\Phi(h)-R_\Phi^*$. For the squared loss
  $\Phi(u)=(1+u)^2$ one may take $s=2$, $c=1/2$. Excess surrogate risk,
  which is controlled by uniform deviations, therefore bounds the excess
  classification risk. This is Zhang's inequality.

A learning algorithm maps a sample $S$ of size $n$ to a predictor $h_S$.
It is **uniformly $\beta$-stable** for a loss $L$ if
$|L(h_S,z)-L(h_{S'},z)|\le\beta$ for every point $z$ and every pair of
samples $S,S'$ that differ in one point.

* **36. Generalization of stable algorithms.** If the algorithm is
  uniformly $\beta$-stable and $0\le L(h_S,z)\le M$ for every sample and
  point, then with probability at least $1-\delta$,
  $$R(h_S)\le R_n(h_S)+\beta+(2n\beta+M)\sqrt{\frac{\log(1/\delta)}{2n}}.$$
  The bound is informative when $\beta=o(n^{-1/2})$. Regularized empirical
  risk minimization over a reproducing-kernel Hilbert space,
  $h_S\in\mathop{\mathrm{argmin}}_h\bigl(R_n(h)+\lambda\|h\|_{\mathcal H}^2\bigr)$,
  with $K(x,x)\le r^2$ and a loss convex in the prediction and $G$-Lipschitz
  in it, is uniformly stable with $\beta\le G^2r^2/(n\lambda)$. Stability
  bounds use no complexity measure of the hypothesis class.

### Kernel regression, nearest neighbours, and data splitting

In the fixed-design regression model $y_i=f^*(x_i)+\sigma w_i$, with
independent standard normal $w_i$, write
$\|g\|_n^2=n^{-1}\sum_ig(x_i)^2$. **Kernel ridge regression** is the
minimizer over the reproducing-kernel Hilbert space $\mathcal H$ of
$(2n)^{-1}\sum_i(y_i-f(x_i))^2+\lambda\|f\|_{\mathcal H}^2$; by
SYNOPSIS104, item 8, it is a combination of the functions $K(\cdot,x_i)$.
Let $\hat\mu_1\ge\cdots\ge\hat\mu_n\ge0$ be the eigenvalues of the matrix
$(K(x_i,x_j)/n)_{i,j}$.

* **37. Rate of kernel ridge regression.** Fix $R>0$ and let
  $\delta_n>0$ satisfy the critical inequality
  $$\sqrt{\frac2n\sum_{j=1}^n\min(\delta_n^2,\hat\mu_j)}
  \le\frac R{4\sigma}\delta_n^2.$$
  If $\lambda\ge2\delta_n^2$, then with probability at least
  $1-c_2\exp(-c_3nR^2\delta_n^2/\sigma^2)$, and also in expectation,
  $$\|\hat f-f^*\|_n^2\le c_0\inf_{\|f\|_{\mathcal H}\le R}
  \Bigl(\|f-f^*\|_n^2+c_1R^2(\delta_n^2+\lambda)\Bigr),$$
  with universal constants. For a kernel of finite rank $m$, $R^2\delta_n^2$
  is of order $\sigma^2m/n$. If $\hat\mu_j\le cj^{-2\alpha}$ with
  $\alpha>1/2$, then for fixed $R$ the squared critical radius is of order
  $(\sigma^2/n)^{2\alpha/(2\alpha+1)}$. The first-order Sobolev kernel
  $\min(x,z)$ on $[0,1]$ has $\alpha=1$ and rate $n^{-2/3}$, in agreement
  with SYNOPSIS104, item 9.

In binary classification with labels in $\{0,1\}$ and features in
$\mathbb R^d$, the **$k$-nearest-neighbour rule** takes a majority vote
among the labels of the $k$ sample points closest to $x$ in Euclidean
distance, distance ties being broken by index. Write $L_n$ for its error
probability given the sample and $L^*$ for the Bayes risk.

* **38. Asymptotics of nearest-neighbour rules.** For every distribution
  of $(X,Y)$, the $1$-nearest-neighbour rule satisfies
  $$\lim_{n\to\infty}\mathbb E L_n=L_{\mathrm{NN}}
  =\mathbb E\bigl[2\eta(X)(1-\eta(X))\bigr],\qquad
  L^*\le L_{\mathrm{NN}}\le2L^*(1-L^*)\le2L^*.$$
  For fixed odd $k$ the limit $L_{k\mathrm{NN}}$ of $\mathbb EL_n$ exists
  for every distribution and satisfies
  $L^*\le L_{k\mathrm{NN}}\le L^*+1/\sqrt{ke}$; it is nonincreasing over
  odd $k$. Universal consistency, $\mathbb EL_n\to L^*$ for every
  distribution, holds when $k\to\infty$ and $k/n\to0$, as in Stone's
  theorem, SYNOPSIS104, item 7. The bound $L_{\mathrm{NN}}\le2L^*$ is the
  Cover–Hart bound.

* **39. Hold-out selection.** Split the sample into a training part and an
  independent hold-out part of size $l$. Let $\phi_1,\ldots,\phi_N$ be
  classifiers computed from the training part, and let $\hat\phi$ minimize
  the hold-out error frequency among them. Conditionally on the training
  part, with probability at least $1-\delta$,
  $$L(\hat\phi)\le\min_{1\le j\le N}L(\phi_j)
  +\sqrt{\frac{2\log(2N/\delta)}l},$$
  where $L$ is the error probability. When the candidate set is infinite,
  a bound of the same type holds, up to constants, with the logarithm of a
  shatter coefficient of the candidate class in place of $\log N$. Hence
  data splitting selects a consistent rule from candidate classes that
  contain one, provided that the logarithm of the expected shatter
  coefficient on $l$ points is $o(l)$. The penalized selector of item 3 is the analogue without
  splitting.

## Reference guide

### Correspondence with the subdivisions

- **[107A](#synopsis-107a)**: van de Geer, Wainwright, Giraud, Koltchinskii,
  and Massart carry sparsity and penalized model selection. Dudoit and van
  der Laan, and Dickhaus, carry multiple testing. Yao, Zheng, and Bai carry
  the Wishart edge and the spiked model. Vershynin, Boucheron, Lugosi, and
  Massart, Tropp, and Foucart and Rauhut supply the concentration and
  restricted-isometry ingredients cited from the analysis synopsis.
  Tsybakov and Giraud carry the hypercube and sparse minimax lower bounds;
  Wainwright carries sparse recovery, low-rank and graphical-model
  estimation, and high-dimensional principal components.
- **[107B](#synopsis-107b)**: Vapnik, Anthony and Bartlett, Mohri,
  Rostamizadeh, and Talwalkar, and Devroye, Györfi, and Lugosi carry VC
  theory and the no-free-lunch theorem. Cesa-Bianchi and Lugosi carry online
  regret. Koltchinskii carries the Rademacher and kernel bounds. Mohri,
  Rostamizadeh, and Talwalkar carry margins, surrogate losses, and
  stability; Wainwright carries kernel ridge regression; Devroye, Györfi,
  and Lugosi carry nearest-neighbour rules and data splitting.

### Source comparisons and local copies

Wainwright's Chapter 15 was read for the estimation-to-testing
reduction, Le Cam's method, and Proposition 15.12 on Fano's method.
Its sparse-regression and model-selection chapters supply the surrounding
regularization framework. Item 1 distinguishes a sparsity-tuned
threshold from the universal threshold, and item 3 requires a sufficiently
large penalty multiplier. Item 18 states the exact bias decomposition
and a sufficient remainder condition, without asserting asymptotic
normality for arbitrary designs. Items 20 and 21 separate Bayes risk,
approximation error, and the uniform deviations already cited from CKMA.

Item 2 is the consequence, at stretching factor $3$, of the sharp oracle
inequality in van de Geer for the lasso normalized as
$n^{-1}\|Y-X\beta\|_2^2+2\lambda\|\beta\|_1$. The factor $3$ is the cone
constant obtained when the penalty level is at least twice
$n^{-1}\|X^\top\varepsilon\|_\infty$. Item 6 follows Yao, Zheng, and Bai:
the centering $\mu_{n,p}$ is asymptotic to the Marchenko–Pastur right edge
$(1+\sqrt y)^2$, and the spike map $\alpha+y\alpha/(\alpha-1)$ is continuous
at the threshold $1+\sqrt y$.

For items 22–39 the following passages were read. Tsybakov, Lemma 2.9
and Lemma 2.12 with Theorem 2.12, supplies the Varshamov–Gilbert bound and
Assouad's lemma; the metric reduction in item 23 is the nearest-index
argument of his Example 2.2. Giraud, Theorem 3.5 and Section 3.4.2, gives
the sparse-regression minimax bound of item 24. Wainwright supplies
Theorem 7.8 and Proposition 7.11 (item 25), Theorem 7.13 (item 27),
Theorem 7.21 and Corollary 7.22 (item 28), Corollary 10.10 for the
standard Gaussian ensemble (item 29), Theorem 6.23 and Corollary 6.24
(item 30), Proposition 11.9 and Theorem 11.12 (item 31), Theorem 8.5 and
Corollary 8.7 (item 32), and Theorem 13.17, Corollary 13.18, and
Examples 13.19–13.20 (item 37). Foucart and Rauhut, Theorem 6.12, gives
item 26. Yao, Zheng, and Bai, Theorem 11.5 and Corollary 11.6, give the
spiked-eigenvector limit of item 33. Mohri, Rostamizadeh, and Talwalkar
supply Theorem 5.8 and Corollary 5.11 (item 34), Proposition 4.6 and
Theorem 4.7 with Exercise 4.2 (item 35), and Theorem 14.2 with
Proposition 14.4 (item 36). Devroye, Györfi, and Lugosi supply
Theorems 5.1, 5.4, and 5.6 (item 38) and Section 22.1 with Theorem 8.3
and Theorem 22.1 (item 39). The hinge-loss constants in item 35 and the
polynomial eigenvalue-decay rate in item 37 are direct computations from
those statements. The graphical-lasso bound in item 31 is stated only up
to a constant factor. No local source treats the knockoff filter or
PAC-Bayes bounds, and the boosting training-error bound is left to the
model-oriented Section 113.

Bühlmann and van de Geer, *Statistics for High-Dimensional Data*, Hastie,
Tibshirani, and Friedman, *The Elements of Statistical Learning*,
Shalev-Shwartz and Ben-David, *Understanding Machine Learning*,
Steinwart and Christmann, *Support Vector Machines*,
Vovk, Gammerman, and Shafer, *Algorithmic Learning in a Random World*, and
Efron, *Large-Scale Inference*, are not in the local reference directory.
Item 12 is the split-conformal coverage theorem of that literature. The
false-discovery statement in item 5 is the Benjamini–Hochberg theorem under
independence and under positive regression dependence. A supplemental
copy of Cucker and Zhou, *Learning Theory*, is present but was not read
for this expansion.

Local texts directly consulted or identified for this selection:

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
- [Tsybakov, *Introduction to Nonparametric Estimation*](../lean-CKMA/ReferencesSuppl/Tsybakov2009IntroductionNonparametricEstimation-SpringerSSS.pdf).
- [Foucart and Rauhut, *A Mathematical Introduction to Compressive Sensing*](../lean-CKMA/References/FoucartRauhut2013MathematicalIntroductionCompressiveSensing-BirkhäuserANHA.pdf).
- [Vapnik, *Statistical Learning Theory*](../lean-CKMA/References/Vapnik1998StatisticalLearningTheory-WileyInterscience.pdf).
- [Anthony and Bartlett, *Neural Network Learning*](../lean-CKMA/References/AnthonyBartlett1999NeuralNetworkLearningTheoreticalFoundations-Cambridge.pdf).
- [Mohri, Rostamizadeh, and Talwalkar, *Foundations of Machine Learning*](../lean-CKMA/References/MohriRostamizadehTalwalkar2018FoundationsMachineLearning2ndEd-MITPress.ACML.pdf).
- [Devroye, Györfi, and Lugosi, *A Probabilistic Theory of Pattern Recognition*](../lean-CKMA/References/DevroyeGyörfiLugosi1996ProbabilisticTheoryPatternRecognition-Springer.SMAP31.pdf).
- [Cesa-Bianchi and Lugosi, *Prediction, Learning, and Games*](../lean-CKMA/References/CesaBianchiLugosi2006PredictionLearningGames-Cambridge.pdf).
