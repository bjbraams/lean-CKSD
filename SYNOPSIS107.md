# Synopsis: Statistical learning and machine learning

Part of the [mathematical synopsis series](SYNOPSIS.md).
[Bibliographical scope and references](CKSD-bib.md#cks-107).

This synopsis follows Section 107. Subdivision 107A is statistical learning
theory, ensembles and probabilistic models, the approximation and training
theory of neural networks, and network data. Subdivision 107B is bandits and
reinforcement learning, privacy, fairness, and distribution shift. The
Sauer–Shelah bound and uniform deviations for VC classes are
[CKMA SYNOPSIS07](../lean-CKMA/SYNOPSIS07.md), items 35 and 37. Soft
thresholding, the representer theorem, and kernel ridge regression are
[SYNOPSIS103](SYNOPSIS103.md), items 8 and 10. Simple kriging is [SYNOPSIS106](SYNOPSIS106.md), item 20. The evidence lower bound is [SYNOPSIS104](SYNOPSIS104.md), item 25.
Exchangeability of sequences is [CKMA SYNOPSIS06](../lean-CKMA/SYNOPSIS06.md),
item 55. Ridge-function approximation in the analytic sense is CKMA
Section 47, and continuous-time stochastic control remains in CKMA Section 8.
Optimization algorithms are in Section 109 of the bibliography, outside this
series.

Numbered definitions and results have stable identifiers. Additions take the
next free number and are placed beside related material; numbers need not
increase in reading order. Proofs are outside the scope of this synopsis.

<a id="synopsis-107a"></a>

## 107A. Learning Theory, Probabilistic Models, Deep Learning, and Networks

### Statistical learning theory

Let $(X,Y),(X_1,Y_1),\ldots$ be independent and identically distributed, and
let $\mathcal F$ be a class of measurable decision functions. Write
$R(f)=\mathbb E[L(Y,f(X))]$ and
$R_n(f)=n^{-1}\sum_{i=1}^n L(Y_i,f(X_i))$ for a loss $L$ bounded in $[0,1]$.
The **VC dimension** of a class of binary classifiers is the largest number of
points that the class can shatter, as in CKMA SYNOPSIS07, item 35.

* **1. Fundamental theorem of statistical learning.** For binary
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

* **2. Rademacher bound.** For a class of functions with values in $[0,1]$,
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

* **3. Rademacher complexity of a kernel ball.** Let $K$ be a positive
  definite kernel and let $\mathcal H$ be its reproducing-kernel Hilbert
  space. On the ball $\|f\|_{\mathcal H}\le B$,
  $$\widehat{\mathop{\mathrm{Rad}}}_n(\{f:\|f\|_{\mathcal H}\le B\})
  \le\frac Bn\sqrt{\sum_{i=1}^n K(x_i,x_i)}.$$
  A minimizer of empirical risk plus $\lambda\|f\|_{\mathcal H}^2$ has the
  finite expansion of SYNOPSIS103, item 8.

Consider sequential decisions against a sequence of convex losses
$\ell_t:\mathcal Z\to\mathbb R$, chosen by an adversary who may see the past
predictions. The **regret** after $T$ rounds relative to a comparison class
is the excess cumulative loss over the best fixed comparator in hindsight.

* **4. Online gradient descent.** Let the losses be convex and
  $G$-Lipschitz on a convex set of Euclidean diameter $D$. Online gradient
  descent with step size $\eta=D/(G\sqrt T)$ has regret at most $DG\sqrt T$
  against every fixed comparator in the set.

* **5. Hedge.** For $K$ actions and losses with values in $[0,1]$, the
  exponentially weighted forecaster, with learning rate of order
  $\sqrt{(\log K)/T}$, has regret at most $\sqrt{2T\log K}$ against the best
  fixed action.

Split the sample into a training part and a calibration part of size $n$, and
let $s$ be a score trained on the training part. Let
$S_1,\ldots,S_n$ be the calibration scores and let $S_{n+1}=s(X_{n+1},Y_{n+1})$.
Write $S_{(k)}$ for the $k$th smallest calibration score, and set
$S_{(k)}=+\infty$ when $k>n$.

* **6. Split conformal prediction.** Assume that the $n+1$ pairs are
  exchangeable and that the score is a function of the training part and of
  the pair at which it is evaluated. Let
  $k=\lceil(n+1)(1-\alpha)\rceil$ and let $C(x)=\{y:s(x,y)\le S_{(k)}\}$.
  Then
  $$\mathbb P\bigl(Y_{n+1}\in C(X_{n+1})\bigr)\ge1-\alpha.$$
  If the $n+1$ scores are almost surely distinct, the same probability is at
  most $1-\alpha+1/(n+1)$.

* **7. No free lunch.** Let the feature space be infinite. For every $n$,
  every classification rule based on a sample of size $n$, and every
  $\varepsilon>0$, there exists a distribution, with Bayes error equal to
  zero, under which the expected $0$–$1$ error of the rule is at least
  $1/2-\varepsilon$.

### Statistical targets in classification

* **8. Bayes classification risk.** For binary labels and
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

* **9. Empirical risk minimization.** If $\hat f$ minimizes empirical risk
  over $\mathcal F$ up to error $\varepsilon_n$, then
  $$R(\hat f)-\inf_{f\in\mathcal F}R(f)
  \le2\sup_{f\in\mathcal F}|R_n(f)-R(f)|+\varepsilon_n.$$
  Thus the uniform deviations of items 1 and 2 control estimation error
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

* **10. Margin bound.** Let $\mathcal H$ be a class of real-valued
  functions and fix $\rho>0$. With probability at least $1-\delta$, every
  $h\in\mathcal H$ satisfies
  $$R(h)\le\hat R_{n,\rho}(h)+\frac2\rho\mathop{\mathrm{Rad}}_n(\mathcal H)
  +\sqrt{\frac{\log(1/\delta)}{2n}},$$
  and also, with the empirical complexity on the sample,
  $$R(h)\le\hat R_{n,\rho}(h)
  +\frac2\rho\widehat{\mathop{\mathrm{Rad}}}_n(\mathcal H)
  +3\sqrt{\frac{\log(2/\delta)}{2n}}.$$
  The bound follows from item 2 applied to the ramp loss and the
  contraction principle of CKMA SYNOPSIS07, item 34. For the kernel ball
  $\|h\|_{\mathcal H}\le\Lambda$ with $K(x,x)\le r^2$, item 3 makes the
  complexity term at most $2\Lambda r/(\rho\sqrt n)$, free of the
  dimension of the feature space.

Let $\eta(x)=P(Y=1\mid X=x)$ and let $R^*$ be the Bayes risk of item 8.
For a convex nondecreasing $\Phi:\mathbb R\to[0,\infty)$ the **surrogate
risk** is $R_\Phi(h)=\mathbb E\,\Phi(-Yh(X))$, with infimum $R_\Phi^*$ over
measurable $h$, and the conditional surrogate risk is
$L_\Phi(x,u)=\eta(x)\Phi(-u)+(1-\eta(x))\Phi(u)$.

* **11. Comparison inequality for convex surrogates.** If $\Phi$ is
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

* **12. Generalization of stable algorithms.** If the algorithm is
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
SYNOPSIS103, item 8, it is a combination of the functions $K(\cdot,x_i)$.
Let $\hat\mu_1\ge\cdots\ge\hat\mu_n\ge0$ be the eigenvalues of the matrix
$(K(x_i,x_j)/n)_{i,j}$.

* **13. Rate of kernel ridge regression.** Fix $R>0$ and let
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
  with SYNOPSIS103, item 9.

In binary classification with labels in $\{0,1\}$ and features in
$\mathbb R^d$, the **$k$-nearest-neighbour rule** takes a majority vote
among the labels of the $k$ sample points closest to $x$ in Euclidean
distance, distance ties being broken by index. Write $L_n$ for its error
probability given the sample and $L^*$ for the Bayes risk.

* **14. Asymptotics of nearest-neighbour rules.** For every distribution
  of $(X,Y)$, the $1$-nearest-neighbour rule satisfies
  $$\lim_{n\to\infty}\mathbb E L_n=L_{\mathrm{NN}}
  =\mathbb E\bigl[2\eta(X)(1-\eta(X))\bigr],\qquad
  L^*\le L_{\mathrm{NN}}\le2L^*(1-L^*)\le2L^*.$$
  For fixed odd $k$ the limit $L_{k\mathrm{NN}}$ of $\mathbb EL_n$ exists
  for every distribution and satisfies
  $L^*\le L_{k\mathrm{NN}}\le L^*+1/\sqrt{ke}$; it is nonincreasing over
  odd $k$. Universal consistency, $\mathbb EL_n\to L^*$ for every
  distribution, holds when $k\to\infty$ and $k/n\to0$, as in Stone's
  theorem, SYNOPSIS103, item 7. The bound $L_{\mathrm{NN}}\le2L^*$ is the
  Cover–Hart bound.

* **15. Hold-out selection.** Split the sample into a training part and an
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
  coefficient on $l$ points is $o(l)$. The penalized selector of SYNOPSIS103, item 35 is the analogue without
  splitting.

### Foundations, probabilistic modelling, and ensembles

The posterior mean of a Gaussian process with covariance kernel $k$ and
noise variance $\sigma^2$ is the kernel ridge regressor of SYNOPSIS103, item 8, with $\lambda=\sigma^2/n$ for its averaged-loss convention, and it is the simple-kriging
predictor of SYNOPSIS106, item 20. A variational autoencoder maximizes the
evidence lower bound of SYNOPSIS104, item 25, with an encoder that maps each
observation to the parameter of the variational factor; the
reparameterization $z=\mu(x)+\sigma(x)\varepsilon$ makes the gradient of
that bound an ordinary expectation under a parameter-free noise law.

Let $X$ take values in $\mathbb R^d$ with $\mathbb E\|X\|^2<\infty$,
and fix $k\ge1$. The $k$-means criterion of a set of centers $c$ is
$\mathbb E\bigl(\min_j\|X-c_j\|^2\bigr)$.

* **16. Consistency of $k$-means.** Suppose $\mathbb E\|X\|^2<\infty$,
  the support contains at least $k$ distinct points, and the population
  optimal $k$-center set is unique up to labels. Then empirical global
  minimizing center sets converge almost surely to that set, up to
  permutation. The nondegeneracy prevents unused centers from escaping
  to infinity. This concerns global minimizers; convergence of Lloyd's
  iteration to a stationary configuration does not imply it finds them.

A binary tree $T$ grown on a training sample has resubstitution error
$R(T)$ and $|T|$ terminal nodes. For $\alpha\ge0$ the **cost-complexity**
is $R_\alpha(T)=R(T)+\alpha|T|$.

* **17. Cost-complexity pruning.** For each $\alpha$ there is a smallest
  subtree minimizing $R_\alpha$. As $\alpha$ increases through $[0,\infty)$,
  these smallest minimizers form a nested decreasing sequence of subtrees.

For squared error, let $f^*(X)=\mathbb E[Y\mid X]$, with $Y\in L^2$,
and put $r_m=f^*-f_m$. The excess prediction risk is $\|r_m\|_2^2$.
A base learner $h_m$ is a nonzero square-integrable function of $X$.

* **18. Descent of gradient boosting.** Suppose
  $\langle r_m,h_m\rangle\ge\gamma\|r_m\|_2\|h_m\|_2$ for a fixed
  $\gamma>0$. Choose the least-squares coefficient
  $a_m=\langle r_m,h_m\rangle/\|h_m\|_2^2$ and update
  $f_{m+1}=f_m+\nu a_m h_m$, with $0<\nu<2$. Then
  $$\|r_{m+1}\|_2^2\le
  (1-\nu(2-\nu)\gamma^2)\|r_m\|_2^2.$$
  Thus the excess risk decreases geometrically. Scaling each learner
  properly is essential; positive correlation and comparable norms alone
  do not imply descent for an arbitrary fixed step. Irreducible response
  noise is excluded from the excess risk.

For a finite-state pairwise graphical model with positive node and edge
potentials, the **Bethe free energy** uses local node and edge marginals,
subject to normalization and marginal-consistency constraints. Its entropy
approximation is $H_B=\sum_{\{i,j\}\in E}H(b_{ij})
-\sum_i(d_i-1)H(b_i)$. **Belief propagation** updates messages along edges.

* **19. Belief propagation and the Bethe free energy.** Positive
  belief-propagation fixed points correspond to interior stationary
  points of the constrained Bethe free energy. Stationarity need not
  mean global minimality or convergence of the message iteration on a
  graph with cycles. Restricting local beliefs to products
  $b_{ij}=b_i b_j$ gives the fully factorized mean-field objective,
  related to the evidence lower bound in SYNOPSIS104, item 25.
  Exact inference on trees is item 23 below.

* **20. Consistency of response-independent forests.** Consider tree
  partitions formed independently of responses, with leaf averages
  computed from an independent sample of identically distributed pairs.
  Suppose the diameter of the leaf containing an independent query $X$
  tends to zero in probability,
  its estimation-sample size tends to infinity, and the resulting
  nonnegative weights sum to one and satisfy the bounded-averaging
  condition
  $$\mathbb E\sum_iw_{ni}(X)g(X_i)\le C\mathbb E g(X)$$
  for all nonnegative bounded $g$, with a fixed $C$ and independent
  query $X$. Require also
  $\mathbb E\sum_iw_{ni}(X)1_{\{\|X_i-X\|>\eta\}}\to0$ for every
  $\eta>0$ and $\mathbb E\max_iw_{ni}(X)\to0$.
  Then the tree regression, and averages of trees drawn from the same
  construction, are consistent in integrated mean squared error for
  $Y\in L^2$. Honesty and growing leaf size
  without shrinking cells are insufficient. Response-adaptive Breiman
  forests require separate model and splitting assumptions, such as
  those in the additive-model theorem of Scornet, Biau, and Vert.

### Prediction losses and ensemble structure

* **21. Proper prediction losses.** For a categorical response with
  conditional probabilities $p_j(x)$, expected logarithmic loss of a
  reported probability vector $q$ equals
  $$-\sum_jp_j\log q_j
  =-\sum_jp_j\log p_j+D(p\|q).$$
  It is minimized by the true probabilities. For the Brier loss
  $\sum_j(q_j-1_{\{Y=j\}})^2$, the excess conditional risk is
  $\sum_j(q_j-p_j)^2$. Thus these losses target conditional
  distributions, whereas $0$–$1$ loss only determines a most probable
  label. Bayes classification risk is item 8.

* **22. Variance of an ensemble average.** If $B$ square-integrable
  predictions have the same variance $\sigma^2$ and pairwise correlation
  $\rho$, their average has variance
  $$\sigma^2\left(\rho+\frac{1-\rho}{B}\right).$$
  Independently randomized learners on the same training sample can
  remain correlated after averaging over that common sample. Under
  squared loss the full risk also includes squared bias; averaging
  controls variance without automatically removing bias or establishing
  consistency. This explains the separate shrinking-cell assumptions
  in item 20.

* **23. Exact belief propagation on a tree.** For the positive pairwise
  model of item 19 on a tree, messages satisfy
  $$m_{i\to j}(x_j)\propto\sum_{x_i}\psi_i(x_i)\psi_{ij}(x_i,x_j)
  \prod_{\ell\in N(i)\setminus\{j\}}m_{\ell\to i}(x_i).$$
  A pass from leaves to a root and back computes exact node and edge
  marginals; the node marginal is proportional to
  $\psi_i(x_i)\prod_{j\in N(i)}m_{j\to i}(x_i)$.
  Local consistency is sufficient for globally realizable beliefs on
  a tree, and the Bethe entropy is exact there. Cycles remove these
  guarantees.

### Boosting and tree splitting

Let a sample $(x_i,y_i)$, $i=1,\ldots,m$, have labels $y_i\in\{-1,1\}$, and
let the base classifiers take values in $\{-1,1\}$. **AdaBoost** starts from
the uniform weights $D_1(i)=1/m$. At round $t$ it selects $h_t$ with
weighted error $\varepsilon_t=\sum_iD_t(i)1_{\{h_t(x_i)\ne y_i\}}$, sets
$\alpha_t=\tfrac12\log\bigl((1-\varepsilon_t)/\varepsilon_t\bigr)$, and
puts $D_{t+1}(i)\propto D_t(i)\exp(-\alpha_ty_ih_t(x_i))$. After $T$ rounds
it returns $f=\sum_{t\le T}\alpha_th_t$.

* **24. AdaBoost: training error and margins.** Suppose
  $0<\varepsilon_t<1/2$ in every round. Then the training error of
  $\mathop{\mathrm{sign}}f$ satisfies
  $$\frac1m\#\{i:y_if(x_i)\le0\}
  \le\prod_{t=1}^T2\sqrt{\varepsilon_t(1-\varepsilon_t)}
  \le\exp\Bigl(-2\sum_{t=1}^T\bigl(\tfrac12-\varepsilon_t\bigr)^2\Bigr),$$
  hence it is at most $e^{-2\gamma^2T}$ if every
  $\varepsilon_t\le\frac12-\gamma$. For $\rho>0$, the fraction of sample
  points with normalized margin $y_if(x_i)/\|\alpha\|_1\le\rho$ is at most
  $2^T\prod_t\sqrt{\varepsilon_t^{1-\rho}(1-\varepsilon_t)^{1+\rho}}$; it
  decreases geometrically in $T$ when every
  $\varepsilon_t\le\frac12-\gamma$ and $\rho<\gamma$. The empirical
  Rademacher complexity of the convex hull of a class equals that of the
  class, so the margin bound of item 10, applies to
  $f/\|\alpha\|_1$ with the complexity of the base class and without
  dependence on $T$. AdaBoost is coordinate descent with exact line
  search on the empirical exponential loss $\sum_ie^{-y_if(x_i)}$. These
  are training-sample and uniform-deviation statements; they do not
  assert consistency of boosting run for an arbitrary number of rounds.

For $J$ classes, an **impurity function** $\phi$ on the probability simplex
is symmetric, maximal only at the uniform vector, and minimal only at the
vertices. At a node $t$ with class proportions $p(\cdot\mid t)$ the node
impurity is $i(t)=\phi(p(\cdot\mid t))$. A split sending proportions $p_L$
and $p_R$ of the cases in $t$ to children $t_L$ and $t_R$ has **impurity
decrease** $\Delta i=i(t)-p_Li(t_L)-p_Ri(t_R)$. The Gini index
$1-\sum_jp_j^2$ and the entropy $-\sum_jp_j\log p_j$ are strictly concave
impurity functions.

* **25. Impurity decrease of a split.** If $\phi$ is strictly concave, then
  $\Delta i\ge0$ for every split with $p_L,p_R>0$, with equality only when
  both children have the class proportions of the parent. Since
  $p(j\mid t)=p_Lp(j\mid t_L)+p_Rp(j\mid t_R)$, this is Jensen's
  inequality. For two classes and a categorical predictor with $L$
  categories, order the categories by their class-one proportion within
  the node. For a twice differentiable strictly concave symmetric impurity
  vanishing at the vertices, some optimal split puts an initial segment of
  this ordering in one child. Thus $L-1$ splits replace the
  $2^{L-1}-1$ candidates. The resubstitution misclassification rate is
  concave but not strictly concave, and its decrease can vanish for splits
  that change the class proportions.

### Variational and exact inference

Let $p_\theta(x)=\exp(\langle\theta,\phi(x)\rangle-A(\theta))$ be an
exponential family with respect to $\nu$, with open natural parameter
space $\Omega$ and affinely independent statistics. The **set of realizable
mean parameters** $\mathcal M$ consists of the vectors $\mathbb E_p\phi(X)$
over all $\nu$-densities $p$ for which this expectation exists. Its
**conjugate dual** is
$A^*(\mu)=\sup_{\theta\in\Omega}\{\langle\mu,\theta\rangle-A(\theta)\}$.
For a finite discrete graphical model with indicator statistics of node and
edge configurations, $\mathcal M$ is the **marginal polytope**; the
consistency constraints of item 19 define a polytope containing it.

* **26. Variational representation of the cumulant function.** The map
  $\nabla A$ sends $\Omega$ onto the interior $\mathcal M^\circ$. For
  $\mu\in\mathcal M^\circ$, $A^*(\mu)=-H(p_{\theta(\mu)})$ is the negative
  entropy of the unique member with mean $\mu$, and $A^*=+\infty$ off the
  closure of $\mathcal M$. Moreover
  $$A(\theta)=\sup_{\mu\in\mathcal M}\{\langle\theta,\mu\rangle-A^*(\mu)\},$$
  attained uniquely at $\mu=\mathbb E_\theta\phi(X)$. For a finite
  discrete model,
  $$\max_x\langle\theta,\phi(x)\rangle
  =\max_{\mu\in\bar{\mathcal M}}\langle\theta,\mu\rangle
  =\lim_{\beta\to\infty}A(\beta\theta)/\beta,$$
  so mode computation is a linear program over the marginal polytope.
  Mean-field methods restrict $\mu$ to an inner subset on which $A^*$ is
  computable and give lower bounds on $A$. The Bethe problem of item 19
  uses the larger consistency polytope and the entropy $H_B$; on graphs
  with cycles its value is in general not a bound on $A$. The
  statistical mean parameterization is SYNOPSIS101, item 42.

A **clique tree** of a graph is a tree whose nodes are its maximal cliques.
It has the **running intersection property**, and is then a **junction
tree**, when every clique on the path joining two cliques contains their
intersection. The intersections of adjacent cliques are the separators.

* **27. Junction-tree exactness.** A graph has a junction tree if and only
  if it is triangulated, that is, decomposable in the sense of
  SYNOPSIS105, item 36. On a junction tree, nonnegative clique and
  separator tables are the marginals of a single distribution if and only
  if each separator table is normalized and each clique table marginalizes
  to every separator it contains. The distribution is then the ratio of
  clique marginals to separator marginals of that item. Consequently,
  after triangulating, sum-product message passing between cliques gives
  exact marginals and the cumulant function of any finite model that
  factorizes over the original graph. Its cost grows exponentially in the
  largest clique size of the triangulation. Item 23 is the tree case.
  Without triangulation, local consistency does not imply global
  realizability, as in item 19.

### Deep learning: architectures, approximation, and training

Density of one-hidden-layer networks in $C(K)$, for a nonpolynomial
continuous activation, is [CKMA SYNOPSIS47](../lean-CKMA/SYNOPSIS47.md),
item 76.

* **28. Barron's rate.** Suppose $f\in L^1(\mathbb R^d)$ has a finite
  Fourier moment
  $C_f=\int_{\mathbb R^d}\|\omega\|\,|\hat f(\omega)|\,d\omega$. On a design
  supported in a fixed ball there is a one-hidden-layer network with $n$
  sigmoidal units and an output bias whose $L^2$ error is at most a
  constant, depending on the ball radius and activation, times
  $C_f n^{-1/2}$. ReLU units also admit this form of the bound.
  The exponent is $-1/2$ in every dimension $d$; finiteness or size
  of $C_f$ remains a restriction on the target function.

* **29. Deep networks and compositional classes.** In nonparametric
  regression with design density bounded above and below by positive
  constants on a compact cube, Gaussian noise, and regression
  functions that are compositions of bounded Hölder maps, let stage $i$
  have smoothness $\beta_i$ and at most $t_i$ active input coordinates
  per component. Put
  $$\beta_i^*=\beta_i\prod_{j>i}\min(\beta_j,1).$$
  Under the usual class nondegeneracy conditions the minimax integrated
  squared-error rate is
  $\max_i n^{-2\beta_i^*/(2\beta_i^*+t_i)}$.
  Suitably constrained sparse ReLU least-squares estimators attain this
  rate up to logarithmic factors. The statement concerns specified
  statistical estimators and classes, not the outcome of arbitrary
  network training.

In the **neural tangent** parameterization the output weights and the inner
weights are scaled so that a gradient step remains of order one as the width
tends to infinity. The **neural tangent kernel** is the Gram matrix of the
output's gradient with respect to the parameters.

* **30. Neural tangent kernel.** In the standard neural-tangent scaling
  of a fully connected network with independent Gaussian initialization,
  assume fixed depth, a fixed finite training set, and a smooth activation
  with bounded derivatives as required for the kernel limit. As the
  hidden widths tend to infinity, the empirical tangent Gram matrix
  converges to a deterministic matrix $\Theta$. For squared loss and
  gradient flow, on fixed finite time intervals the limiting training
  outputs satisfy
  $$\dot f_t=-\Theta(f_t-y)/n.$$
  Linearization is valid in this width limit under its regularity
  hypotheses; it is not a generic property of every parameterization or
  every duration of finite-width training.

Let $x_i$ be independent standard normal vectors in $\mathbb R^p$, let
$y_i=x_i^\top\beta+\varepsilon_i$ with independent centered errors
of variance $\sigma^2$, independent of the design, and let $\hat\beta$ be the minimum-$\ell^2$-norm least
squares estimator. The **excess prediction risk** is
$\mathbb E(x^\top\hat\beta-x^\top\beta)^2$, averaging over the training
data and an independent test point $x$. The parameter vectors are
deterministic. Write $\gamma=\lim p/n$.

* **31. Ridgeless least squares.** In the isotropic Gaussian design,
  the expected excess prediction risk is exactly
  $$\frac{\sigma^2p}{n-p-1}\quad(n>p+1),$$
  and
  $$\|\beta\|^2(1-n/p)+\frac{\sigma^2 n}{p-n-1}\quad(p>n+1).$$
  If $p/n\to\gamma\in(0,\infty)\setminus\{1\}$ and
  $\|\beta\|^2\to r^2$, the respective limits are
  $\sigma^2\gamma/(1-\gamma)$ and
  $r^2(1-1/\gamma)+\sigma^2/(\gamma-1)$.
  The inverse-Wishart denominators expose the risk singularity near
  interpolation; existence of an interpolating estimator alone does
  not bound its prediction risk.

For a generator density $p_g$ and a data density $p$, the **generative
adversarial** value of a discriminator $D$ with values in $[0,1]$ is
$$\mathbb E_p\log D(X)+\mathbb E_{p_g}\log\bigl(1-D(X)\bigr).$$

* **32. Equilibrium of a generative adversary.** For fixed $p_g$ the optimal
  discriminator is $D^\star(x)=p(x)/\bigl(p(x)+p_g(x)\bigr)$ wherever the sum
  is positive. Its value equals $-\log4+2\,\mathop{\mathrm{JSD}}(p,p_g)$,
  where $\mathop{\mathrm{JSD}}$ is the Jensen–Shannon divergence,
  with the usual $0\log0=0$ convention. If $D$ is restricted to
  $(0,1)$, this can be a supremum rather than an attained maximum.
  The value
  is minimized, with minimum $-\log4$, if and only if $p_g=p$.

### Probabilistic output layers and kernel prediction

* **33. Softmax and cross-entropy.** For logits $z\in\mathbb R^K$,
  let $A(z)=\log\sum_j e^{z_j}$ and $q_j=e^{z_j-A(z)}$.
  For a one-hot observed label $y$, logarithmic loss is $A(z)-y^\top z$,
  with gradient $q-y$ and Hessian
  $$\mathop{\mathrm{diag}}(q)-qq^\top.$$
  The Hessian is positive semidefinite and vanishes in the direction
  $1$, reflecting invariance to adding a constant to all logits.
  Convexity in logits does not imply convexity in the parameters of
  a network producing them. The cumulant calculation is the
  exponential-family identity of SYNOPSIS101, item 4.

* **34. Gaussian-process posterior prediction.** Let a zero-mean Gaussian
  process have kernel $k$, and observe
  $y_i=f(x_i)+\varepsilon_i$ with independent $N(0,\sigma^2)$ noise,
  $\sigma^2>0$. For $K=(k(x_i,x_j))$ and
  $k_x=(k(x_i,x))_i$, the posterior mean and covariance are
  $$m(x)=k_x^\top(K+\sigma^2I)^{-1}y,$$
  $$k_{\mathrm{post}}(x,x')
  =k(x,x')-k_x^\top(K+\sigma^2I)^{-1}k_{x'}.$$
  Future noisy-response variance adds $\sigma^2$. The posterior mean
  is kernel ridge regression with penalty $\lambda=\sigma^2/n$ under
  the averaged squared-loss convention. This equality of means does
  not identify a frequentist confidence band with a posterior band.

### Capacity, depth, and symmetry

A **feedforward network** of depth $L$ with widths $N_0=d,N_1,\ldots,N_L$
alternates affine maps with a coordinatewise activation on the $L-1$ hidden
layers; $P$ denotes its number of weights and biases. An activation is
**piecewise polynomial** when the line splits into finitely many intervals on
each of which it is a polynomial. The ReLU $\max(u,0)$ is piecewise linear
and positively homogeneous.

* **35. Capacity of network classes.** For a fixed piecewise-polynomial
  activation there is a constant $c$ such that, for every depth $L$ and
  every architecture with $P$ parameters, the sign classifiers of that
  architecture have VC dimension at most $c(PL\log P+PL^2)$. With the
  fundamental theorem of item 1, fixed-depth classes thus
  have uniform deviations of order $\sqrt{P\log P/n}$ up to confidence
  terms. For bias-free networks on the unit ball, with a
  $1$-Lipschitz positively homogeneous activation and every weight matrix
  of Frobenius norm at most $C$, the Rademacher complexity of the
  real-valued class is at most $2^{L-1}C^L/\sqrt n$, independent of the
  widths. Parameter-count bounds are vacuous when the parameters outnumber
  the samples; norm bounds instead depend on the size of the trained
  weights.

* **36. Approximation rates of deep ReLU networks.** Let $k\ge2$,
  $p\in[1,\infty]$, $s\in[0,1]$, and $B>0$, and let the activation be
  piecewise linear with at least one breakpoint. There is a constant $c$
  such that for each $\varepsilon\in(0,1/2)$ a single architecture with at
  most $c\varepsilon^{-d/(k-s)}\log(1/\varepsilon)$ parameters
  approximates every $g$ with $\|g\|_{W^{k,p}((0,1)^d)}\le B$ within
  $\varepsilon$ in the $W^{s,p}((0,1)^d)$ norm. For $p=\infty$ and $s=0$
  this is Yarotsky's theorem. The depth of the architectures must grow as
  $\varepsilon\to0$; the exponent $d/k$ is that of classical
  approximation and still deteriorates with the dimension. Item 29 is the
  corresponding statistical statement for compositional classes.

* **37. Depth separation.** For the ReLU, logistic, or Heaviside
  activation there are $c,C>0$ such that for each $d\ge C$ there exist a
  probability measure $\mu$ on $\mathbb R^d$ and a function $g$, bounded by
  $2$ and computed by a network with two hidden layers of width at most
  $Cd^5$ and weights at most $Cd^C$, such that every network with one
  hidden layer of width $n\le ce^{cd}$ has $L^2(\mu)$ distance at least $c$
  from $g$ (Eldan and Shamir). If $g\in C^2([0,1]^d)$ is not affine and
  $L\ge2$, there is $c>0$ such that, for every $\varepsilon\in(0,1)$, every
  ReLU network with $L-1$ hidden layers and at most
  $c\varepsilon^{-1/(2(L-1))}$ neurons has uniform error at least
  $\varepsilon$ on $[0,1]^d$ (Yarotsky). These are approximation lower
  bounds at fixed depth; they do not say that training finds the deeper
  approximant.

The **cyclic shift** $S$ on $\mathbb R^n$ moves each coordinate one place
to the right, cyclically. A matrix is **circulant** when it is a polynomial
in $S$; it acts as a cyclic convolution. A map $F$ on feature matrices
$X\in\mathbb R^{n\times d}$ is **permutation equivariant** if
$F(PX)=PF(X)$ for every $n\times n$ permutation matrix $P$. **Self-attention**
with query, key, and value matrices $W_Q,W_K\in\mathbb R^{d\times d_k}$
and $W_V\in\mathbb R^{d\times d_v}$ is
$$\mathop{\mathrm{Att}}(X)=\mathop{\mathrm{softmax}}
\bigl(XW_QW_K^\top X^\top/\sqrt{d_k}\bigr)XW_V,$$
with the softmax of item 33 applied to each row.

* **38. Equivariant linear layers and self-attention.** A matrix commutes
  with $S$ if and only if it is circulant; all circulant matrices are
  diagonalized by the discrete Fourier basis. For $n\ge2$, the linear maps
  $F:\mathbb R^n\to\mathbb R^n$ with $F(Px)=PF(x)$ for every permutation
  matrix are exactly $aI+b\mathbf 1\mathbf 1^\top$. On feature matrices
  the linear permutation-equivariant maps are
  $X\mapsto X\Theta_1+n^{-1}\mathbf 1\mathbf 1^\top X\Theta_2$.
  Self-attention satisfies $\mathop{\mathrm{Att}}(PX)=P\mathop{\mathrm{Att}}(X)$;
  it is a message-passing map, as in item 46, on the complete graph with
  data-dependent weights. Order enters a transformer only through
  positional encodings added to $X$, which break this equivariance.
  Exact translation equivariance of a convolutional layer on a finite grid
  requires periodic boundary conditions; padding and strided pooling
  break it.

### Random initialization and implicit bias

Consider a fully connected network whose biases are independent
$N(0,C_b)$ and whose weights into layer $\ell+1$ are independent
$N(0,C_W/N_\ell)$, with $C_b\ge0$ and $C_W>0$. Write $z^{(\ell)}(x)$ for the
preactivation vector of layer $\ell$ at input $x\in\mathbb R^d$.

* **39. Gaussian-process limit at initialization.** Let the activation
  $\sigma$ be continuous with $|\sigma(u)|\le a+b|u|$. Fix the depth and
  finitely many inputs, and let the hidden widths tend to infinity. Then
  the coordinates of $z^{(\ell)}$ converge jointly in distribution to
  independent copies of a centered Gaussian process with covariance
  $K^{(\ell)}$, where $K^{(1)}(x,x')=C_b+C_W\langle x,x'\rangle/d$ and
  $$K^{(\ell+1)}(x,x')=C_b+C_W\,\mathbb E[\sigma(U)\sigma(U')],$$
  with $(U,U')$ centered Gaussian of covariance given by $K^{(\ell)}$ on
  $\{x,x'\}$. Bayesian regression with this network prior and Gaussian
  noise becomes, in the limit, the Gaussian-process prediction of item 34
  with kernel $K^{(L)}$. At finite width the law is non-Gaussian, with
  corrections of order the inverse width. The tangent kernel of item 30 is
  a different kernel, which governs training rather than the prior.

* **40. Implicit bias of gradient descent.** For
  $\frac12\|X\theta-y\|_2^2$ with $X\in\mathbb R^{n\times p}$, gradient
  descent with constant step $0<\eta<2/\lambda_{\max}(X^\top X)$ from
  $\theta_0$ converges to $X^+y+(I-X^+X)\theta_0$. From $\theta_0=0$ this
  is the minimum-norm least-squares solution, which is the interpolant of
  item 31 when $p>n$ and $X$ has full row rank. For linearly separable data
  $(x_i,y_i)$, the logistic loss, and gradient descent with a sufficiently
  small constant step from any initialization, $\|\theta_t\|\to\infty$ and
  $\theta_t/\|\theta_t\|\to\hat\theta/\|\hat\theta\|$, where $\hat\theta$
  minimizes $\|\theta\|_2$ subject to $y_i\langle\theta,x_i\rangle\ge1$
  for all $i$ (Soudry, Hoffer, Nacson, Gunasekar, and Srebro). The
  directional convergence is only logarithmic in $t$. In the kernel limit
  of item 30, squared-loss training converges to the minimum-norm
  interpolant in the reproducing kernel Hilbert space of the limiting
  kernel, up to a term from the random initial function. Analogous
  statements for deep nonlinear networks need additional assumptions.

### Networks and graph representation learning

In the **symmetric two-group stochastic block model**, $n$ vertices are
split equally at random into two groups, edges are independent, and the
probability of an edge is $p$ inside a group and $q$ between groups.
**Exact recovery** means that a labeling agrees with the planted partition,
or with its global flip, with probability tending to one.

* **41. Exact recovery.** For fixed $a,b>0$ in
  $p=a\log n/n$, $q=b\log n/n$, exact recovery is possible, and
  achievable in polynomial time, if and only if
  $$(\sqrt a-\sqrt b)^2\ge2.$$
  The equality case is included for strictly positive $a,b$.
  With $b=0$ and $a>0$, recovery instead requires $a>2$;
  the equality case has a connectivity obstruction. Thus the boundary
  cannot be described by a single strict inequality for all parameters.

**Weak recovery** means that a labeling, after the better global sign flip,
has correlation with the planted partition bounded away from zero with
probability tending to one.
**Consistent distinction** from an Erdős–Rényi model means the existence
of graph tests whose two error probabilities tend to zero. Contiguity
is a comparison of sequences of laws that can preclude such distinction;
it is not itself the definition of a recovery task.

* **42. Kesten–Stigum threshold.** For fixed $a,b>0$ in the
  constant-degree regime $p=a/n$, $q=b/n$, weak recovery is possible
  if and only if $(a-b)^2>2(a+b)$, and is achievable efficiently above
  that threshold. Strictly below it, the graph law is mutually contiguous
  to the corresponding Erdős–Rényi law, so consistent distinction is
  impossible. Weak recovery is impossible also at equality. The
  two-group result does not extend unchanged to arbitrarily many groups.

A **graphon** is a symmetric measurable function
$W:[0,1]^2\to[0,1]$. The graphon model draws latent variables
$U_i$ independently from the uniform law on $[0,1]$ and, conditionally on
the latent variables, includes each edge $\{i,j\}$ independently with
probability $W(U_i,U_j)$.

* **43. Aldous–Hoover theorem for graphs.** A simple undirected random
  graph on the positive integers whose law is invariant under finite
  vertex permutations is a mixture of graphon models. Two graphons
  induce the same random-graph law precisely when they are weakly
  isomorphic: they have equal pullbacks almost everywhere by suitable
  measure-preserving maps from a common atomless probability space.
  One need not be obtained from the other by a single invertible
  measure-preserving relabeling of $[0,1]$. The sequence analogue is
  de Finetti's theorem, CKMA SYNOPSIS06, item 55.

The **one-dimensional Weisfeiler–Leman algorithm** colors vertices by
iterating the multiset of colors in the neighborhood. A **message-passing
network** updates each vertex feature from the multiset, or the sum, of the
features of its neighbors.

* **44. Weisfeiler–Leman bound.** A message-passing network with shared
  updates and permutation-invariant neighborhood aggregation cannot
  distinguish initially equally featured graphs that one-dimensional
  Weisfeiler–Leman refinement does not distinguish. At depth $L$ the
  analogous comparison uses $L$ refinement rounds. With injective
  multiset aggregation, updates, and graph readout, the bound can be
  attained on the prescribed feature and multiset domain. Standard
  graph-isomorphism-network constructions use countable feature domains
  and bounded multiset sizes; unrestricted real-valued sum aggregation
  is not automatically injective.

### Symmetry and graph signal

* **45. Population eigenspaces of the block model.** For a balanced
  two-group model with label vector $s\in\{-1,1\}^n$ and $1^\top s=0$,
  the conditional adjacency expectation is
  $$\mathbb E[A\mid s]=\tfrac{p+q}{2}11^\top
  +\tfrac{p-q}{2}ss^\top-pI.$$
  Its eigenvectors $1$ and $s$ have eigenvalues
  $n(p+q)/2-p$ and $n(p-q)/2-p$, respectively; every orthogonal
  direction has eigenvalue $-p$. This identifies the population signal.
  Consistent empirical eigenvector recovery additionally requires
  noise and spectral-gap control. In sparse graphs, population
  separation alone does not make the unregularized adjacency method
  attain the thresholds of items 41 and 42.

* **46. Permutation equivariance.** For a shared message-passing map
  $F$ with permutation-invariant neighborhood aggregation and a vertex
  permutation matrix $P$,
  $$F(PAP^\top,PX)=PF(A,X).$$
  A permutation-invariant pooling of the resulting node features is
  a graph invariant. Equivariance is a constraint on relabeling, while
  the Weisfeiler–Leman theorem of item 44 bounds distinguishing power;
  one does not imply that the other is maximal.

### Random graphs and spectral recovery

The **Erdős–Rényi graph** $G(n,p)$ includes each of the $\binom n2$
possible edges independently with probability $p$.

* **47. Phase transitions of the Erdős–Rényi graph.** Let $p=c/n$ with a
  fixed $c>0$. If $c<1$, then with probability tending to one every
  component has $O(\log n)$ vertices. If $c>1$, the largest component
  $C_1$ satisfies $|C_1|/n\to\zeta_c$ in probability, where
  $\zeta_c\in(0,1)$ is the positive solution of $1-\zeta=e^{-c\zeta}$,
  and with probability tending to one every other component has
  $O(\log n)$ vertices. Here $\zeta_c$ is the survival probability of a
  Galton–Watson process with Poisson($c$) offspring, CKMA SYNOPSIS06,
  item 65. For $p=(\log n+x_n)/n$, the graph is connected with
  probability tending to one if $x_n\to\infty$, and has isolated vertices
  with probability tending to one if $x_n\to-\infty$; for fixed $x_n=x$
  the probability of connectivity tends to $\exp(-e^{-x})$. Thus
  connectivity and the disappearance of isolated vertices share the sharp
  threshold $\log n/n$, whereas the giant component appears at average
  degree one.

For the two-group model of item 45 with $p>q$, let $D$ be the
$n\times n$ matrix with entries $p$ within and $q$ between groups,
diagonal included, let $R=A-D$, and put $\mu=\min\{q,(p-q)/2\}$.
**Spectral clustering** labels each vertex by the sign of its coordinate in
a unit eigenvector for the second largest eigenvalue of $A$.

* **48. Spectral clustering of the block model.** If $\mu>0$, then up to
  a global flip spectral clustering misclassifies at most
  $8\|R\|_{\mathrm{op}}^2/(\mu^2n)$ vertices. This is a deterministic
  consequence of the Davis–Kahan theorem, CKMA SYNOPSIS13, item 67, and
  the population eigenvectors of item 45. Since
  $\|R\|_{\mathrm{op}}\le C\sqrt n$ with probability at least $1-4e^{-n}$,
  at most $C/\mu^2$ vertices are misclassified, a bounded number when
  $p$ and $q$ are fixed. With $\bar d=n(p+q)/2$, the matrix Bernstein
  inequality, CKMA SYNOPSIS07, item 44, gives
  $\mathbb E\|R\|_{\mathrm{op}}\le C(\sqrt{\bar d\log n}+\log n)$; hence
  the misclassified fraction tends to zero in probability when
  $\bar d\ge\log n$ and $n^2\mu^2/(\bar d\log n)\to\infty$. These
  conditions are stronger than the thresholds of items 41 and 42, which
  require other methods.

<a id="synopsis-107b"></a>

## 107B. Bandits, Reinforcement Learning, Privacy, Fairness, and Distribution Shift

### Bandits and reinforcement learning

A **stochastic bandit** has $K$ arms with reward laws $\nu_1,\ldots,\nu_K$
in a one-parameter exponential family. Write $\Delta_k$ for the gap between
the mean of arm $k$ and the optimal mean, and write
$\mathop{\mathrm{kl}}(\nu_k,\nu^\star)$ for the Kullback–Leibler divergence
between the reward law of arm $k$ and the optimal reward law.
Assume a regular one-parameter family with a continuous strictly increasing
mean parameter, a unique optimal arm, and optimal mean in the interior
of the mean domain. The
**regret** after $n$ plays is the expected difference between $n$ times the
optimal mean and the sum of the observed rewards.

* **49. Lai–Robbins lower bound.** For a uniformly efficient policy,
  meaning regret $o(n^\alpha)$ at every parameter configuration for every
  $\alpha>0$, the regular exponential-family bandit satisfies
  $$\liminf_{n\to\infty}\frac{\mathop{\mathrm{regret}}(n)}{\log n}
  \ge\sum_{k:\Delta_k>0}\frac{\Delta_k}
  {\mathop{\mathrm{kl}}(\nu_k,\nu^\star)}.$$
  More generally the denominator is the infimum divergence from $\nu_k$
  to an admissible arm law with mean strictly greater than the optimal
  mean. In the stated regular family, interiority and continuity reduce
  that infimum to the displayed divergence.

* **50. Upper confidence bounds.** For independent reward streams
  supported on $[0,1]$, the UCB1 policy, initialized by sampling each arm,
  has expected regret
  $$O\left(\sum_{k:\Delta_k>0}\frac{\log n}{\Delta_k}
  +\sum_{k:\Delta_k>0}\Delta_k\right).$$
  For fixed positive gaps this gives logarithmic growth. It matches the
  logarithmic order of item 49 in applicable exponential-family models,
  rather than its exact leading divergence constant.

* **51. Thompson sampling and the Gittins index.** For Bernoulli arms
  with means in $(0,1)$ and independent beta priors with positive
  parameters, Thompson sampling attains the asymptotic regret constant
  of item 49. Extensions require specified likelihood and prior
  regularity. For a Bayesian bandit with independent arms, each arm's
  state frozen when unplayed, and a common geometric discount factor,
  a Gittins index policy maximizes expected discounted reward. The
  index theorem concerns discounted Bayesian optimality, a different
  criterion from asymptotic frequentist regret.

* **52. Adversarial bandits.** For an oblivious sequence of losses
  in $[0,1]$ on $K\ge2$ arms, Exp3 with a horizon-tuned exploration
  parameter has expected regret $O(\sqrt{KT\log K})$ against the best
  fixed arm in hindsight. Only the selected loss is observed; importance
  weighting estimates the other arms' losses without bias.
  The full-information comparator is item 5.

Consider a finite Markov decision process with nonempty finite action
sets, discount $\gamma\in(0,1)$, and bounded rewards. The
**Bellman optimality operator** on action-value functions is
$$(TQ)(s,a)
=\mathbb E\Bigl[R+\gamma\max_{a'}Q(S',a')\Bigm| S=s,\,A=a\Bigr].$$

* **53. Contraction of the Bellman operator.** The operator $T$ is a
  $\gamma$-contraction of the supremum norm. It has a unique fixed point
  $Q^\star$. Every policy that is greedy for $Q^\star$ is optimal, and
  value iteration converges to $Q^\star$ geometrically with ratio $\gamma$.

On a finite state-action space the **tabular $Q$-learning** update replaces
$Q(s,a)$ by
$(1-\alpha)Q(s,a)+\alpha\bigl(r+\gamma\max_{a'}Q(s',a')\bigr)$ when $(s,a)$
is visited and a reward $r$ and a next state $s'$ are observed.

* **54. Convergence of $Q$-learning.** In the finite discounted model,
  assume each observed transition and reward has the specified conditional
  Markov law, and every state-action pair is visited infinitely often.
  For its own update sequence, require $0\le\alpha_t(s,a)\le1$,
  $\sum_t\alpha_t(s,a)=\infty$, and
  $\sum_t\alpha_t(s,a)^2<\infty$. Then $Q_t\to Q^\star$ almost surely.
  The infinite-visitation and step-size conditions apply to the actual
  visits to each pair, rather than merely to a global time sequence.

### Policy evaluation and policy-dependent distributions

For a policy $\pi$ in the finite discounted model, let $P_\pi$ and
$r_\pi$ be its transition matrix and expected one-step reward vector.

* **55. Policy evaluation and improvement.** The policy value is
  $$V^\pi=(I-\gamma P_\pi)^{-1}r_\pi
  =\sum_{t\ge0}\gamma^tP_\pi^t r_\pi.$$
  If $\pi'$ selects maximizing actions for
  $r(s,a)+\gamma\sum_{s'}P(s'\mid s,a)V^\pi(s')$, then
  $V^{\pi'}\ge V^\pi$ at every state. Policy iteration with a tie rule
  retaining current maximizing actions terminates after finitely many
  strict policy improvements at an optimal deterministic policy.

Fix an initial distribution $\mu$ and write
$J(\pi)=\mathbb E_{\mu,\pi}\sum_{t\ge0}\gamma^tR_t$.
The normalized **discounted occupancy measure** is
$d_\mu^\pi=(1-\gamma)\sum_{t\ge0}\gamma^t\mathop{\mathrm{Law}}_{\mu,\pi}(S_t)$.
The **advantage** is $A^\pi(s,a)=Q^\pi(s,a)-V^\pi(s)$.

* **56. Performance difference identity.** For any two policies,
  $$J(\pi')-J(\pi)=\frac1{1-\gamma}
  \mathbb E_{S\sim d_\mu^{\pi'},\,A\sim\pi'(\cdot\mid S)}
  [A^\pi(S,A)].$$
  The state distribution on the right is that of the new policy.
  Replacing it by an old-policy empirical distribution without a
  justified approximation or reweighting changes the identity.

* **57. Policy gradient.** For a differentiable policy family with
  strictly positive action probabilities and parameter-independent
  transitions, rewards, and initial distribution,
  $$\nabla_\theta J(\pi_\theta)
  =\frac1{1-\gamma}\mathbb E_{d_\mu^{\pi_\theta},\pi_\theta}
  [\nabla_\theta\log\pi_\theta(A\mid S)Q^{\pi_\theta}(S,A)].$$
  Any action-independent baseline $b(S)$ may be subtracted from $Q$
  without changing this expectation. Finite state and action spaces,
  bounded rewards, and local differentiability justify the
  discounted differentiation. Variance and bias of a fitted critic
  are additional questions.

### Optimal policies, planning, and sample complexity

* **58. Stationary optimal policies and linear programming.** In the
  finite discounted model of item 53, let $V^\star$ and $Q^\star$ be the
  suprema of $V^\pi$ and $Q^\pi$ over all history-dependent randomized
  policies. Some stationary deterministic policy attains both at every
  state and action; every policy greedy for $Q^\star$ does. The function
  $V^\star$ is the componentwise smallest $V$ satisfying
  $$V(s)\ge r(s,a)+\gamma\sum_{s'}P(s'\mid s,a)V(s')
  \quad\text{for all }(s,a),$$
  and for an initial law $\mu$ of full support it is the unique minimizer
  of $\sum_s\mu(s)V(s)$ over this set. The state-action occupancy measures
  $d^\pi_\mu(s,a)=(1-\gamma)\sum_t\gamma^tP_{\mu,\pi}(S_t=s,A_t=a)$ of
  stationary policies are exactly the nonnegative $d$ with
  $$\sum_ad(s,a)=(1-\gamma)\mu(s)
  +\gamma\sum_{s',a'}P(s\mid s',a')d(s',a')\quad\text{for all }s,$$
  and $J(\pi)=(1-\gamma)^{-1}\sum_{s,a}d^\pi_\mu(s,a)r(s,a)$. Maximizing
  this linear function over the polytope is the dual linear program. If
  $\mu$ has full support and $d^\star$ is optimal, then
  $\pi(a\mid s)=d^\star(s,a)/\sum_{a'}d^\star(s,a')$ is optimal.

In the **generative model** the rewards $r(s,a)\in[0,1]$ are known and, for
each state-action pair, $N$ independent next states are drawn from
$P(\cdot\mid s,a)$. Let $\hat P$ be the empirical transition law, and let
hats denote quantities of the model with $\hat P$ in place of $P$.

* **59. Sample complexity with a generative model.** For every stationary
  policy $\pi$,
  $$Q^\pi-\hat Q^\pi=\gamma(I-\gamma\hat P^\pi)^{-1}(P-\hat P)V^\pi,$$
  with $\hat P^\pi$ the empirical state-action transition matrix under
  $\pi$; hence
  $\|Q^\pi-\hat Q^\pi\|_\infty\le\gamma(1-\gamma)^{-1}
  \|(P-\hat P)V^\pi\|_\infty$. There is an absolute constant $c$ such
  that, if $\varepsilon\le1$, $\delta\in(0,1)$, and
  $$N\ge\frac{c\log(c|S||A|/\delta)}{(1-\gamma)^3\varepsilon^2},$$
  then with probability at least $1-\delta$ the optimal function of the
  empirical model satisfies $\|\hat Q^\star-Q^\star\|_\infty\le\varepsilon$.
  If $\varepsilon\le(1-\gamma)^{-1/2}$, a sample size of the same order
  makes an optimal policy $\hat\pi$ of the empirical model satisfy
  $\|Q^{\hat\pi}-Q^\star\|_\infty\le\varepsilon$. Conversely, for some
  class of models every procedure that is $\varepsilon$-accurate for
  $Q^\star$ with probability $1-\delta$ needs at least
  $c|S||A|\log(c/\delta)/((1-\gamma)^3\varepsilon^2)$ samples in total.
  A crude argument through uniform model accuracy gives the worse factor
  $|S|^2|A|(1-\gamma)^{-4}$; the sharp exponent uses the variance of
  $V^\star$ under the transitions.

For a fixed policy, let the states form an irreducible aperiodic chain on
$\{1,\ldots,n\}$ with transition matrix $P$, stationary law $\varpi$,
one-step costs $g(i,j)$, and value $V$. Let $\Phi$ be an $n\times K$ feature
matrix of full column rank, with rows $\phi(i)^\top$. **TD($\lambda$)**, for
$\lambda\in[0,1]$, runs along one trajectory $(i_t)$ with
$d_t=g(i_t,i_{t+1})+\gamma\phi(i_{t+1})^\top r_t-\phi(i_t)^\top r_t$,
eligibility $z_t=\sum_{k\le t}(\gamma\lambda)^{t-k}\phi(i_k)$, and update
$r_{t+1}=r_t+\alpha_td_tz_t$. Let $\Pi$ be the orthogonal projection onto
the range of $\Phi$ in the $\varpi$-weighted norm $\|\cdot\|_\varpi$.

* **60. Temporal differences with linear features.** If the steps are
  positive, deterministic, $\sum_t\alpha_t=\infty$, and
  $\sum_t\alpha_t^2<\infty$, then $r_t\to r^\star$ almost surely, where
  $\Phi r^\star$ is the unique fixed point of $\Pi T^{(\lambda)}$, with
  $T^{(\lambda)}=(1-\lambda)\sum_{m\ge0}\lambda^mT^{m+1}$ for $\lambda<1$,
  $T^{(1)}$ the constant map to $V$, and $T$ the policy Bellman operator. Moreover
  $$\|\Phi r^\star-V\|_\varpi\le\frac{1-\gamma\lambda}{1-\gamma}
  \|\Pi V-V\|_\varpi.$$
  For $\lambda=1$ the limit is the best approximation $\Pi V$. The
  argument uses that $P$ is nonexpansive in $\|\cdot\|_\varpi$; sampling
  states from another law, or nonlinear parameterizations, can make the
  iteration diverge (Tsitsiklis and Van Roy).

For a finite discounted model with rewards in $[0,1]$, the **softmax
policy** with parameters $\theta_{s,a}$ is
$\pi_\theta(a\mid s)\propto e^{\theta_{s,a}}$. With start law $\rho$, the
**natural policy gradient** update is
$\theta^{(t+1)}=\theta^{(t)}+\eta F_\rho(\theta^{(t)})^+\nabla_\theta J(\pi_{\theta^{(t)}})$,
where $F_\rho(\theta)$ is the Fisher information of $\pi_\theta(\cdot\mid S)$
averaged over $S\sim d_\rho^{\pi_\theta}$ and $^+$ is the Moore–Penrose
inverse.

* **61. Convergence of natural policy gradient.** For the softmax policy
  the update is
  $\pi^{(t+1)}(a\mid s)\propto
  \pi^{(t)}(a\mid s)\exp\bigl(\eta A^{(t)}(s,a)/(1-\gamma)\bigr)$, with
  $A^{(t)}$ the advantage of $\pi^{(t)}$. From $\theta^{(0)}=0$ and any
  step $\eta>0$, for every $T\ge1$,
  $$J^\star(\rho)-J(\pi^{(T)})\le\frac{\log|A|}{\eta T}
  +\frac1{(1-\gamma)^2T},$$
  where $J^\star(\rho)$ is the optimal value from $\rho$. The bound is free
  of $|S|$ and of distribution-mismatch coefficients. It assumes exact
  advantages; sampled versions add estimation errors. The ordinary
  softmax policy gradient of item 57 converges to optimality for a
  small enough step when its start law has full support, but its
  worst-case rate can be very slow.

### Minimax and linear bandits

* **62. Minimax regret of finite-armed bandits.** For $K\ge2$ arms and a
  horizon $n>K/(4\log(4/3))$, every strategy, possibly randomized, has
  regret at least
  $$\frac{\sqrt2-1}{\sqrt{32\log(4/3)}}\sqrt{nK}$$
  on some instance with independent Bernoulli rewards. The hard instances
  have all arms of mean $1/2$ except one, chosen uniformly at random, whose
  mean is shifted by an amount of order $\sqrt{K/n}$. Since UCB attains
  $O(\sqrt{Kn\log n})$ uniformly over rewards in $[0,1]$, and Exp3 the
  bound of item 52 against oblivious adversaries, these orders are
  minimax up to logarithmic factors. Item 49 instead concerns fixed
  instances as $n\to\infty$.

In a **linear bandit** the learner picks $x_t$ in a decision set
$\mathcal D\subseteq\mathbb R^d$ and observes $\langle\mu^\star,x_t\rangle+\eta_t$.
The regret is $R_T=\sum_{t<T}(\max_{x\in\mathcal D}\langle\mu^\star,x\rangle
-\langle\mu^\star,x_t\rangle)$. **LinUCB** forms the ridge estimate
$\hat\mu_t$ with $\Sigma_t=\lambda I+\sum_{\tau<t}x_\tau x_\tau^\top$, and
chooses $x_t$ maximizing
$\langle\hat\mu_t,x\rangle+\sqrt{\beta_t}\,(x^\top\Sigma_t^{-1}x)^{1/2}$.

* **63. Self-normalized confidence and LinUCB.** Let $(\mathcal F_t)$ be a
  filtration, let real $\varepsilon_t$ be $\mathcal F_t$-measurable,
  conditionally centered and $\sigma$-sub-Gaussian given
  $\mathcal F_{t-1}$, and let $X_t\in\mathbb R^d$ be
  $\mathcal F_{t-1}$-measurable. For positive definite $V_0$ and
  $V_t=V_0+\sum_{i\le t}X_iX_i^\top$, with probability at least $1-\delta$,
  simultaneously for all $t\ge1$,
  $$\Bigl\|\sum_{i\le t}X_i\varepsilon_i\Bigr\|_{V_t^{-1}}^2
  \le2\sigma^2\log\frac{\det(V_t)^{1/2}\det(V_0)^{-1/2}}{\delta}$$
  (Abbasi-Yadkori, Pál, and Szepesvári). If
  $|\langle\mu^\star,x\rangle|\le1$ and $\|x\|_2\le B$ on $\mathcal D$,
  $\|\mu^\star\|_2\le W$, and the noise satisfies these conditions, then
  LinUCB with $\lambda=\sigma^2/W^2$ and
  $\beta_t=\sigma^2\bigl(2+4d\log(1+tB^2W^2/(d\sigma^2))+8\log(4/\delta)\bigr)$
  has, with probability at least $1-\delta$ and for all $T$,
  $$R_T\le c\sigma\sqrt T\Bigl(d\log\bigl(1+TB^2W^2/(d\sigma^2)\bigr)
  +\log(4/\delta)\Bigr).$$
  This is $\tilde O(d\sqrt T)$, with no dependence on $|\mathcal D|$. A
  lower bound of order $d\sqrt T$ holds for $T\ge\max\{256,d^2/16\}$.

### Privacy, fairness, and distribution shift

Data sets are **neighboring** when one is obtained from the other by
changing a single record. A mechanism $M$ is **$\varepsilon$-differentially
private** when
$P(M(D)\in A)\le e^\varepsilon P(M(D')\in A)$ for every measurable $A$ and
every neighboring pair. It is **$(\varepsilon,\delta)$-differentially
private** when the same comparison holds with an additive $\delta$ on the
right-hand side. The **$\ell^1$ sensitivity** of a query
$f$ is the supremum of $\|f(D)-f(D')\|_1$ over neighboring pairs.

* **64. Laplace mechanism.** If $f$ takes values in $\mathbb R^k$ and has
  $\ell^1$ sensitivity $\Delta>0$, the mechanism that adds an independent
  $\mathop{\mathrm{Lap}}(\Delta/\varepsilon)$ random variable to each
  coordinate is $\varepsilon$-differentially private. The density of
  $\mathop{\mathrm{Lap}}(b)$ on the line is $(1/(2b))e^{-|t|/b}$, so
  $b=\Delta/\varepsilon$ for $\Delta>0$ and $\varepsilon>0$.
  A zero-sensitivity query can be released directly. This is
  Theorem 3.6 of Dwork and Roth.

* **65. Composition.** The adaptive composition of $k$ mechanisms that are
  $(\varepsilon_i,\delta_i)$-differentially private is
  $\bigl(\sum_i\varepsilon_i,\sum_i\delta_i\bigr)$-differentially private.
  If each mechanism is $(\varepsilon,\delta)$-differentially private, then
  for every $\delta'\in(0,1)$ the composition is $(\varepsilon',k\delta+\delta')$-differentially
  private with
  $$\varepsilon'
  =\sqrt{2k\log(1/\delta')}\,\varepsilon
  +k\varepsilon(e^\varepsilon-1).$$
  These are Theorem 3.16 and Theorem 3.20 of Dwork and Roth.

* **66. Private mean estimation.** For independent observations
  supported on $[-1,1]$ and $0<\varepsilon\le1$, the minimax squared
  error under noninteractive $\varepsilon$-local differential privacy is
  of order $\min\{1,1/(n\varepsilon^2)\}$. Here each individual's
  release kernel must obey the privacy inequality for every pair of
  possible input values. Under central pure $\varepsilon$-privacy,
  where a mechanism sees the whole sample, the minimax error is of order
  $\min\{1,n^{-1}+(n\varepsilon)^{-2}\}$.
  Adding Laplace noise to the bounded sample mean attains the central
  order. Boundedness of the mean alone, without controlling the
  observation laws, does not justify these uniform rates.

A score $S$ satisfies **separation**, or equalized odds, when
$S\perp A\mid Y$. It satisfies **sufficiency** when $Y\perp A\mid S$.
For $S\in[0,1]$, calibration within groups is the stronger numerical
condition $P(Y=1\mid S,A)=S$ almost surely, which implies sufficiency.

* **67. Incompatibility of calibration and equalized odds.** Let $Y,A$
  be binary, with $P(Y=y,A=a)>0$ for all four cells and unequal group
  base rates. If a score satisfies both separation and sufficiency,
  it must determine $Y$ almost surely. Thus a score leaving unresolved
  label uncertainty cannot satisfy both conditions; perfect prediction
  is an exception. In particular, unequal base rates rule out simultaneous
  within-group calibration and separation for an imperfect score.
  Group-dependent randomized thresholding can give a released binary
  prediction equalized odds, possibly at substantial cost in accuracy.

Let $\mathcal H$ be a class of binary classifiers. The
**$\mathcal H\Delta\mathcal H$-divergence** is
$d_{\mathcal H\Delta\mathcal H}(P,Q)
=2\sup_{h,h'\in\mathcal H}|P(h\ne h')-Q(h\ne h')|$.
It is twice the integral probability metric of
[SYNOPSIS108](SYNOPSIS108.md) for these disagreement indicators.

* **68. Domain adaptation and covariate shift.** For binary
  classification and every $h\in\mathcal H$,
  $$R_T(h)\le R_S(h)+\tfrac12d_{\mathcal H\Delta\mathcal H}(P_S^X,P_T^X)
  +\inf_{g\in\mathcal H}(R_S(g)+R_T(g)).$$
  Under covariate shift, the conditional response law given $X$ is
  unchanged. If $P_T^X\ll P_S^X$ and $w=dP_T^X/dP_S^X$, then for
  an integrable loss $R_T(f)=\mathbb E_S[w(X)L(Y,f(X))]$.
  This identifies target risk; accuracy of its weighted empirical
  estimate also depends on moments of the density ratio.

### Privacy mechanisms and weighted inference

* **69. Post-processing and groups.** Any measurable randomized
  post-processing of an $(\varepsilon,\delta)$-private release, using
  only the release and fresh randomness, is again
  $(\varepsilon,\delta)$-private. For pure privacy, if datasets differ
  in at most $k$ records, repeated application of the neighboring-data
  inequality gives a factor $e^{k\varepsilon}$. These statements require
  no independence between the output coordinates.

* **70. Gaussian mechanism.** Let a vector query have Euclidean
  sensitivity $\Delta_2$. For $0<\varepsilon<1$, $0<\delta<1$,
  and $c>0$ with $c^2>2\log(1.25/\delta)$, adding independent
  $N(0,\sigma^2)$ coordinates with $\sigma\ge c\Delta_2/\varepsilon$
  is $(\varepsilon,\delta)$-differentially private. The norm used
  for sensitivity is part of the theorem; the Laplace mechanism of
  item 64 instead uses $\ell^1$ sensitivity.

* **71. Exponential mechanism.** For a fixed finite output set
  $\mathcal R$, let a utility $u(D,r)$ have sensitivity $\Delta u>0$
  uniformly over $r$. Drawing an output with probability proportional
  to $\exp(\varepsilon u(D,r)/(2\Delta u))$ is
  $\varepsilon$-differentially private. With probability at least
  $1-\eta$, the released utility is within
  $$\frac{2\Delta u}{\varepsilon}
  (\log|\mathcal R|+\log(1/\eta))$$
  of the maximum. The output set must not itself reveal the data.

* **72. Randomized response and a private mean.** For $\varepsilon>0$, put
  $\rho_\varepsilon=(e^\varepsilon-1)/(e^\varepsilon+1)$.
  For an individual input $x\in[-1,1]$, release $Z\in\{-1,1\}$ with
  $$P(Z=1\mid x)=\frac{1+\rho_\varepsilon x}{2}.$$
  This is $\varepsilon$-locally private and satisfies
  $\mathbb E[Z\mid x]=\rho_\varepsilon x$. For independent individuals
  and independent randomization, $\sum_iZ_i/(n\rho_\varepsilon)$ is
  unbiased for the population mean, with variance at most
  $1/(n\rho_\varepsilon^2)$. Clipping to $[-1,1]$ cannot increase
  squared error and gives the order in item 66 for $0<\varepsilon\le1$.

* **73. Accuracy under bounded importance weights.** Under covariate
  shift, suppose the known density ratio satisfies $0\le w\le B$,
  and the loss is in $[0,1]$. For a fixed predictor, or conditionally
  on independent training data, the weighted mean of $n$ independent
  source validation losses is unbiased for target risk and has
  variance at most $B/n$, since $\mathbb E_Sw=1$.
  A Bernstein bound gives, with probability at least $1-\delta$,
  $$|\hat R_T-R_T|\le
  \sqrt{\frac{2B\log(2/\delta)}n}
  +\frac{2B\log(2/\delta)}{3n}.$$
  Estimating the ratio or selecting the predictor on those same
  validation observations requires further error control.

### Threshold queries and local contraction

**AboveThreshold** answers an adaptively chosen stream of real queries
$f_1,f_2,\ldots$, each of sensitivity at most $1$, against a public
threshold $T$. It draws $\hat T=T+\mathop{\mathrm{Lap}}(2/\varepsilon)$ once
and, for each query, an independent $\nu_i\sim\mathop{\mathrm{Lap}}(4/\varepsilon)$.
It reports "below" while $f_i(D)+\nu_i<\hat T$, and at the first $i$ with
$f_i(D)+\nu_i\ge\hat T$ it reports "above" and halts.

* **74. Sparse vector technique.** AboveThreshold is
  $\varepsilon$-differentially private, whatever the number of queries.
  If among the first $k$ queries only the last can satisfy
  $f_i(D)\ge T-\alpha$, then with probability at least $1-\beta$ it does
  not halt before query $k$, every "above" report has $f_i(D)\ge T-\alpha$,
  and every "below" report has $f_i(D)\le T+\alpha$, where
  $$\alpha=\frac{8(\log k+\log(2/\beta))}{\varepsilon}.$$
  Privacy is paid for the above-threshold reports only; restarting after
  each of $c$ such reports and using item 65 handles $c>1$. Releasing all
  noisy query values would instead cost privacy for every query.

A release kernel $Q$ is **$\varepsilon$-locally private** when
$Q(B\mid x)\le e^\varepsilon Q(B\mid x')$ for all measurable $B$ and all
inputs $x,x'$. For a law $P$ of the input write $M_P=\int Q(\cdot\mid x)\,dP(x)$
for the law of the release, and let $\|P_1-P_2\|_{\mathrm{TV}}
=\sup_B|P_1(B)-P_2(B)|$.

* **75. Contraction under local privacy.** If $Q$ is
  $\varepsilon$-locally private, then for all input laws $P_1,P_2$,
  $$D(M_{P_1}\|M_{P_2})+D(M_{P_2}\|M_{P_1})
  \le4(e^\varepsilon-1)^2\|P_1-P_2\|_{\mathrm{TV}}^2$$
  (Duchi, Jordan, and Wainwright). For $n$ individuals with independent
  inputs and noninteractive releases, divergences add, so the two-point
  and Fano methods of SYNOPSIS103, items 39 and 40, apply with $n$
  replaced by an effective sample size of order $n(e^\varepsilon-1)^2$,
  that is $n\varepsilon^2$ for $\varepsilon\le1$. This yields the local
  lower bound of item 66. The statement extends to sequentially
  interactive releases.

### Fairness criteria and label shift

A score $S$ satisfies **independence**, or demographic parity, when
$S\perp A$.

* **76. Independence versus the conditional criteria.** If $A$ and $Y$
  are dependent, independence and sufficiency cannot both hold, since
  $A\perp S$ and $A\perp Y\mid S$ give $A\perp(Y,S)$. If $Y$ is binary,
  $A$ and $Y$ are dependent, and $S$ and $Y$ are dependent, independence
  and separation cannot both hold; this can fail for a response with more
  than two values. A sufficient score becomes calibrated within groups
  after the relabeling $\ell(s)=P(Y=1\mid S=s)$. With item 67, each pair
  of the three criteria is therefore incompatible outside degenerate
  cases.

Under **label shift**, source and target laws of $(X,Y)$, with
$Y\in\{1,\ldots,K\}$, have the same class-conditional laws of $X$ given
$Y=j$ but label marginals $p_S$ and $p_T$, with $p_S(j)>0$ for all $j$. Put
$w_j=p_T(j)/p_S(j)$.

* **77. Label shift: correction and identification.** The target
  conditional probabilities are
  $$p_T(j\mid x)=\frac{w_jp_S(j\mid x)}{\sum_kw_kp_S(k\mid x)},$$
  and for an integrable loss $R_T(f)=\mathbb E_S[w_YL(Y,f(X))]$. For any
  fixed classifier $h$ with values in $\{1,\ldots,K\}$, the target law of
  its predictions is $q_i=P_T(h(X)=i)=\sum_jC_{ij}w_j$, with
  $C_{ij}=P_S(h(X)=i,\,Y=j)$. If $C$ is invertible, then $w=C^{-1}q$ is
  identified from labeled source data and unlabeled target covariates.
  The weights here depend on the label, whereas under covariate shift,
  item 68, they depend on the covariates. A classifier that never predicts
  some class makes $C$ singular, and plug-in estimation error grows as
  the smallest singular value of $C$ decreases.

## Reference guide

### Correspondence with the subdivisions

- **[107A](#synopsis-107a)**: Vapnik, Anthony and Bartlett, Mohri,
  Rostamizadeh, and Talwalkar, and Devroye, Györfi, and Lugosi carry VC theory
  and the no-free-lunch theorem. Cesa-Bianchi and Lugosi carry online regret.
  Koltchinskii carries the Rademacher and kernel bounds. Mohri, Rostamizadeh,
  and Talwalkar carry margins, surrogate losses, and stability; Wainwright
  carries kernel ridge regression; Devroye, Györfi, and Lugosi carry
  nearest-neighbour rules and data splitting. Breiman, Friedman, Olshen, and
  Stone carry cost-complexity pruning. Pollard carries consistency of
  $k$-means. Wainwright and Jordan carry the Bethe free energy and belief
  propagation. Scornet, Biau, and Vert carry consistency of random forests in
  additive models. Mohri, Rostamizadeh, and Talwalkar carry AdaBoost and
  ensemble margins; Wainwright and Jordan also carry the conjugate duality of
  the cumulant function and junction trees. Cybenko, Hornik, Stinchcombe, and
  White, and Leshno, Lin, Pinkus, and Schocken carry universal approximation.
  Barron carries the dimension-free one-hidden-layer rate. Schmidt-Hieber
  carries compositional rates for deep ReLU networks. Jacot, Gabriel, and
  Hongler carry the neural tangent kernel. Hastie, Montanari, Rosset, and
  Tibshirani carry ridgeless interpolation. Goodfellow and coauthors carry the
  adversarial equilibrium. Grohs and Kutyniok's collection carries network
  capacity, depth separation, Yarotsky's rates, and implicit bias; Roberts,
  Yaida, and Hanin carry the infinite-width kernel recursion; Bronstein,
  Bruna, Cohen, and Veličković carry equivariant layers and attention. Abbe's
  survey carries the stochastic block model thresholds. Lovász carries
  graphons. Kolaczyk and Newman carry the statistical and probabilistic
  background on networks. Xu, Hu, Leskovec, and Jegelka carry the
  Weisfeiler–Leman comparison for message-passing networks. Blum, Hopcroft,
  and Kannan, and Newman, carry Erdős–Rényi thresholds; Vershynin carries
  spectral clustering of the block model.
- **[107B](#synopsis-107b)**: Lai and Robbins carry the asymptotic lower
  bound. Auer, Cesa-Bianchi, and Fischer carry UCB1 and Exp3. Puterman, and
  Bertsekas and Tsitsiklis, carry Markov decision processes and the
  convergence of $Q$-learning. Gittins carries the index theorem. Agarwal,
  Brantley, Jiang, Kakade, and Sun carry the linear-programming view,
  generative-model sample complexity, natural policy gradient, and LinUCB;
  Bertsekas and Tsitsiklis carry TD($\lambda$); Cesa-Bianchi and Lugosi carry
  the minimax bandit lower bound. Dwork and Roth carry differential privacy,
  the Laplace mechanism, and composition. Barocas, Hardt, and Narayanan carry
  the fairness definitions and the incompatibility and post-processing
  statements. Ben-David, Blitzer, Crammer, and Pereira carry the $\mathcal
  H\Delta\mathcal H$ bound. Shimodaira carries covariate-shift reweighting.
  Dwork and Roth also carry the sparse vector technique; Duchi, Jordan, and
  Wainwright carry local-privacy contraction; Quiñonero-Candela and coauthors
  carry prior-probability shift.

### Source comparisons and local copies

#### High-dimensional statistics and statistical learning

Items 8 and 9 separate Bayes risk, approximation error, and the uniform
deviations already cited from CKMA.

Mohri, Rostamizadeh, and Talwalkar supply Theorem 5.8 and Corollary 5.11
(item 10), Proposition 4.6 and Theorem 4.7 with Exercise 4.2 (item 11), and
Theorem 14.2 with Proposition 14.4 (item 12). Devroye, Györfi, and Lugosi
supply Theorems 5.1, 5.4, and 5.6 (item 14) and Section 22.1 with Theorem
8.3 and Theorem 22.1 (item 15). The hinge-loss constants in item 11 and the
polynomial eigenvalue-decay rate in item 13 are direct computations from
those statements.

Bühlmann and van de Geer, *Statistics for High-Dimensional Data*, Hastie,
Tibshirani, and Friedman, *The Elements of Statistical Learning*,
Shalev-Shwartz and Ben-David, *Understanding Machine Learning*, Steinwart
and Christmann, *Support Vector Machines*, Vovk, Gammerman, and Shafer,
*Algorithmic Learning in a Random World*, and Efron, *Large-Scale
Inference*, are not in the local reference directory. Item 6 is the
split-conformal coverage theorem of that literature.

#### Machine-learning models and sequential decisions

Wainwright–Jordan's tree and Bethe variational developments were consulted
for items 19 and 23. Their tree exactness does not imply convergence or
global optimality of loopy belief propagation. The corrected boosting
statement is the squared-error line-search identity; the forest statement
uses independent response estimation and locality, not honesty alone.
Scornet–Biau–Vert's response-adaptive theorem is a specialized result,
not a general corollary of the shrinking-cell argument.

The local Grohs–Kutyniok collection, Chapter 1, was read for Theorem 1.27
on Barron approximation and the tangent-kernel discussion around
equations (1.21)–(1.23). Item 29 specifies the statistical compositional
class and effective smoothness. Item 31 now gives finite-sample expected
Gaussian-design risks and assumes a limiting signal norm; item 32 permits
boundary discriminator values when claiming an attained maximum.
Bishop–Bishop supplies the probabilistic output and Gaussian-conditioning
framework for the new prediction entries.

[Abbe's survey, Theorem 13 and its boundary discussion](https://jmlr.org/papers/v18/16-480.html),
was checked online for items 41 and 42. The exact-recovery equality case
differs for positive and zero between-group probabilities. For item 43,
[Janson's Theorem 8.6](https://arxiv.org/abs/1009.2376)
gives common measure-preserving pullbacks, not necessarily one invertible
relabeling. Message-passing injectivity is stated only on the domain for
which it is assumed or constructed.

Puterman and Bertsekas–Tsitsiklis supply discounted policy evaluation,
improvement, and the stochastic approximation framework. The finite-model
conditions are now explicit for Bellman contraction and $Q$-learning.
Items 56 and 57 record the occupancy and score identities for those models.
The bandit entries distinguish instance-dependent logarithmic regret,
its leading divergence constant, discounted Bayesian index optimality,
and the oblivious-adversary bound. Lattimore–Szepesvári, Sutton–Barto,
and the original bandit papers were not located as local full texts.

Dwork–Roth, Proposition 2.1 and Sections 3.2–3.5, was consulted for
post-processing, randomized response, the exponential mechanism, and
Theorem 3.22 on Gaussian noise. Item 66 now fixes bounded observations
and the privacy model; it no longer states a uniform minimax rate from
boundedness of the mean alone. The local-model comparison is in
[Duchi–Jordan–Wainwright](https://arxiv.org/abs/1604.02390).
The central bounded-model upper bound follows from the sample mean's
sensitivity; its lower bound already occurs in bounded two-point families.

Barocas–Hardt–Narayanan, the chapter on classification criteria, was read
for separation, sufficiency, and their incompatibility propositions.
Calibration is distinguished from sufficiency, and perfect prediction
is retained as an exception. Item 68 fixes the conventional factor two
in the disagreement divergence, and item 73 gives a separate variance
condition for weighted inference.

Hastie–Tibshirani–Friedman, Goodfellow–Bengio–Courville, Murphy,
Bishop's 2006 pattern-recognition book, and Lovász were not located in
the two reference directories. Bishop–Bishop's 2024 text is a different
local book and was consulted. Original online papers read for this review
are identified above; the lists below also retain other source copies
identified in the first pass.

Items 24–27, 35–40, 47, 48, 58–63, and 74–77 were checked against the following passages. Mohri,
Rostamizadeh, and Talwalkar, Theorem 7.2, Lemma 7.4, Corollary 7.5,
Theorem 7.7 with the discussion of (7.18), and Section 7.2.2, give item 24.
Breiman, Friedman, Olshen, and Stone, Definitions 2.5–2.6, Proposition 4.4,
and Theorem 4.5, give item 25; the multiclass Jensen form is a direct
computation. Wainwright and Jordan, Theorems 3.3–3.4, Theorem 8.1,
Proposition 4.1, Definition 2.1, and Proposition 2.1 with the
triangulation discussion of Section 2.5.2, give items 26 and 27. Grohs and
Kutyniok, Chapter 1, Theorems 1.20, 1.23, 1.24, 1.25, and 1.26, and
Section 1.2.3 with equation (1.24), give items 35–37 and 40; the
linear-envelope condition of Matthews and coauthors in item 39 and the
Soudry et al. statement in item 40 are recorded from the primary papers,
which are not local.
Roberts, Yaida, and Hanin, equations (4.3)–(4.4), (4.8), and (5.1)–(5.2),
give the kernel recursion of item 39. Bronstein, Bruna, Cohen, and
Veličković, Sections 4.1, 4.2 on circulant matrices, and 5.4, give item 38; the self-attention identity is a direct computation.

Blum, Hopcroft, and Kannan, Table 8.1, Theorems 8.6 and 8.11, and Section
8.3, and Newman, equation (11.16), give the Erdős–Rényi thresholds of item 47; the double-exponential connectivity limit is the classical
Erdős–Rényi theorem, not proved in these local texts. Vershynin (2018),
Theorems 4.5.5–4.5.6 and Exercises 5.5.1–5.5.2, give item 48; the explicit
constant $8$ follows from his inequality (4.19). Lovász, *Large Networks
and Graph Limits*, is not local; an earlier entry on the counting lemma
and the Lovász–Szegedy limit and compactness theorems was removed for
want of a local check. Agarwal, Brantley, Jiang, Kakade, and Sun, Theorem 1.7,
Proposition 1.15 with the primal and dual programs of Section 1.3,
Lemma 2.2, Proposition 2.1, Theorems 2.6–2.7, Lemma 10.6, Theorems
10.3 and 10.8, Theorems 5.2 and 5.4–5.5, and Lemma A.9, give items 58, 59, and 61–63. In Lemma A.9 the regressors are taken predictable, as in
Abbasi-Yadkori, Pál, and Szepesvári. Bertsekas and Tsitsiklis, Section 6.3,
Assumption 6.1 and Propositions 6.4–6.5, give item 60. Cesa-Bianchi and
Lugosi, Theorem 6.11 and its proof, give item 62; the proof bounds
the regret against the best arm in expectation on stochastic Bernoulli
instances.

Dwork and Roth, Algorithm 1 with Theorems 3.23–3.24 and Section 3.6,
give item 74. An earlier entry giving the hypothesis-testing restatement
of the privacy definition was removed as redundant with that definition. Item 75 is
Theorem 1 of the Duchi–Jordan–Wainwright paper linked above.
Barocas, Hardt, and Narayanan, Propositions 1–3 of the classification
chapter, give item 76. Quiñonero-Candela and coauthors, Section 1.5, give
the prior-shift correction of item 77; the confusion-matrix identification
is a direct computation, the black-box shift estimator of Lipton, Wang,
and Smola, which is not local.

Local texts directly consulted or identified for this selection:

- [van de Geer, *Estimation and Testing Under Sparsity*](../lean-CKMA/References/VanDeGeer2016EstimationTestingUnderSparsityÉcoleDÉtéProbabilitésSaintFlourXLV2015-Springer.LNM2159.pdf).
- [Wainwright, *High-Dimensional Statistics*](../lean-CKMA/References/Wainwright2019HighDimensionalStatistics-Cambridge.pdf).
- [Koltchinskii, *Oracle Inequalities in Empirical Risk Minimization*](../lean-CKMA/References/Koltchinskii2011OracleInequalitiesEmpiricalRiskMinimizationSparseRecoveryProblems-Springer.LNM2033.pdf).
- [Vapnik, *Statistical Learning Theory*](../lean-CKMA/References/Vapnik1998StatisticalLearningTheory-WileyInterscience.pdf).
- [Anthony and Bartlett, *Neural Network Learning*](../lean-CKMA/References/AnthonyBartlett1999NeuralNetworkLearningTheoreticalFoundations-Cambridge.pdf).
- [Mohri, Rostamizadeh, and Talwalkar, *Foundations of Machine Learning*](../lean-CKMA/References/MohriRostamizadehTalwalkar2018FoundationsMachineLearning2ndEd-MITPress.ACML.pdf).
  Chapter 7 was read.
- [Devroye, Györfi, and Lugosi, *A Probabilistic Theory of Pattern Recognition*](../lean-CKMA/References/DevroyeGyörfiLugosi1996ProbabilisticTheoryPatternRecognition-Springer.SMAP31.pdf).
- [Cesa-Bianchi and Lugosi, *Prediction, Learning, and Games*](../lean-CKMA/References/CesaBianchiLugosi2006PredictionLearningGames-Cambridge.pdf).
  Theorem 6.11 was read.
- [Bishop and Bishop, *Deep Learning: Foundations and Concepts*](../lean-CKMA/References/BishopBishop2024DeepLearningFoundationsConcepts-Springer.pdf).
  Probabilistic prediction and the diffusion chapter were consulted.
- [Dwork and Roth, *The Algorithmic Foundations of Differential Privacy*](../lean-CKMA/References/DworkRoth2014AlgorithmicFoundationsDifferentialPrivacy-NowPublishers.FnTTCS9.pdf).
  Theorems 3.6, 3.16, 3.20, and 3.23–3.24 were read.
- [Wainwright and Jordan, *Graphical Models, Exponential Families, and Variational Inference*](../lean-CKMA/References/WainwrightJordan2008GraphicalModelsExponentialFamiliesVariationalInference-NowPublishers.FnTML1.pdf).
- [Breiman, Friedman, Olshen, and Stone, *Classification and Regression Trees*](../lean-CKMA/References/BreimanFriedmanOlshenStone1984ClassificationRegressionTrees-ChapmanHallCRC.pdf).
- [Koller and Friedman, *Probabilistic Graphical Models*](../lean-CKMA/References/KollerFriedman2009ProbabilisticGraphicalModelsPrinciplesTechniques-MITPress.ACML.pdf).
- [Pinkus, *Ridge Functions*](../lean-CKMA/References/Pinkus2015RidgeFunctions-Cambridge.TractsMath205.pdf).
- [Grohs and Kutyniok, editors, *Mathematical Aspects of Deep Learning*](../lean-CKMA/References/GrohsKutyniokEds2023MathematicalAspectsDeepLearning-Cambridge.pdf).
- [Puterman, *Markov Decision Processes*](../lean-CKMA/References/Puterman1994rep2005MarkovDecisionProcessesDiscreteStochasticDynamicProgramming-WileySerProbStat.pdf).
- [Bertsekas and Tsitsiklis, *Neuro-Dynamic Programming*](../lean-CKMA/References/BertsekasTsitsiklis1996NeuroDynamicProgramming-AthenaScientific.pdf).
- [Meyn, *Control Systems and Reinforcement Learning*](../lean-CKMA/References/Meyn2022ControlSystemsReinforcementLearning-Cambridge.pdf).
- [Kolaczyk, *Statistical Analysis of Network Data*](../lean-CKMA/References/Kolaczyk2009StatisticalAnalysisNetworkDataMethodsModels-SpringerSSS.pdf).
- [Newman, *Networks*](../lean-CKMA/References/Newman2018Networks2ndEd-OxfordUP.pdf).
- [Barocas, Hardt, and Narayanan, *Fairness and Machine Learning*](../lean-CKMA/References/BarocasHardtNarayanan2022FairnessMachineLearningLimitationsOpportunities-AuthorManuscript.pdf).
- [Hardt and Recht, *Patterns, Predictions, and Actions*](../lean-CKMA/References/HardtRecht2023PatternsPredictionsActionsStoryMachineLearning-AuthorManuscript.pdf).
- [Blum, Hopcroft, and Kannan, *Foundations of Data Science*](../lean-CKMA/References/BlumHopcroftKannan2020FoundationsDataScience-Cambridge.pdf).
- [Agarwal, Brantley, Jiang, Kakade, and Sun, *Reinforcement Learning: Theory and Algorithms*](../lean-CKMA/References/AgarwalEtAl2026ReinforcementLearningTheoryAlgorithms-BookDraft.pdf).
  Chapters 1, 2, 5, and 10 and Appendix A.5 were read.
- [Vershynin, *High-Dimensional Probability*](../lean-CKMA/References/Vershynin2018HighDimensionalProbabilityIntroductionApplicationsDataScience-CambridgeSerStatProbMath47.pdf).
  Sections 4.5 and 5.5 were read.
- [Bronstein, Bruna, Cohen, and Veličković, *Geometric Deep Learning*](../lean-CKMA/References/BronsteinBrunaCohenVeličković2021GeometricDeepLearningGridsGroupsGraphsGeodesicsGauges-BookDraft.Arxiv2104.13478v2.pdf).
- [Roberts and Yaida, with Hanin, *The Principles of Deep Learning Theory*](../lean-CKMA/References/RobertsYaidaHanin2022PrinciplesDeepLearningTheory-CambridgeUP.pdf).
  Chapters 4 and 5 were consulted for the kernel recursion.
- [Quiñonero-Candela, Sugiyama, Schwaighofer, and Lawrence, editors, *Dataset Shift in Machine Learning*](../lean-CKMA/References/QuiñoneroCandelaSugiyamaSchwaighoferLawrenceEds2009DatasetShiftMachineLearning-MITPress.NeuralInfProc.pdf).
  Section 1.5 was read.
