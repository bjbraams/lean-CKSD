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
points that the class can shatter, as in CKMA SYNOPSIS07, item 35. A
class is **agnostic PAC learnable** with sample complexity
$m(\varepsilon,\delta)$ if there is a rule mapping samples to $\hat f\in\mathcal F$
such that for all $\varepsilon,\delta\in(0,1)$, every law of $(X,Y)$, and
every $n\ge m(\varepsilon,\delta)$, with probability at least $1-\delta$,
$R(\hat f)\le\inf_{f\in\mathcal F}R(f)+\varepsilon$; it is **PAC learnable
in the realizable case** if this holds for the laws with
$\inf_{f\in\mathcal F}R(f)=0$. The sample complexity of the class is the
smallest such function.

* **1. Fundamental theorem of statistical learning.** For binary
  classification under $0$–$1$ loss, the following are equivalent: the VC
  dimension $v$ is finite; the class is PAC learnable in the realizable case;
  the class is agnostic PAC learnable. There are absolute constants
  $C_1,C_2>0$ such that, if $1\le v<\infty$, the agnostic sample complexity
  lies between $C_1(v+\log(1/\delta))/\varepsilon^2$ and
  $C_2(v+\log(1/\delta))/\varepsilon^2$, and the realizable sample
  complexity lies between $C_1(v+\log(1/\delta))/\varepsilon$ and
  $C_2(v\log(1/\varepsilon)+\log(1/\delta))/\varepsilon$.
  For an empirical-risk minimizer $\hat f$ over a class of VC dimension
  $v\ge1$, there is a universal constant $C$ such that, for all $n\ge2$
  and $\delta\in(0,1)$, with probability at least $1-\delta$,
  $$R(\hat f)\le R_n(\hat f)
  +C\sqrt{\frac{v\log n+\log(1/\delta)}n}.$$
  The uniform deviation behind this bound is CKMA SYNOPSIS07, item 37.

The **empirical Rademacher complexity** of a class $\mathcal F$ on a sample
$x_1,\ldots,x_n$ is
$$\widehat{\mathop{\mathrm{Rad}}}_n(\mathcal F)
=\mathbb E_\sigma\Bigl[\sup_{f\in\mathcal F}
n^{-1}\sum_{i=1}^n\sigma_i f(x_i)\Bigr],$$
where the $\sigma_i$ are independent Rademacher signs. For an
independent and identically distributed sample $Z_1,\ldots,Z_n$ with law $P$
write $Pf=\mathbb Ef(Z_1)$ and $P_nf=n^{-1}\sum_{i=1}^nf(Z_i)$, and evaluate
the empirical complexity at $x_i=Z_i$.

* **2. Rademacher bound.** For a countable class of measurable functions
  with values in $[0,1]$, or any such class for which the suprema below are
  measurable,
  $$\mathbb E\sup_{f\in\mathcal F}(P_n-P)f
  \le2\,\mathbb E\,\widehat{\mathop{\mathrm{Rad}}}_n(\mathcal F),$$
  and the same holds with $P-P_n$ in place of $P_n-P$.
  With probability at least $1-\delta$,
  $$\sup_{f\in\mathcal F}|(P_n-P)f|
  \le2\,\mathbb E\,\widehat{\mathop{\mathrm{Rad}}}_n(\mathcal F)
  +\sqrt{\frac{\log(2/\delta)}{2n}}.$$
  With probability at least $1-\delta$, also
  $$\sup_{f\in\mathcal F}(P-P_n)f
  \le2\,\widehat{\mathop{\mathrm{Rad}}}_n(\mathcal F)
  +3\sqrt{\frac{\log(2/\delta)}{2n}}.$$

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
For a closed convex set $\mathcal Z\subseteq\mathbb R^m$ with Euclidean
projection $\Pi$, **online gradient descent** with step $\eta$ starts at
$z_1\in\mathcal Z$ and sets $z_{t+1}=\Pi(z_t-\eta g_t)$, where $g_t$ is a
subgradient of $\ell_t$ at $z_t$. For $K$ actions and loss vectors
$\ell_t\in[0,1]^K$, the **exponentially weighted forecaster** with learning
rate $\eta$ plays the weights $p_t(i)\propto\exp(-\eta\sum_{s<t}\ell_s(i))$
and incurs loss $\sum_ip_t(i)\ell_t(i)$.

* **4. Online gradient descent.** Let the losses be convex and
  $G$-Lipschitz on a closed convex set of Euclidean diameter $D$, and let
  $\|g_t\|_2\le G$. Online gradient
  descent with step size $\eta=D/(G\sqrt T)$ has regret at most $DG\sqrt T$
  against every fixed comparator in the set.

* **5. Hedge.** For $K$ actions and losses with values in $[0,1]$, the
  exponentially weighted forecaster with learning rate
  $\eta=\sqrt{8(\log K)/T}$ has regret at most $\sqrt{(T/2)\log K}$ against
  the best fixed action.

Split the sample into a training part and a calibration part of size $n$, and
let $s$ be a score trained on the training part. Let
$S_1,\ldots,S_n$ be the calibration scores and let $S_{n+1}=s(X_{n+1},Y_{n+1})$.
Write $S_{(k)}$ for the $k$th smallest calibration score, and set
$S_{(k)}=+\infty$ when $k>n$.

* **6. Split conformal prediction.** Assume that the $n+1$ calibration
  and test pairs are exchangeable conditionally on the training part, and
  that the score is a function of the training part and of the pair at
  which it is evaluated. For $\alpha\in(0,1)$ let
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
  $2C\delta^{\alpha+1}$.

* **9. Empirical risk minimization.** If $\hat f$ minimizes empirical risk
  over $\mathcal F$ up to error $\varepsilon_n$, then
  $$R(\hat f)-\inf_{f\in\mathcal F}R(f)
  \le2\sup_{f\in\mathcal F}|R_n(f)-R(f)|+\varepsilon_n.$$

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
  For the kernel ball
  $\|h\|_{\mathcal H}\le\Lambda$ with $K(x,x)\le r^2$, item 3 makes the
  complexity term $(2/\rho)\widehat{\mathop{\mathrm{Rad}}}_n$ at most
  $2\Lambda r/(\rho\sqrt n)$.

Let $\eta(x)=P(Y=1\mid X=x)$ and let $R^*$ be the Bayes risk of item 8.
For a convex nondecreasing $\Phi:\mathbb R\to[0,\infty)$ the **surrogate
risk** is $R_\Phi(h)=\mathbb E\,\Phi(-Yh(X))$, with infimum $R_\Phi^*$ over
measurable $h$, and the conditional surrogate risk is
$L_\Phi(x,u)=\eta(x)\Phi(-u)+(1-\eta(x))\Phi(u)$.

* **11. Comparison inequality for convex surrogates.** If $\Phi$ is
  differentiable at $0$ with $\Phi'(0)>0$, then every minimizer of
  $u\mapsto L_\Phi(x,u)$ over $[-\infty,\infty]$ is positive when
  $\eta(x)>1/2$ and negative when $\eta(x)<1/2$, and $u=0$ is a minimizer
  when $\eta(x)=1/2$. If there are $s\ge1$ and $c>0$ with
  $$\bigl|\eta(x)-\tfrac12\bigr|^s
  \le c^s\Bigl(L_\Phi(x,0)-\inf_uL_\Phi(x,u)\Bigr)$$
  for all $x$, then for every measurable $h$ with $P(h(X)=0)=0$,
  $$R(h)-R^*\le2c\bigl(R_\Phi(h)-R_\Phi^*\bigr)^{1/s}.$$
  The condition $P(h(X)=0)=0$ cannot be dropped: for $\eta\equiv1/2$ and
  $h\equiv0$ one has $R(h)-R^*=1/2$ and $R_\Phi(h)=R_\Phi^*$.
  For the hinge loss $\Phi(u)=\max(0,1+u)$ one may take $s=1$, $c=1/2$,
  giving $R(h)-R^*\le R_\Phi(h)-R_\Phi^*$. For the squared hinge loss
  $\Phi(u)=\max(0,1+u)^2$ one may take $s=2$, $c=1/2$. This is Zhang's
  inequality.

A learning algorithm maps a sample $S$ of size $n$ to a predictor $h_S$.
For a loss $L$ the map $(S,z)\mapsto L(h_S,z)$ is assumed measurable.
It is **uniformly $\beta$-stable** for $L$ if
$|L(h_S,z)-L(h_{S'},z)|\le\beta$ for every point $z$ and every pair of
samples $S,S'$ that differ in one point.

* **12. Generalization of stable algorithms.** If the algorithm is
  uniformly $\beta$-stable and $0\le L(h_S,z)\le M$ for every sample and
  point, then with probability at least $1-\delta$,
  $$R(h_S)\le R_n(h_S)+\beta+(2n\beta+M)\sqrt{\frac{\log(1/\delta)}{2n}}.$$
  Regularized empirical
  risk minimization over a reproducing-kernel Hilbert space,
  $h_S\in\mathop{\mathrm{argmin}}_h\bigl(R_n(h)+\lambda\|h\|_{\mathcal H}^2\bigr)$,
  with $K(x,x)\le r^2$ and a loss convex in the prediction and $G$-Lipschitz
  in it, is uniformly stable with $\beta\le G^2r^2/(n\lambda)$.

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
  with universal constants $c_0,c_1,c_2,c_3>0$. If $\hat\mu_j=0$ for
  $j>m$, the critical inequality holds with
  $\delta_n^2=32\sigma^2m/(nR^2)$. If $\hat\mu_j\le cj^{-2\alpha}$ for all
  $j$, with $\alpha>1/2$, it holds with
  $\delta_n^2=C(\sigma^2/n)^{2\alpha/(2\alpha+1)}$ for a constant $C$
  depending only on $c$, $\alpha$, and $R$. For the first-order Sobolev
  kernel $\min(x,z)$ on $[0,1]$ and the design $x_i=i/n$ one has
  $\hat\mu_j\le9/(4j^2)$, so $\alpha=1$ and $\delta_n^2$ is a constant
  multiple of $(\sigma^2/n)^{2/3}$, in agreement with SYNOPSIS103, item 9.

In binary classification with labels in $\{0,1\}$ and features in
$\mathbb R^d$, the **$k$-nearest-neighbour rule** takes a majority vote
among the labels of the $k$ sample points closest to $x$ in Euclidean
distance, distance ties being broken by comparing independent uniform
random variables attached to the sample points. Write $L_n$ for its error
probability given the sample and $L^*$ for the Bayes risk.

* **14. Asymptotics of nearest-neighbour rules.** For every distribution
  of $(X,Y)$, the $1$-nearest-neighbour rule satisfies
  $$\lim_{n\to\infty}\mathbb E L_n=L_{\mathrm{NN}}
  =\mathbb E\bigl[2\eta(X)(1-\eta(X))\bigr],\qquad
  L^*\le L_{\mathrm{NN}}\le2L^*(1-L^*)\le2L^*.$$
  For fixed odd $k$ the limit $L_{k\mathrm{NN}}$ of $\mathbb EL_n$ exists
  for every distribution and satisfies
  $L^*\le L_{k\mathrm{NN}}\le L^*+1/\sqrt{ke}$; it is nonincreasing over
  odd $k$. If $k=k_n\to\infty$ and $k_n/n\to0$, then $\mathbb EL_n\to L^*$
  for every distribution; compare Stone's theorem, SYNOPSIS103, item 7.

* **15. Hold-out selection.** Split the sample into a training part and an
  independent hold-out part of size $l$. Let $\phi_1,\ldots,\phi_N$ be
  classifiers computed from the training part, and let $\hat\phi$ minimize
  the hold-out error frequency among them. Conditionally on the training
  part, with probability at least $1-\delta$,
  $$L(\hat\phi)\le\min_{1\le j\le N}L(\phi_j)
  +\sqrt{\frac{2\log(2N/\delta)}l},$$
  where $L$ is the error probability. The penalized selector of
  SYNOPSIS103, item 35 is the analogue without splitting.

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
  criterion has a unique minimizing set $C^*$ of $k$ centers. Let
  $X_1,X_2,\ldots$ be independent copies of $X$ and, for each $n$, let
  $C_n$ be any set of at most $k$ centers minimizing the empirical
  criterion $n^{-1}\sum_{i\le n}\min_j\|X_i-c_j\|^2$. Then the Hausdorff
  distance between $C_n$ and $C^*$ tends to $0$ almost surely.

A binary tree $T$ grown on a training sample has resubstitution error
$R(T)$ and $|T|$ terminal nodes. For $\alpha\ge0$ the **cost-complexity**
is $R_\alpha(T)=R(T)+\alpha|T|$.

* **17. Cost-complexity pruning.** Consider the pruned subtrees of $T$,
  that is, the subtrees with the root of $T$ obtained by removing
  branches. For each $\alpha\ge0$ there is a unique pruned subtree
  $T(\alpha)$ that minimizes $R_\alpha$ and is a pruned subtree of every
  other minimizer. If $\alpha\le\alpha'$, then $T(\alpha')$ is a pruned
  subtree of $T(\alpha)$; hence $\alpha\mapsto T(\alpha)$ takes finitely
  many values, forming a nested decreasing sequence.

For squared error, let $f^*(X)=\mathbb E[Y\mid X]$, with $Y\in L^2$,
and put $r_m=f^*-f_m$, where $\langle\cdot,\cdot\rangle$ and $\|\cdot\|_2$
are those of $L^2$ of the law of $X$. The excess prediction risk is
$\|r_m\|_2^2$. A base learner $h_m$ is a nonzero square-integrable
function of $X$.

* **18. Descent of gradient boosting.** Suppose
  $\langle r_m,h_m\rangle\ge\gamma\|r_m\|_2\|h_m\|_2$ for a fixed
  $\gamma>0$. Choose the least-squares coefficient
  $a_m=\langle r_m,h_m\rangle/\|h_m\|_2^2$ and update
  $f_{m+1}=f_m+\nu a_m h_m$, with $0<\nu<2$. Then
  $$\|r_{m+1}\|_2^2\le
  (1-\nu(2-\nu)\gamma^2)\|r_m\|_2^2.$$
  If this holds at every step, then
  $\|r_m\|_2^2\le(1-\nu(2-\nu)\gamma^2)^m\|r_0\|_2^2$.

Consider a **pairwise model** on a finite graph $(V,E)$ with finite state
spaces, $p(x)\propto\prod_{i\in V}\psi_i(x_i)\prod_{\{i,j\}\in E}
\psi_{ij}(x_i,x_j)$, with positive potentials; $N(i)$ is the neighbourhood
and $d_i$ the degree of $i$. The **local polytope** consists of the
families of nonnegative $b_i$ and $b_{ij}$ with $\sum_{x_i}b_i(x_i)=1$ and
$\sum_{x_j}b_{ij}(x_i,x_j)=b_i(x_i)$ for every edge and both orientations.
On it the **Bethe free energy** is
$$F_B(b)=-\sum_i\sum_{x_i}b_i\log\psi_i
-\sum_{\{i,j\}\in E}\sum_{x_i,x_j}b_{ij}\log\psi_{ij}-H_B(b),\qquad
H_B=\sum_{\{i,j\}\in E}H(b_{ij})-\sum_i(d_i-1)H(b_i).$$
**Belief propagation** acts on positive messages $m_{i\to j}$, one for
each oriented edge, by
$$m_{i\to j}(x_j)\propto\sum_{x_i}\psi_i(x_i)\psi_{ij}(x_i,x_j)
\prod_{\ell\in N(i)\setminus\{j\}}m_{\ell\to i}(x_i).$$
The beliefs of messages are
$b_i\propto\psi_i\prod_{j\in N(i)}m_{j\to i}$ and
$b_{ij}\propto\psi_i\psi_j\psi_{ij}\prod_{\ell\in N(i)\setminus\{j\}}
m_{\ell\to i}\prod_{\ell\in N(j)\setminus\{i\}}m_{\ell\to j}$.

* **19. Belief propagation and the Bethe free energy.** The beliefs of a
  fixed point of belief propagation lie in the relative interior of the
  local polytope and are a stationary point of $F_B$ restricted to that
  polytope. Conversely, every stationary point of $F_B$ in the relative
  interior of the local polytope consists of the beliefs of some fixed
  point. Exact inference on trees is item 23 below.

* **20. Consistency of response-independent forests.** Let
  $(X,Y),(X_1,Y_1),\ldots,(X_n,Y_n)$ be independent and identically
  distributed, with $\mathbb EY^2<\infty$ and $m(x)=\mathbb E[Y\mid X=x]$.
  Let the weights $w_{ni}(x)\ge0$, with $\sum_iw_{ni}(x)=1$, be measurable
  functions of $x$, of $X_1,\ldots,X_n$, and of randomness independent of
  all the pairs, but not of $Y_1,\ldots,Y_n$. Leaf averages of a tree
  partition built without these responses, and averages of several such
  trees, are of this form when no leaf is free of sample points. Put $m_n(x)=\sum_iw_{ni}(x)Y_i$. Suppose that
  there is $C$ with
  $$\mathbb E\sum_iw_{ni}(X)g(X_i)\le C\,\mathbb E g(X)$$
  for all $n$ and all nonnegative bounded measurable $g$, that
  $\mathbb E\sum_iw_{ni}(X)1_{\{\|X_i-X\|>\eta\}}\to0$ for every
  $\eta>0$, and that $\mathbb E\max_iw_{ni}(X)\to0$. Then
  $\mathbb E(m_n(X)-m(X))^2\to0$.

### Prediction losses and ensemble structure

* **21. Proper prediction losses.** For a categorical response with
  conditional probabilities $p_j(x)$, expected logarithmic loss of a
  reported probability vector $q$ equals
  $$-\sum_jp_j\log q_j
  =-\sum_jp_j\log p_j+D(p\|q).$$
  It is minimized by the true probabilities. For the Brier loss
  $\sum_j(q_j-1_{\{Y=j\}})^2$, the excess conditional risk is
  $\sum_j(q_j-p_j)^2$. Bayes classification risk is item 8.

* **22. Variance of an ensemble average.** If $B$ square-integrable
  predictions have the same variance $\sigma^2$ and pairwise correlation
  $\rho$, their average has variance
  $$\sigma^2\left(\rho+\frac{1-\rho}{B}\right).$$

* **23. Exact belief propagation on a tree.** For the positive pairwise
  model of item 19 on a tree, the belief-propagation equations have a
  fixed point that is unique up to positive scaling of each message; it
  is computed by one pass from the leaves to a root and one pass back.
  Its beliefs $b_i$ and $b_{ij}$ are the exact node and edge marginals of
  $p$. On a tree every member $b$ of the local polytope is the family of
  marginals of the distribution
  $q(x)=\prod_ib_i(x_i)\prod_{\{i,j\}\in E}
  b_{ij}(x_i,x_j)/(b_i(x_i)b_j(x_j))$, with $0/0=0$, and $H(q)=H_B(b)$.

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
  $2^T\prod_t\sqrt{\varepsilon_t^{1-\rho}(1-\varepsilon_t)^{1+\rho}}$. If
  $0<\rho<\gamma<1/2$ and every $\varepsilon_t\le\frac12-\gamma$, this is
  at most $u^T$ with
  $u=(1-2\gamma)^{(1-\rho)/2}(1+2\gamma)^{(1+\rho)/2}<1$. The empirical
  Rademacher complexity of the convex hull of a class equals that of the
  class, so the margin bound of item 10 applies to
  $f/\|\alpha\|_1$ with the complexity of the base class and without
  dependence on $T$. In each round, $\alpha_t$ minimizes
  $a\mapsto\sum_i\exp\bigl(-y_i(f_{t-1}(x_i)+ah_t(x_i))\bigr)$, where
  $f_{t-1}=\sum_{s<t}\alpha_sh_s$.

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
  both children have the class proportions of the parent. For two classes and a categorical predictor with $L$
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
edge configurations, $\mathcal M$ is the **marginal polytope**; it is
contained in the local polytope of item 19.

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
  so mode computation is a linear program over the marginal polytope. The
  statistical mean parameterization is SYNOPSIS101, item 42.

A **clique tree** of a graph is a tree whose nodes are its maximal cliques.
It has the **running intersection property**, and is then a **junction
tree**, when every clique on the path joining two cliques contains their
intersection. The intersections of adjacent cliques are the separators.

* **27. Junction-tree exactness.** A graph has a junction tree if and only
  if it is triangulated, that is, decomposable in the sense of
  SYNOPSIS105, item 36. On a junction tree with finite state spaces,
  nonnegative clique and separator tables are the marginals of a joint
  probability law if and only if every table is normalized and, on each
  tree edge, both incident clique tables marginalize to its separator
  table. The joint law that is Markov with respect to the graph is unique
  and is the product of clique tables divided by the product of separator
  tables, with one separator factor per tree edge. A configuration with a
  zero separator factor has probability zero; the ratio is interpreted
  with $0/0=0$. The prescribed marginals need not determine a joint law
  outside the Markov class. Item 23 is the tree case.

### Deep learning: architectures, approximation, and training

Density of one-hidden-layer networks in $C(K)$, for a nonpolynomial
continuous activation, is [CKMA SYNOPSIS47](../lean-CKMA/SYNOPSIS47.md),
item 76.

* **28. Barron's rate.** Let the activation be the ReLU or a sigmoidal
  function, that is, a continuous $\phi$ with $\phi(u)\to1$ as
  $u\to\infty$ and $\phi(u)\to0$ as $u\to-\infty$. There is a constant
  $c$, depending only on the activation, such that for all $d,n\ge1$,
  every probability measure $\mu$ on the closed unit ball of $\mathbb R^d$,
  and every continuous integrable $f:\mathbb R^d\to\mathbb R$ with finite
  Fourier moment
  $C_f=\int_{\mathbb R^d}\|\omega\|\,|\hat f(\omega)|\,d\omega$, some
  one-hidden-layer network with $n$ hidden units and an output bias has
  $L^2(\mu)$ distance at most $cC_fn^{-1/2}$ from $f$. The pointwise
  target is the continuous representative determined by Fourier inversion,
  including when $\mu$ is singular with respect to Lebesgue measure.

Fix $q\ge0$, dimensions $d_0=d,d_1,\ldots,d_q$ and $d_{q+1}=1$, integers
$1\le t_i\le d_i$, smoothness indices $\beta_i>0$, and $K>0$. The
**compositional class** $\mathcal G$ consists of the functions
$f=g_q\circ\cdots\circ g_0$ with $g_i:[a_i,b_i]^{d_i}\to
[a_{i+1},b_{i+1}]^{d_{i+1}}$, $[a_0,b_0]=[0,1]$, $|a_i|,|b_i|\le K$, such
that each coordinate of $g_i$ depends on at most $t_i$ of its arguments
and, as a function of those, lies in the Hölder ball of smoothness
$\beta_i$ and radius $K$. For a domain $D\subset\mathbb R^r$ this ball
consists of the $g:D\to\mathbb R$ whose partial derivatives
$\partial^\alpha g$ of order $|\alpha|<\beta$ exist and satisfy
$$\sum_{|\alpha|<\beta}\sup_D|\partial^\alpha g|
+\sum_{|\alpha|=\lfloor\beta\rfloor}\sup_{x\ne y}
\frac{|\partial^\alpha g(x)-\partial^\alpha g(y)|}
{\|x-y\|_\infty^{\beta-\lfloor\beta\rfloor}}\le K,$$
where $\lfloor\beta\rfloor$ is the largest integer strictly smaller
than $\beta$.
Observe $n$ independent copies of $(X,Y)$ with $Y=f(X)+\varepsilon$,
$\varepsilon$ standard normal and independent of $X$, and $X$ with a
Lebesgue density on $[0,1]^d$ bounded above and below by positive
constants. The risk of $\hat f$ is $\mathbb E\int(\hat f-f)^2\,dP_X$.

* **29. Deep networks and compositional classes.** Put
  $$\beta_i^*=\beta_i\prod_{j=i+1}^q\min(\beta_j,1),\qquad
  \phi_n=\max_{0\le i\le q}n^{-2\beta_i^*/(2\beta_i^*+t_i)}.$$
  If $t_i\le\min(d_0,\ldots,d_{i-1})$ for every $i$, then for all
  sufficiently large $K$ there is $c>0$ such that every estimator has
  maximal risk over $\mathcal G$ at least $c\phi_n$. For every $K$ there
  are $C$ and, for each $n\ge2$, a class of sparse ReLU networks, of
  depth of order $\log n$, with all weights and shifts in $[-1,1]$ and
  outputs bounded by $\max(K,1)$, such that every least-squares
  estimator over that class has maximal risk over $\mathcal G$ at most
  $C\phi_n(\log n)^3$. The upper bound does not use the density
  assumption on $X$.

In the **neural tangent parameterization** a fully connected network of
depth $L$ with widths $n_0=d,n_1,\ldots,n_L=1$ and activation $\sigma$ has
$\alpha^{(0)}(x)=x$, $\tilde\alpha^{(\ell+1)}=n_\ell^{-1/2}W^{(\ell)}
\alpha^{(\ell)}+\beta b^{(\ell)}$, $\alpha^{(\ell)}=\sigma(\tilde\alpha^{(\ell)})$
coordinatewise for $1\le\ell<L$, and output $f_\theta=\tilde\alpha^{(L)}$,
with a fixed $\beta>0$. All parameters $\theta$ are initialized as
independent standard normal variables. The **neural tangent kernel** is
$\Theta_\theta(x,x')=\sum_p\partial_{\theta_p}f_\theta(x)\,
\partial_{\theta_p}f_\theta(x')$. Training on inputs $x_1,\ldots,x_n$ with
targets $y$ is gradient flow
$\dot\theta_t=-\nabla_\theta\,(2n)^{-1}\sum_i(f_{\theta_t}(x_i)-y_i)^2$;
write $f_t$ and $\Theta_t$ for the vector of training outputs and the
$n\times n$ kernel matrix at time $t$.

* **30. Neural tangent kernel.** Along the gradient flow, at every width,
  $$\dot f_t=-\Theta_t(f_t-y)/n.$$
  Let $\sigma$ be Lipschitz and twice differentiable with bounded second
  derivative, and let the hidden widths $n_1,\ldots,n_{L-1}$ tend to
  infinity one after the other. Then $\Theta_0$ converges in probability
  to a deterministic positive semidefinite matrix $\Theta$, given by an
  explicit layer recursion, and for every $T>0$,
  $\sup_{0\le t\le T}\|\Theta_t-\Theta\|$ tends to $0$ in probability.

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

For a generator density $p_g$ and a data density $p$, the **generative
adversarial** value of a discriminator $D$ with values in $[0,1]$ is
$$\mathbb E_p\log D(X)+\mathbb E_{p_g}\log\bigl(1-D(X)\bigr).$$

* **32. Equilibrium of a generative adversary.** For fixed $p_g$ the optimal
  discriminator is $D^\star(x)=p(x)/\bigl(p(x)+p_g(x)\bigr)$ wherever the sum
  is positive. Its value equals $-\log4+2\,\mathop{\mathrm{JSD}}(p,p_g)$,
  where $\mathop{\mathrm{JSD}}$ is the Jensen–Shannon divergence,
  with the usual $0\log0=0$ convention. As a function of $p_g$, this
  maximal value is at least $-\log4$, with equality if and only if
  $p_g=p$.

### Probabilistic output layers and kernel prediction

* **33. Softmax and cross-entropy.** For logits $z\in\mathbb R^K$,
  let $A(z)=\log\sum_j e^{z_j}$ and $q_j=e^{z_j-A(z)}$.
  For a one-hot observed label $y$, logarithmic loss is $A(z)-y^\top z$,
  with gradient $q-y$ and Hessian
  $$\mathop{\mathrm{diag}}(q)-qq^\top.$$
  The Hessian is positive semidefinite and annihilates the vector $1$.
  The cumulant calculation is the
  exponential-family identity of SYNOPSIS101, item 4.

* **34. Gaussian-process posterior prediction.** Let a zero-mean Gaussian
  process have kernel $k$, and observe
  $y_i=f(x_i)+\varepsilon_i$ with independent $N(0,\sigma^2)$ noise,
  $\sigma^2>0$. For $K=(k(x_i,x_j))$ and
  $k_x=(k(x_i,x))_i$, the posterior mean and covariance are
  $$m(x)=k_x^\top(K+\sigma^2I)^{-1}y,$$
  $$k_{\mathrm{post}}(x,x')
  =k(x,x')-k_x^\top(K+\sigma^2I)^{-1}k_{x'}.$$
  The posterior predictive variance of a new noisy response at $x$ is
  $k_{\mathrm{post}}(x,x)+\sigma^2$. The posterior mean
  is kernel ridge regression with penalty $\lambda=\sigma^2/n$ for the
  criterion $n^{-1}\sum_i(y_i-f(x_i))^2+\lambda\|f\|_{\mathcal H}^2$.

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
  architecture have VC dimension at most $c(PL\log P+PL^2)$. For every
  class of VC dimension $v$ the $0$–$1$ risks satisfy, with probability
  at least $1-\delta$,
  $\sup_f|R(f)-R_n(f)|\le c'\sqrt{(v+\log(1/\delta))/n}$ with an absolute
  constant $c'$. Hence for each depth $L$ there is $c_L$ such that, for
  $P\ge2$, the bound
  $c_L\sqrt{(P\log P+\log(1/\delta))/n}$ holds for these architectures.
  For bias-free networks on the unit ball, with a
  $1$-Lipschitz positively homogeneous activation and every weight matrix
  of Frobenius norm at most $C$, the Rademacher complexity of the
  real-valued class is at most $2^{L-1}C^L/\sqrt n$, independent of the
  widths.

* **36. Approximation rates of deep ReLU networks.** Let $k\ge2$,
  $p\in[1,\infty]$, $s\in[0,1]$, and $B>0$, and let the activation be
  piecewise linear with at least one breakpoint. There is a constant $c$
  such that for each $\varepsilon\in(0,1/2)$ a single architecture with at
  most $c\varepsilon^{-d/(k-s)}\log(1/\varepsilon)$ parameters
  approximates every $g$ with $\|g\|_{W^{k,p}((0,1)^d)}\le B$ within
  $\varepsilon$ in the $W^{s,p}((0,1)^d)$ norm. For $p=\infty$ and $s=0$
  this is Yarotsky's theorem.

* **37. Depth separation.** For the ReLU, logistic, or Heaviside
  activation there are $c,C>0$ such that for each $d\ge C$ there exist a
  probability measure $\mu$ on $\mathbb R^d$ and a function $g$, bounded by
  $2$ and computed by a network with two hidden layers of width at most
  $Cd^5$ and weights at most $Cd^C$, such that every network with one
  hidden layer of width $n\le ce^{cd}$ has $L^2(\mu)$ distance at least $c$
  from $g$ (Eldan and Shamir). If $g\in C^2([0,1]^d)$ is not affine and
  $L\ge2$, there are $c,\varepsilon_0>0$ such that, for every
  $\varepsilon\in(0,\varepsilon_0)$, every ReLU network with $L-1$ hidden
  layers and at most $c\varepsilon^{-1/(2(L-1))}$ neurons has uniform error
  at least $\varepsilon$ on $[0,1]^d$ (Yarotsky). The restriction to small
  $\varepsilon$ is necessary, since a constant approximates $g$ within
  $\sup|g|$.

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
  the linear permutation-equivariant maps
  $\mathbb R^{n\times d}\to\mathbb R^{n\times d'}$ are
  $X\mapsto X\Theta_1+n^{-1}\mathbf 1\mathbf 1^\top X\Theta_2$ with
  $\Theta_1,\Theta_2\in\mathbb R^{d\times d'}$.
  Self-attention satisfies
  $\mathop{\mathrm{Att}}(PX)=P\mathop{\mathrm{Att}}(X)$.

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
  $\{x,x'\}$.

* **40. Implicit bias of gradient descent.** For
  $\frac12\|X\theta-y\|_2^2$ with $X\in\mathbb R^{n\times p}$, gradient
  descent with constant step $0<\eta<2/\lambda_{\max}(X^\top X)$ from
  $\theta_0$ converges to $X^+y+(I-X^+X)\theta_0$. From $\theta_0=0$ this
  is the minimum-norm least-squares solution, which is the interpolant of
  item 31 when $p>n$ and $X$ has full row rank. For linearly separable data
  $(x_i,y_i)$ and the logistic loss
  $\sum_i\log(1+e^{-y_i\langle\theta,x_i\rangle})$, there is $\eta_0>0$
  such that gradient descent with any constant step $\eta\in(0,\eta_0)$,
  from any initialization, has $\|\theta_t\|\to\infty$ and
  $\theta_t/\|\theta_t\|\to\hat\theta/\|\hat\theta\|$, where $\hat\theta$
  minimizes $\|\theta\|_2$ subject to $y_i\langle\theta,x_i\rangle\ge1$
  for all $i$ (Soudry, Hoffer, Nacson, Gunasekar, and Srebro).

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
  With $b=0$ and $a>0$, exact recovery is possible if and only if $a>2$.

With the planted labels $\sigma_i\in\{-1,1\}$, **weak recovery** means
that there are $\varepsilon>0$ and labelings $\hat\sigma$ computed from
the graph with
$P\bigl(n^{-1}|\sum_i\sigma_i\hat\sigma_i|\ge\varepsilon\bigr)\to1$.
**Consistent distinction** from an Erdős–Rényi model means the existence
of graph tests whose two error probabilities tend to zero. Two sequences
of laws $P_n$ and $Q_n$ are **mutually contiguous** when, for every
sequence of events $A_n$, $P_n(A_n)\to0$ if and only if $Q_n(A_n)\to0$.

* **42. Kesten–Stigum threshold.** For fixed $a,b>0$ in the
  constant-degree regime $p=a/n$, $q=b/n$, weak recovery is possible
  if and only if $(a-b)^2>2(a+b)$, and is achievable efficiently above
  that threshold. If $(a-b)^2<2(a+b)$, the graph law is mutually
  contiguous to the law of $G(n,(a+b)/(2n))$, so consistent distinction
  is impossible.

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
  The sequence analogue is
  de Finetti's theorem, CKMA SYNOPSIS06, item 55.

Let finite graphs carry initial vertex features from a set $\mathcal X$.
The **one-dimensional Weisfeiler–Leman refinement** starts from the
initial features and replaces the color $c(v)$ of each vertex by the pair
$\bigl(c(v),\{\!\{c(u):u\in N(v)\}\!\}\bigr)$, with $\{\!\{\cdot\}\!\}$ a
multiset; $L$ rounds **distinguish** two graphs if the resulting multisets
of vertex colors differ. A **message-passing layer** replaces each vertex
feature $h_v$ by $\varphi\bigl(h_v,\{\!\{h_u:u\in N(v)\}\!\}\bigr)$ for a
map $\varphi$ that is the same at every vertex. A **message-passing
network** of depth $L$ is a composition of $L$ such layers followed by a
readout, a function of the multiset of final vertex features.

* **44. Weisfeiler–Leman bound.** If $L$ rounds of Weisfeiler–Leman
  refinement do not distinguish two graphs, then every message-passing
  network of depth $L$ gives them the same output. If $\mathcal X$ is
  countable and the maps $\varphi$ of all layers and the readout are
  injective on their domains, the network gives different outputs to any
  two graphs that $L$ rounds of refinement distinguish.

### Symmetry and graph signal

* **45. Population eigenspaces of the block model.** For a balanced
  two-group model with label vector $s\in\{-1,1\}^n$ and $1^\top s=0$,
  the conditional adjacency expectation is
  $$\mathbb E[A\mid s]=\tfrac{p+q}{2}11^\top
  +\tfrac{p-q}{2}ss^\top-pI.$$
  Its eigenvectors $1$ and $s$ have eigenvalues
  $n(p+q)/2-p$ and $n(p-q)/2-p$, respectively; every orthogonal
  direction has eigenvalue $-p$.

* **46. Permutation equivariance.** Let $F(A,X)$ be the matrix of vertex
  features produced by the layers of a message-passing network of item 44
  from the adjacency matrix $A$ and the feature matrix $X$. For every
  vertex permutation matrix $P$,
  $$F(PAP^\top,PX)=PF(A,X).$$
  Consequently the readout of the network is invariant:
  its value at $(PAP^\top,PX)$ equals its value at $(A,X)$.

### Random graphs and spectral recovery

The **Erdős–Rényi graph** $G(n,p)$ includes each of the $\binom n2$
possible edges independently with probability $p$.

* **47. Phase transitions of the Erdős–Rényi graph.** Let $p=c/n$ with a
  fixed $c>0$. If $c<1$, there is $C$ such that with probability tending
  to one every component has at most $C\log n$ vertices. If $c>1$, the
  largest component
  $C_1$ satisfies $|C_1|/n\to\zeta_c$ in probability, where
  $\zeta_c\in(0,1)$ is the positive solution of $1-\zeta=e^{-c\zeta}$,
  and there is $C$ such that with probability tending to one every other
  component has at most $C\log n$ vertices. Here $\zeta_c$ is the survival probability of a
  Galton–Watson process with Poisson($c$) offspring, CKMA SYNOPSIS06,
  item 65. For $p=(\log n+x_n)/n$, the graph is connected with
  probability tending to one if $x_n\to\infty$, and has isolated vertices
  with probability tending to one if $x_n\to-\infty$; for fixed $x_n=x$
  the probability of connectivity tends to $\exp(-e^{-x})$.

For the two-group model of item 45 with $p>q$, let $D$ be the
$n\times n$ matrix with entries $p$ within and $q$ between groups,
diagonal included, let $R=A-D$, and put $\mu=\min\{q,(p-q)/2\}$.
**Spectral clustering** labels each vertex by the sign of its coordinate in
a unit eigenvector for the second largest eigenvalue of $A$.

* **48. Spectral clustering of the block model.** If $\mu>0$, then for
  every realization of $A$, up to
  a global flip spectral clustering misclassifies at most
  $8\|R\|_{\mathrm{op}}^2/(\mu^2n)$ vertices; this rests on the
  Davis–Kahan theorem, CKMA SYNOPSIS13, item 67. There is an absolute
  constant $C$ such that $\|R\|_{\mathrm{op}}\le C\sqrt n$ with
  probability at least $1-4e^{-n}$; then at most $C'/\mu^2$ vertices are
  misclassified, with $C'=8C^2$. With $\bar d=n(p+q)/2$, the matrix Bernstein
  inequality, CKMA SYNOPSIS07, item 44, gives
  $\mathbb E\|R\|_{\mathrm{op}}\le C(\sqrt{\bar d\log n}+\log n)$; hence
  the misclassified fraction tends to zero in probability when
  $p=p_n$ and $q=q_n$ satisfy $\bar d\ge\log n$ and
  $n^2\mu^2/(\bar d\log n)\to\infty$.

<a id="synopsis-107b"></a>

## 107B. Bandits, Reinforcement Learning, Privacy, Fairness, and Distribution Shift

### Bandits and reinforcement learning

A **stochastic bandit** has $K$ arms; each play of arm $k$ yields a
reward drawn from $\nu_k$, independently of everything else, and a policy
chooses the next arm from the past arms and rewards. The **regret** after
$n$ plays is the expected difference between $n$ times the optimal mean and
the sum of the observed rewards. Write $\Delta_k$ for the gap between the
mean of arm $k$ and the optimal mean. In the **exponential-family bandit**
the laws are $\nu_k=\nu_{\theta_k}$ with
$\nu_\theta(dx)=\exp(\theta x-b(\theta))\,\lambda(dx)$ for a fixed measure
$\lambda$ on $\mathbb R$ that is not a point mass and $\theta$ in an open
interval $\Theta$ on which $b$ is finite; $\nu^\star$ is the law of an
optimal arm, and $\mathop{\mathrm{kl}}(\nu_k,\nu^\star)$ is the
Kullback–Leibler divergence.

* **49. Lai–Robbins lower bound.** Call a policy uniformly efficient if
  its regret is $o(n^\alpha)$ for every $\alpha>0$ at every configuration
  $(\theta_1,\ldots,\theta_K)\in\Theta^K$. For such a policy and every
  configuration,
  $$\liminf_{n\to\infty}\frac{\mathop{\mathrm{regret}}(n)}{\log n}
  \ge\sum_{k:\Delta_k>0}\frac{\Delta_k}
  {\mathop{\mathrm{kl}}(\nu_k,\nu^\star)}.$$

* **50. Upper confidence bounds.** Let the reward laws be supported on
  $[0,1]$. The UCB1 policy plays each arm once and then, when $t$ plays
  have been made in all, plays next an arm maximizing
  $\bar x_j+\sqrt{2\log t/n_j}$, where $n_j$ is the number of plays of
  arm $j$ so far and $\bar x_j$ their mean reward.
  For every $n\ge K$ its regret is at most
  $$8\sum_{k:\Delta_k>0}\frac{\log n}{\Delta_k}
  +\Bigl(1+\frac{\pi^2}3\Bigr)\sum_{k=1}^K\Delta_k.$$

Arm $k$ of a **Markov bandit** is a Markov chain $X^k$ on a countable
state space with a bounded reward function $r_k$; at each time one arm is
played, it collects $r_k(X^k_t)$ and moves one step, and the other arms do
not move. For a discount factor $\beta\in(0,1)$ the **Gittins index** of
arm $k$ in state $x$ is
$$G_k(x)=\sup_{\tau\ge1}\frac{\mathbb E_x\sum_{t<\tau}\beta^tr_k(X^k_t)}
{\mathbb E_x\sum_{t<\tau}\beta^t},$$
the supremum over stopping times $\tau\ge1$ of the chain of that arm.

* **51. Thompson sampling and the Gittins index.** For Bernoulli arms
  with means in $(0,1)$, a unique optimal arm, and independent uniform
  priors, Thompson sampling, which plays each arm with its posterior
  probability of being optimal, satisfies
  $$\lim_{n\to\infty}\frac{\mathop{\mathrm{regret}}(n)}{\log n}
  =\sum_{k:\Delta_k>0}\frac{\Delta_k}
  {\mathop{\mathrm{kl}}(\nu_k,\nu^\star)},$$
  the constant of item 49. For a Markov bandit with independent arms, a
  policy that always plays an arm of largest current Gittins index
  maximizes the expected discounted reward
  $\mathbb E\sum_{t\ge0}\beta^t r_{k_t}(X^{k_t}_t)$ over all policies.
  A Bernoulli bandit with independent beta priors is the Markov bandit
  whose states are the beta posteriors of the arms.

For an oblivious sequence of loss vectors $\ell_t\in[0,1]^K$, $K\ge2$,
**Exp3** with learning rate $\eta$ draws arm $I_t$ from
$p_t(i)\propto\exp(-\eta\sum_{s<t}\hat\ell_s(i))$, observes only
$\ell_t(I_t)$, and sets $\hat\ell_t(i)=\ell_t(i)1_{\{I_t=i\}}/p_t(i)$.

* **52. Adversarial bandits.** Conditionally on the past, $\hat\ell_t(i)$
  has mean $\ell_t(i)$ for every arm $i$. With $\eta=\sqrt{2\log K/(TK)}$,
  the expected regret of Exp3 after $T$ rounds against the best fixed arm
  in hindsight is at most $\sqrt{2TK\log K}$. The full-information
  comparator is item 5.

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
  let $(s_t,a_t,r_t,s_t')$ be the pair updated at step $t$ and its
  observation, where, conditionally on the past and on $(s_t,a_t)$, the
  next state $s_t'$ has law $P(\cdot\mid s_t,a_t)$ and the bounded reward
  $r_t$ has the reward law of $(s_t,a_t)$. Let the steps $\alpha_t(s,a)$
  be determined by the past and $(s_t,a_t)$, with $\alpha_t(s,a)=0$ unless
  $(s,a)=(s_t,a_t)$, $0\le\alpha_t(s,a)\le1$, and, almost surely for every
  pair, $\sum_t\alpha_t(s,a)=\infty$ and $\sum_t\alpha_t(s,a)^2<\infty$.
  Then $Q_t\to Q^\star$ almost surely.

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

* **57. Policy gradient.** In the finite discounted model with bounded
  rewards, let $\theta\mapsto\pi_\theta(a\mid s)$ be differentiable and
  strictly positive, with transitions, rewards, and initial distribution
  not depending on $\theta$. Then
  $$\nabla_\theta J(\pi_\theta)
  =\frac1{1-\gamma}\mathbb E_{d_\mu^{\pi_\theta},\pi_\theta}
  [\nabla_\theta\log\pi_\theta(A\mid S)Q^{\pi_\theta}(S,A)].$$
  Any action-independent baseline $b(S)$ may be subtracted from $Q$
  without changing this expectation.

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
  If $\varepsilon\le(1-\gamma)^{-1/2}$, the same condition on $N$
  makes an optimal policy $\hat\pi$ of the empirical model satisfy
  $\|Q^{\hat\pi}-Q^\star\|_\infty\le\varepsilon$ with probability at least
  $1-\delta$. Conversely, there are absolute constants
  $\varepsilon_0,\delta_0\in(0,1)$ and $c'>0$ and a class of models such
  that, for $\varepsilon<\varepsilon_0$ and $\delta<\delta_0$, every
  procedure that on each model of the class outputs $\hat Q$ with
  $\|\hat Q-Q^\star\|_\infty\le\varepsilon$ with probability at least
  $1-\delta$ uses at least
  $c'|S||A|\log(c'/\delta)/((1-\gamma)^3\varepsilon^2)$ samples from the
  generative model.

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
  For $\lambda=1$ the limit is the best approximation $\Pi V$.

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
  where $J^\star(\rho)$ is the optimal value from $\rho$.

### Minimax and linear bandits

* **62. Minimax regret of finite-armed bandits.** For $K\ge2$ arms and a
  horizon $n>K/(4\log(4/3))$, every strategy, possibly randomized, has
  regret at least
  $$\frac{\sqrt2-1}{\sqrt{32\log(4/3)}}\sqrt{nK}$$
  on some instance with independent Bernoulli rewards. There is an
  absolute constant $C$ such that the regret of UCB1 is at most
  $C\sqrt{Kn\log n}$ for all $n\ge\max(K,2)$ and all reward laws on
  $[0,1]$.

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
  +\log(4/\delta)\Bigr),$$
  with an absolute constant $c$. Conversely, there is a distribution over
  instances $\mu^\star$, with rewards in $[-1,1]$ and $\sigma\le1$, such
  that every algorithm has $\mathbb E R_T\ge d\sqrt T/2500$ for all
  $T\ge\max\{256,d^2/16\}$, the expectation including the draw of
  $\mu^\star$.

### Privacy, fairness, and distribution shift

Data sets are **neighboring** when one is obtained from the other by
changing a single record. A mechanism $M$ is **$\varepsilon$-differentially
private** when
$P(M(D)\in A)\le e^\varepsilon P(M(D')\in A)$ for every measurable $A$ and
every neighboring pair. It is **$(\varepsilon,\delta)$-differentially
private** when the same comparison holds with an additive $\delta$ on the
right-hand side. The **$\ell^1$ sensitivity** of a query
$f$ is the supremum of $\|f(D)-f(D')\|_1$ over neighboring pairs.

* **64. Laplace mechanism.** Let $\varepsilon>0$. If $f$ takes values in
  $\mathbb R^k$ and has
  $\ell^1$ sensitivity $\Delta>0$, the mechanism that adds an independent
  $\mathop{\mathrm{Lap}}(\Delta/\varepsilon)$ random variable to each
  coordinate is $\varepsilon$-differentially private, where
  $\mathop{\mathrm{Lap}}(b)$ is the law on the line with density
  $(1/(2b))e^{-|t|/b}$. A query of sensitivity $0$ released without noise
  is $0$-differentially private. This is Theorem 3.6 of Dwork and Roth.

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

* **66. Private mean estimation.** Consider $n$ independent observations
  from an unknown law on $[-1,1]$, the mean as target, squared error, and
  $0<\varepsilon\le1$. There are absolute constants $0<c\le C$ such that
  for all $n\ge1$ the minimax risk over all estimators computed from
  noninteractive $\varepsilon$-locally private releases (each individual
  released through an $\varepsilon$-locally private kernel, item 75) lies
  between $c\min\{1,1/(n\varepsilon^2)\}$ and
  $C\min\{1,1/(n\varepsilon^2)\}$, and the minimax risk over all
  $\varepsilon$-differentially private estimators lies between
  $c\min\{1,n^{-1}+(n\varepsilon)^{-2}\}$ and
  $C\min\{1,n^{-1}+(n\varepsilon)^{-2}\}$. The upper bound in the second
  case is attained by adding Laplace noise to the sample mean and
  clipping to $[-1,1]$.

Let $Y$ be an outcome, $A$ a group attribute, and $S$ a score, random
variables on a common probability space. The score satisfies
**separation**, or equalized odds, when
$S\perp A\mid Y$. It satisfies **sufficiency** when $Y\perp A\mid S$.
For $S\in[0,1]$, calibration within groups is the stronger numerical
condition $P(Y=1\mid S,A)=S$ almost surely, which implies sufficiency.

* **67. Incompatibility of calibration and equalized odds.** Let $Y,A$
  be binary, with $P(Y=y,A=a)>0$ for all four cells and unequal group
  base rates. If a score satisfies both separation and sufficiency,
  it determines $Y$ almost surely: $Y=g(S)$ almost surely for a
  measurable $g$. In particular, a score that is calibrated within groups
  and satisfies separation determines $Y$ almost surely.

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

### Privacy mechanisms and weighted inference

* **69. Post-processing and groups.** Any measurable randomized
  post-processing of an $(\varepsilon,\delta)$-private release, using
  only the release and fresh randomness, is again
  $(\varepsilon,\delta)$-private. If $M$ is $\varepsilon$-differentially
  private and $D,D'$ differ in at most $k$ records, then
  $P(M(D)\in A)\le e^{k\varepsilon}P(M(D')\in A)$ for every measurable
  $A$.

* **70. Gaussian mechanism.** Let a vector query have Euclidean
  sensitivity $\Delta_2$. For $0<\varepsilon<1$, $0<\delta<1$,
  and $c>0$ with $c^2>2\log(1.25/\delta)$, adding independent
  $N(0,\sigma^2)$ coordinates with $\sigma\ge c\Delta_2/\varepsilon$
  is $(\varepsilon,\delta)$-differentially private.

* **71. Exponential mechanism.** For a fixed finite output set
  $\mathcal R$, let a utility $u(D,r)$ have sensitivity $\Delta u>0$
  uniformly over $r$. Drawing an output with probability proportional
  to $\exp(\varepsilon u(D,r)/(2\Delta u))$ is
  $\varepsilon$-differentially private. With probability at least
  $1-\eta$, the released utility is within
  $$\frac{2\Delta u}{\varepsilon}
  (\log|\mathcal R|+\log(1/\eta))$$
  of the maximum $\max_ru(D,r)$.

* **72. Randomized response and a private mean.** For $\varepsilon>0$, put
  $\rho_\varepsilon=(e^\varepsilon-1)/(e^\varepsilon+1)$.
  For an individual input $x\in[-1,1]$, release $Z\in\{-1,1\}$ with
  $$P(Z=1\mid x)=\frac{1+\rho_\varepsilon x}{2}.$$
  This is $\varepsilon$-locally private and satisfies
  $\mathbb E[Z\mid x]=\rho_\varepsilon x$. For independent individuals
  and independent randomization, $\sum_iZ_i/(n\rho_\varepsilon)$ is
  unbiased for the population mean, with variance at most
  $1/(n\rho_\varepsilon^2)$. Its clipping to $[-1,1]$ has mean squared
  error at most $\min\{4,1/(n\rho_\varepsilon^2)\}$, which for
  $0<\varepsilon\le1$ is at most $C\min\{1,1/(n\varepsilon^2)\}$ with an
  absolute constant $C$.

* **73. Accuracy under bounded importance weights.** Under covariate
  shift, suppose the known density ratio satisfies $0\le w\le B$,
  and the loss is in $[0,1]$. For a fixed predictor, or conditionally
  on independent training data, the weighted mean of $n$ independent
  source validation losses is unbiased for target risk and has
  variance at most $B/n$. With probability at least $1-\delta$,
  $$|\hat R_T-R_T|\le
  \sqrt{\frac{2B\log(2/\delta)}n}
  +\frac{2B\log(2/\delta)}{3n}.$$

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
  Running AboveThreshold $c$ times in succession, each run with
  $\varepsilon/c$ in place of $\varepsilon$ and started after the
  previous run halts, is $\varepsilon$-differentially private by item 65.

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
  inputs of law $P_1$, respectively $P_2$, each released through an
  $\varepsilon$-locally private kernel, possibly depending on the earlier
  releases, the laws $M^n_{P_1}$ and $M^n_{P_2}$ of all $n$ releases
  satisfy
  $$D(M^n_{P_1}\|M^n_{P_2})+D(M^n_{P_2}\|M^n_{P_1})
  \le4n(e^\varepsilon-1)^2\|P_1-P_2\|_{\mathrm{TV}}^2.$$
  With the two-point and Fano methods of SYNOPSIS103, items 39 and 40,
  this gives the local lower bound of item 66.

### Fairness criteria and label shift

A score $S$ satisfies **independence**, or demographic parity, when
$S\perp A$.

* **76. Independence versus the conditional criteria.** If $A$ and $Y$
  are dependent, independence and sufficiency cannot both hold. If $Y$ is
  binary, $A$ and $Y$ are dependent, and $S$ and $Y$ are dependent,
  independence and separation cannot both hold. If $Y$ is binary and $S$
  is sufficient, the score $\ell(S)$ with $\ell(s)=P(Y=1\mid S=s)$ is
  calibrated within groups.

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
  Covariate shift is item 68.

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
  propagation. Stone's weight conditions carry consistency of
  response-independent forests; Scornet, Biau, and Vert treat
  response-adaptive forests in additive models. Mohri, Rostamizadeh, and Talwalkar carry AdaBoost and
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
  bound. Auer, Cesa-Bianchi, and Fischer carry UCB1, and Auer,
  Cesa-Bianchi, Freund, and Schapire carry Exp3. Puterman, and
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
(item 10), Proposition 4.6 and Theorem 4.7 with Exercise 4.3 (item 11),
Theorem 14.2 with Proposition 14.4 (item 12), and Theorem 3.3 for the
empirical-complexity bound of item 2. Devroye, Györfi, and Lugosi
supply Theorems 5.1, 5.4, and 5.6 (item 14), with their randomized
tie-breaking, and Section 22.1 with Theorem
8.3 and Theorem 22.1 (item 15). Wainwright, Theorem 13.17, Corollary
13.18, and Examples 13.19–13.20, give item 13. The hinge-loss constants in
item 11, and the critical radii for finite rank, polynomial eigenvalue
decay, and the equispaced Sobolev design in item 13, are direct
computations from those statements. The condition $P(h(X)=0)=0$ in item 11
is needed because $R(h)=P(Yh(X)\le0)$ counts $h(X)=0$ as an error; the
inequality holds for every measurable $h$ when $R(h)$ is instead the error
of $\mathop{\mathrm{sign}}h$ with a fixed value of
$\mathop{\mathrm{sign}}0\in\{-1,1\}$.

Bühlmann and van de Geer, *Statistics for High-Dimensional Data*, Hastie,
Tibshirani, and Friedman, *The Elements of Statistical Learning*,
Shalev-Shwartz and Ben-David, *Understanding Machine Learning*, Steinwart
and Christmann, *Support Vector Machines*, Vovk, Gammerman, and Shafer,
*Algorithmic Learning in a Random World*, and Efron, *Large-Scale
Inference*, are not in the local reference directory. The two-sided
sample-complexity bounds of item 1 are Theorem 6.8 of Shalev-Shwartz and
Ben-David. Item 6 is the split-conformal coverage theorem of that
literature.

#### Machine-learning models and sequential decisions

Wainwright–Jordan's tree and Bethe variational developments were consulted
for items 19 and 23. Their tree exactness does not imply convergence or
global optimality of loopy belief propagation. The boosting
statement is the squared-error line-search identity; the forest statement
is Stone's theorem for weights that do not depend on the responses, in
the form of Györfi, Kohler, Krzyżak, and Walk, Theorem 4.1, which is not
local. Scornet–Biau–Vert's response-adaptive theorem is a specialized
result, not a corollary of that theorem.

The local Grohs–Kutyniok collection, Chapter 1, was read for Theorem 1.27
on Barron approximation and the tangent-kernel discussion around
equations (1.21)–(1.23). Item 30 records Theorems 1 and 2 of
[Jacot, Gabriel, and Hongler (2018)](https://arxiv.org/abs/1806.07572),
checked online: Theorem 1 needs only a Lipschitz activation, Theorem 2
adds a bounded second derivative and a stochastically bounded integral
of the training direction, and their Section 5 notes that this holds for
the least-squares cost, whose training direction has decreasing norm.
Item 29 follows
[Schmidt-Hieber (2020)](https://arxiv.org/abs/1708.06633), checked
online: the class $\mathcal G(q,\mathbf d,\mathbf t,\boldsymbol\beta,K)$
and Hölder ball of his Section 3, the lower bound of his Theorem 3, and
the upper bound of his Theorem 1 and Corollary 1 with network sup-norm
bound $F=\max(K,1)$ and depth of order $\log n$. Item 31 gives finite-sample expected
Gaussian-design risks and assumes a limiting signal norm; item 32 permits
boundary discriminator values when claiming an attained maximum.
Bishop–Bishop supplies the probabilistic output and Gaussian-conditioning
framework for the prediction entries.

[Abbe's survey, Theorem 13 and its boundary discussion](https://jmlr.org/papers/v18/16-480.html),
was checked online for items 41 and 42. The exact-recovery equality case
differs for positive and zero between-group probabilities. For item 43,
[Janson's Theorem 8.6](https://arxiv.org/abs/1009.2376)
gives common measure-preserving pullbacks, not necessarily one invertible
relabeling. Message-passing injectivity is stated only on the domain for
which it is assumed or constructed.

Puterman and Bertsekas–Tsitsiklis supply discounted policy evaluation,
improvement, and the stochastic approximation framework. The finite-model
conditions are explicit for Bellman contraction and $Q$-learning.
Items 56 and 57 record the occupancy and score identities for those models.
The bandit entries distinguish instance-dependent logarithmic regret,
its leading divergence constant, discounted Bayesian index optimality,
and the oblivious-adversary bound. Item 50 is Theorem 1 of Auer,
Cesa-Bianchi, and Fischer, "Finite-time analysis of the multiarmed bandit
problem" (Machine Learning, 2002), checked online. The Thompson-sampling
limit in item 51 combines Theorem 1 of
[Kaufmann, Korda, and Munos (ALT 2012)](https://arxiv.org/abs/1205.4217)
(uniform priors, unique optimal arm; Theorem 1 of
[Agrawal and Goyal (AISTATS 2013)](https://arxiv.org/abs/1209.3353) is
the same upper bound) with item 49, which applies because Theorem 2 and
Appendix A of
[Agrawal and Goyal (COLT 2012)](https://arxiv.org/abs/1111.1797) give
logarithmic regret on every Bernoulli instance. The Gittins index theorem
of item 51 (Gittins, 1979) is Theorem 35.9 of
[Lattimore–Szepesvári](https://tor-lattimore.com/downloads/book/book.pdf),
with the index in the form (35.9) and the beta-posterior chain of
Example 35.8. Exp3 was introduced by Auer, Cesa-Bianchi, Freund, and
Schapire (SIAM J. Comput., 2002); the constant in item 52 is Theorem 11.2
of Lattimore–Szepesvári, whose reward-based estimator gives the same
sampling probabilities as the loss-based estimator of item 52.
Sutton–Barto and the original bandit papers were not located as local
full texts.

Dwork–Roth, Proposition 2.1 and Sections 3.2–3.5, was consulted for
post-processing, randomized response, the exponential mechanism, and
Theorem 3.22 on Gaussian noise. Item 66 assumes bounded observations
and specifies the privacy model. The local-model comparison is in
[Duchi–Jordan–Wainwright](https://arxiv.org/abs/1604.02390): the upper
bound is their Corollary 1, since bounded laws have every $k$th moment at
most $1$, and the lower bound is the two-point argument of its proof with
support $\{-1,0,1\}$. The central bounds are Theorems 1 and 3 of
[Chaudhuri, Miagkov, and Courtade (2023)](https://arxiv.org/abs/2310.13137)
with equal privacy levels, rescaled from $[-1/2,1/2]$; the upper bound
also follows from the sample mean's sensitivity $2/n$ and item 64.

Barocas–Hardt–Narayanan, the chapter on classification criteria, was read
for separation, sufficiency, and their incompatibility propositions.
Calibration is distinguished from sufficiency, and perfect prediction
is retained as an exception. Item 68 fixes the conventional factor two
in the disagreement divergence, and item 73 gives a separate variance
condition for weighted inference.

Hastie–Tibshirani–Friedman, Goodfellow–Bengio–Courville, Murphy,
Bishop's 2006 pattern-recognition book, and Lovász were not located in
the two reference directories. Bishop–Bishop's 2024 text is a different
local book and is part of the consulted source basis. Online primary
sources are identified above; local source copies are listed below.

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
and Graph Limits*, is not local. Agarwal, Brantley, Jiang, Kakade, and Sun, Theorem 1.7,
Proposition 1.15 with the primal and dual programs of Section 1.3,
Lemma 2.2, Proposition 2.1, Theorems 2.6–2.7, Lemma 10.6, Theorems
10.3 and 10.8, Theorems 5.2 and 5.4–5.5, and Lemma A.9, give items 58, 59, and 61–63. In Lemma A.9 the regressors are taken predictable, as in
Abbasi-Yadkori, Pál, and Szepesvári. Bertsekas and Tsitsiklis, Section 6.3,
Assumption 6.1 and Propositions 6.4–6.5, give item 60. Cesa-Bianchi and
Lugosi, Theorem 6.11 and its proof, give item 62; the proof bounds
the regret against the best arm in expectation on stochastic Bernoulli
instances.

Dwork and Roth, Algorithm 1 with Theorems 3.23–3.24 and Section 3.6,
give item 74. Item 75 is
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
