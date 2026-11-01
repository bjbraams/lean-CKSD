# Synopsis: Optimal transport and kernel discrepancies

Part of the [mathematical synopsis series](SYNOPSIS.md).
[Bibliographical scope and references](CKSD-bib.md#cks-111).

This synopsis follows Section 111. Subdivision 111A records the statistical
uses of Wasserstein distance: empirical and minimax rates, transport-map and
entropic estimation, semidiscrete transport, and the tangent-space geometry
of barycenters. Subdivision 111B records kernel discrepancies: mean
embeddings, characteristic kernels, comparison and metrization of
distances, kernel Stein discrepancies, conditional embeddings, and random
features.
Existence of optimal plans, Kantorovich duality, cyclical monotonicity,
completeness of $W_p$, the Kantorovich–Rubinstein formula, the
one-dimensional quantile coupling, Brenier's theorem, displacement
interpolation, the Benamou–Brenier formula, and entropic transport are
[CKMA SYNOPSIS39](../lean-CKMA/SYNOPSIS39.md), items 39–49 and 90. The heat
flow as a Wasserstein gradient flow is item 62 of that file. The representer theorem is [SYNOPSIS104](SYNOPSIS104.md), item 8, and the
Hilbertian central limit theorem is item 20 of that file. Kernel Rademacher
complexity is [SYNOPSIS107](SYNOPSIS107.md), item 9.

Throughout, for $p\ge1$, $W_p$ is the $p$-Wasserstein distance on the space
$\mathcal P_p$ of Borel probabilities with finite $p$th moment, as in
CKMA SYNOPSIS39.

Numbered definitions and results have stable identifiers. Additions take the
next free number and are placed beside related material; numbers need not
increase in reading order. Proofs are outside the scope of this synopsis.

<a id="synopsis-111a"></a>

## 111A. Optimal Transport, Wasserstein Distances, and Their Statistics

Let $\mu_n$ be the empirical measure of $n$ independent copies of a
probability $\mu$ on $\mathbb R^d$.

* **1. Empirical Wasserstein bounds.** For a probability supported in
  a fixed bounded subset of $\mathbb R^d$ and $p\ge1$,
  $$\mathbb E W_p^p(\mu_n,\mu)\le C
  \begin{cases}n^{-1/2},&p>d/2,\\
  n^{-1/2}\log(1+n),&p=d/2,\\
  n^{-p/d},&p<d/2.
  \end{cases}$$
  If only a finite $q$th moment is assumed, $q>p$, the usual
  Fournier–Guillin bound adds $C n^{-(q-p)/q}$, away from the critical
  cases $q=2p$ for $p\ge d/2$ and $q=dp/(d-p)$ for $p<d/2$,
  where logarithmic modifications are needed. These are upper bounds,
  not the exact rate for every distribution. Smooth one-dimensional
  laws can converge faster, whereas atoms can attain slower rates.

Let $\mu_1,\ldots,\mu_K\in\mathcal P_2(\mathbb R^d)$ and let
$\lambda_i>0$ sum to one. A **Wasserstein barycenter** minimizes
$\mu\mapsto\sum_{i=1}^K\lambda_i W_2^2(\mu,\mu_i)$.

* **2. Uniqueness of the barycenter.** If at least one $\mu_i$ is
  absolutely continuous, the barycenter exists and is unique.

* **3. Consistency of Brenier maps.** Let $\mu\in\mathcal P_2(\mathbb R^d)$
  be absolutely continuous and let $\nu,\nu_n\in\mathcal P_2(\mathbb R^d)$
  satisfy $W_2(\nu_n,\nu)\to0$. Let $T$ and $T_n$ be the Brenier maps pushing
  $\mu$ forward to $\nu$ and to $\nu_n$, in the sense of CKMA SYNOPSIS39,
  item 46. Then $T_n\to T$ in $L^2(\mu)$. A quantitative comparison of map
  error and target-measure error requires additional regularity; this
  consistency theorem supplies no universal rate.

A **metric measure space** is a complete separable metric space equipped
with a Borel probability. For $p\ge1$ and probabilities of finite $p$th
moment, the **Gromov–Wasserstein distance** of order $p$ is
$$
\mathop{\mathrm{GW}}_p(\mu,\nu)^p
=\inf_{\pi\in\Pi(\mu,\nu)}
\iint \bigl|d_X(x,x')-d_Y(y,y')\bigr|^p\,d\pi(x,y)\,d\pi(x',y').
$$

* **4. Gromov–Wasserstein distance.** With the normalization above,
  $\mathop{\mathrm{GW}}_p$ is a metric on compact metric probability
  spaces modulo measure-preserving isometries of their supports.
  In particular, it vanishes exactly when those supports are isomorphic.
  Extra points outside the support are invisible to the discrepancy;
  an isometry of the entire underlying spaces follows if both measures
  have full support.

For $\varepsilon>0$ let $\mathop{\mathrm{OT}}_\varepsilon(\mu,\nu)$ be the
entropic transport cost of CKMA SYNOPSIS39, item 90. The **debiased
Sinkhorn divergence** is
$$
S_\varepsilon(\mu,\nu)
=\mathop{\mathrm{OT}}_\varepsilon(\mu,\nu)
-\tfrac12\mathop{\mathrm{OT}}_\varepsilon(\mu,\mu)
-\tfrac12\mathop{\mathrm{OT}}_\varepsilon(\nu,\nu).
$$

* **5. Debiased Sinkhorn divergence.** On a compact Euclidean domain
  with quadratic cost, for every $\varepsilon>0$,
  $S_\varepsilon(\mu,\nu)\ge0$, with equality exactly when $\mu=\nu$.
  Moreover $S_\varepsilon(\mu_n,\mu)\to0$ if and only if
  $\mu_n\Rightarrow\mu$. A sufficient general setting is a compact
  metric space with Lipschitz symmetric cost whose Gibbs kernel
  $e^{-c/\varepsilon}$ is positive and universal. These hypotheses
  distinguish the theorem from a claim for arbitrary costs or tails.

### Explicit geometries and empirical inference

* **10. Barycenters on the line.** For $\mu_i\in\mathcal P_2(\mathbb R)$,
  the unique weighted barycenter has quantile function
  $$F_{\bar\mu}^{-1}(u)=\sum_i\lambda_iF_{\mu_i}^{-1}(u).$$
  More generally, for a random measure $\Lambda$ with
  $\mathbb E\int x^2\Lambda(dx)<\infty$, the population barycenter
  has quantile $\mathbb E F_\Lambda^{-1}$ almost everywhere. The quantile
  embedding
  makes this a Hilbert-space mean. Such an averaging formula does not
  hold for arbitrary multivariate transport maps.

* **11. Gaussian transport and barycenters.** For covariance matrices
  $A,B\ge0$,
  $$W_2^2(N(m,A),N(n,B))
  =\|m-n\|^2+\mathop{\mathrm{tr}}
  [A+B-2(A^{1/2}BA^{1/2})^{1/2}].$$
  If $A>0$, the optimal map is
  $x\mapsto n+A^{-1/2}(A^{1/2}BA^{1/2})^{1/2}A^{-1/2}(x-m)$.
  A barycenter of positive definite Gaussian measures is Gaussian,
  with mean $\sum_i\lambda_i m_i$ and covariance satisfying
  $$\bar A=\sum_i\lambda_i
  (\bar A^{1/2}A_i\bar A^{1/2})^{1/2}.$$
  If the $A_i$ commute, $\bar A=(\sum_i\lambda_i A_i^{1/2})^2$;
  a matrix square-root average is not the general noncommuting solution.

* **12. One-dimensional empirical transport limit.** Suppose $\mu$ is
  supported on $[a,b]$ and has a continuous density bounded above and
  below by positive constants there. Then
  $$nW_2^2(\mu_n,\mu)\Rightarrow
  \int_0^1\frac{B^0(u)^2}{f(F^{-1}(u))^2}\,du,$$
  by the quantile-process delta method. Thus $W_2(\mu_n,\mu)=O_P(n^{-1/2})$
  under these assumptions, faster than the distribution-free bound
  inferred from item 1. Atoms, gaps, and unbounded tails can change
  the rate or invalidate this integral limit.

* **13. Sliced Wasserstein distance.** Let $\sigma$ be uniform probability
  on $S^{d-1}$ and $P_\theta(x)=\theta^\top x$. Then
  $$\mathop{\mathrm{SW}}_p(\mu,\nu)
  =\left(\int W_p^p((P_\theta)_\#\mu,(P_\theta)_\#\nu)
  \,\sigma(d\theta)\right)^{1/p}$$
  defines a metric on $\mathcal P_p(\mathbb R^d)$ and is at most
  $W_p(\mu,\nu)$. Vanishing projected distances imply equality of
  the laws by continuity of characteristic functions and the
  Cramér–Wold characterization. A finite collection of directions alone
  does not determine every multivariate law.

* **18. Consistency of empirical barycenters.** Suppose independent
  identically distributed random measures $\Lambda_i$ are supported in a common compact set
  $K\subset\mathbb R^d$, and the population Fréchet functional
  $\mathbb E W_2^2(\mu,\Lambda_1)$ has a unique minimizer $\bar\mu$.
  Any sequence minimizing $n^{-1}\sum_iW_2^2(\mu,\Lambda_i)$ converges
  almost surely to $\bar\mu$ in $W_2$. Minimizers can be confined to
  the compact convex hull of $K$; uniform convergence there gives the
  argmin conclusion. Noncompact versions require suitable moment and
  compactness control.

### Minimax limits, smoothness, and smoothing

* **19. Minimax lower bounds for transport estimation.** Let $d\ge3$
  and let $\lambda$ be the uniform law on $[0,1]^d$. Every probability
  $\tilde\mu$ supported on at most $n$ points satisfies
  $$W_1(\tilde\mu,\lambda)\ge\frac{n^{-1/d}}{108\,d};$$
  in particular this holds for the empirical measure, almost surely.
  More strongly, for $n\ge8$ and every estimator $\tilde\mu_n$, that is,
  every measurable function of $n$ independent observations,
  $$\sup_\mu\mathbb E_\mu W_1(\tilde\mu_n,\mu)\ge\tfrac1{16}(2n)^{-1/d},$$
  the supremum over probabilities supported in $[0,1]^d$. Thus the rate
  $n^{-1/d}$ of item 1 for $p=1$ cannot be improved uniformly by any
  estimator. The plug-in estimator $W_1(\mu_m,\nu_n)$ of $W_1(\mu,\nu)$ from two
  independent samples has error of order $(m\wedge n)^{-1/d}$, which is
  sharp in general, and a goodness-of-fit or two-sample test based on the
  empirical $W_1$ needs thresholds, hence separations, of order at least
  $n^{-1/d}$. The
  adversarial laws in the proof are atomic; item 20 shows how smoothness
  changes the picture.

On the torus $\mathbb T^d=\mathbb R^d/(2\pi\mathbb Z)^d$ with its quotient
metric, the Sobolev space $H^s$, $s$ a positive integer, consists of
densities whose derivatives of order at most $s$ are square integrable.
For $\sigma>0$, the **smoothed Wasserstein distance** is
$W_p^{(\sigma)}(\mu,\nu)=W_p(\mu*N(0,\sigma^2I),\nu*N(0,\sigma^2I))$;
it is a metric on $\mathcal P_p(\mathbb R^d)$.

* **20. Smooth laws and smoothed distances.** Let $d\ge3$. If $\mu$ has a
  density on $\mathbb T^d$ with $H^s$ norm bounded by a constant, the
  estimator obtained by truncating the empirical Fourier series at
  frequencies $\|m\|\le M$, $M\asymp n^{1/(d+2s)}$, satisfies
  $$\mathbb E W_1(\tilde\mu_n,\mu)\lesssim n^{-(s+1)/(d+2s)}.$$
  The truncated series is a signed measure; its $W_1$-projection onto
  probability measures loses at most a factor two. Smoothing the metric
  instead of the estimator removes the curse of dimensionality from the
  exponent: for $\mu$ supported in $[-1,1]^d$,
  $$\mathbb E W_1^{(\sigma)}(\mu_n,\mu)\lesssim n^{-1/2},$$
  with a constant depending on $\sigma$ and on $d$, growing exponentially
  in $d$. That growth reflects the difficulty of item 19 and is not
  removable.

### Estimation of transport maps

Let $\mu,\nu\in\mathcal P_2(\mathbb R^d)$ with $\mu$ absolutely continuous,
and let $T=\nabla\varphi$ be the Brenier map from $\mu$ to $\nu$, with
$\varphi$ convex (CKMA SYNOPSIS39, item 46). For a convex function $\phi$
with Legendre conjugate $\phi^*$, the **semidual functional** is
$$\mathcal S(\phi)=\int\phi\,d\mu+\int\phi^*\,d\nu.$$
By Kantorovich duality (CKMA SYNOPSIS39, item 40) the Brenier potential
$\varphi$ minimizes $\mathcal S$. The **semidual estimator** minimizes the
empirical version $\int\phi\,d\mu_n+\int\phi^*\,d\nu_n$ over a chosen
class $\Phi$ of convex potentials, and estimates $T$ by $\nabla\hat\phi$.
The error is measured in $L^2(\mu)$; it bounds $W_2^2((\nabla\hat\phi)_\#\mu,\nu)$.

* **21. Semidual stability.** If $\nu=(\nabla\varphi)_\#\mu$ and $\phi$ is
  convex and twice differentiable with
  $\tfrac12I\preceq\nabla^2\phi\preceq2I$, then
  $$\tfrac14\|\nabla\phi-\nabla\varphi\|_{L^2(\mu)}^2
  \le\mathcal S(\phi)-\mathcal S(\varphi)
  \le\|\nabla\phi-\nabla\varphi\|_{L^2(\mu)}^2.$$
  Thus excess semidual risk and squared map error are comparable for
  strongly convex smooth candidates. This turns map estimation into
  empirical risk minimization. Without strong convexity and smoothness,
  Brenier's uniqueness gives identifiability but no such quantitative
  comparison.

* **22. Rates for transport-map estimation.** Let $\mu$ and $\nu$ be
  supported in the unit ball, and let $\nu=(\nabla\varphi)_\#\mu$ with
  $\varphi\in\Phi$. Suppose the potentials in $\Phi$ are uniformly bounded
  there, satisfy $\tfrac12I\preceq\nabla^2\phi\preceq2I$ in the open ball,
  and have uniform covering numbers
  $\log N(\varepsilon,\Phi)\lesssim\varepsilon^{-\gamma}\log(1+\varepsilon^{-1})$
  with $\gamma\in[0,1)$. With $n$ independent observations from each law,
  the semidual estimator satisfies
  $\mathbb E\|\nabla\hat\phi-\nabla\varphi\|_{L^2(\mu)}^2\lesssim n^{-1/2}$.
  If moreover $\Phi$ is convex and $\mu$ satisfies a Poincaré
  inequality, the rate improves to
  $$\mathbb E\|\nabla\hat\phi-\nabla\varphi\|_{L^2(\mu)}^2
  \lesssim\Bigl(\frac{\log n}{n}\Bigr)^{2/(2+\gamma)},$$
  which is $(\log n)/n$ for finite-dimensional classes. For
  nonparametric smoothness classes, Hütter and Rigollet prove the
  following. Let $\mu$ have a density bounded above and below on
  $[0,1]^d$. Let $T=\nabla f$ have Hölder norm of order $\alpha>1$
  bounded by $R$ on a neighbourhood. Let
  $M^{-1}I\preceq DT\preceq MI$, and let $T_\#\mu$ have support
  $[0,1]^d$. Then the minimax risk satisfies
  $$\inf_{\hat T}\sup\mathbb E\|\hat T-T\|_{L^2(\mu)}^2\asymp
  n^{-2\alpha/(2\alpha-2+d)}\vee n^{-1},$$
  up to a factor $(\log n)^2$ in the upper bound. A semidual estimator over
  truncated wavelet expansions attains it. The rate escapes the curse of
  dimensionality only as the smoothness grows with $d$.

### Entropic transport: duality and statistical rates

Let $\mathop{\mathrm{OT}}_\varepsilon$ be the entropic cost of CKMA SYNOPSIS39,
item 90, here with quadratic cost $c(x,y)=\|x-y\|^2$ and compactly
supported $\mu,\nu$ on $\mathbb R^d$. Let $(f,g)$ be the Schrödinger potentials
and $\pi_\varepsilon$ the optimal coupling. The **entropic map** is the
conditional mean $b_\varepsilon(x)=\mathbb E_{\pi_\varepsilon}[Y\mid X=x]$.

* **23. Entropic duality and the entropic map.** One has
  $$\mathop{\mathrm{OT}}_\varepsilon(\mu,\nu)=\sup_{f,g}\Bigl\{\int f\,d\mu+\int g\,d\nu
  -\varepsilon\iint\bigl(e^{(f(x)+g(y)-c(x,y))/\varepsilon}-1\bigr)\,
  d\mu(x)\,d\nu(y)\Bigr\},$$
  over bounded continuous $f,g$, an unconstrained strictly concave problem
  in $f\oplus g$. The Schrödinger potentials attain it. Conversely, if
  $e^{(f\oplus g-c)/\varepsilon}\,d(\mu\otimes\nu)$ is a coupling of $\mu$ and $\nu$,
  then it is the optimal coupling and $(f,g)$ is dual optimal. This is
  the entropic form of complementary slackness. Exact maximization in $g$
  for fixed $f$ gives
  $g(y)=-\varepsilon\log\int e^{(f(x)-c(x,y))/\varepsilon}\mu(dx)$, so
  Sinkhorn's iteration is alternating maximization of this dual. With the
  canonical smooth extension
  $f(x)=-\varepsilon\log\int e^{(g(y)-\|x-y\|^2)/\varepsilon}\nu(dy)$,
  $$b_\varepsilon=\nabla\Bigl(\tfrac12\|x\|^2-\tfrac12f(x)\Bigr),$$
  the gradient of a convex function. In general
  $(b_\varepsilon)_\#\mu\ne\nu$; the entropic map is the $L^2$ projection of the
  coupling onto maps, not a transport map.

* **24. Dimension-free sample complexity of entropic transport.** Let
  $\mu$ and $\nu$ be supported in a ball of radius $\tfrac12$ in
  $\mathbb R^d$. Let $\mu_n,\nu_n$ be empirical measures of independent
  samples of size $n$. Let $\hat b$ be the entropic map between them,
  extended canonically off the sample. Then
  $$\mathbb E\bigl(\mathop{\mathrm{OT}}_\varepsilon(\mu_n,\nu_n)-\mathop{\mathrm{OT}}_\varepsilon(\mu,\nu)\bigr)^2
  \lesssim\frac1n,\qquad
  \bigl|\mathbb E\mathop{\mathrm{OT}}_\varepsilon(\mu_n,\nu_n)-\mathop{\mathrm{OT}}_\varepsilon(\mu,\nu)\bigr|
  \lesssim\frac1n,$$
  $$\mathbb E\|\hat b-b_\varepsilon\|_{L^2(\mu)}^2\lesssim\frac1n.$$
  The implicit constants do not depend on the dimension through the
  exponent of $n$, but grow exponentially in $1/\varepsilon$. The bounded
  diameter and strong concavity of the dual are the operative
  hypotheses. Earlier bounds of Genevay and coauthors, and of Mena and
  Niles-Weed, give rate $n^{-1/2}$ for the cost with powers of
  $1/\varepsilon$ that grow with $d$. Such parametric rates do not transfer
  to unregularized transport as $\varepsilon\downarrow0$, by item 19.

### Semidiscrete transport

Let $\mu\in\mathcal P_2(\mathbb R^d)$ be absolutely continuous, and let
$\nu=\sum_{j=1}^m b_j\delta_{y_j}$ with distinct $y_j$ and $b_j>0$. For quadratic
cost $c$ and $g\in\mathbb R^m$, put
$g^c(x)=\min_j\bigl(c(x,y_j)-g_j\bigr)$. The **Laguerre cells**
$L_j(g)=\{x:c(x,y_j)-g_j\le c(x,y_k)-g_k\ \text{for all }k\}$ are
convex polyhedra covering $\mathbb R^d$ (a power diagram), with
overlaps of Lebesgue measure zero.

* **25. Semidiscrete dual.** The function
  $$E(g)=\int g^c\,d\mu+\sum_jb_jg_j$$
  is concave and invariant under adding a constant to all $g_j$.
  It is continuously differentiable with
  $$\frac{\partial E}{\partial g_j}=b_j-\mu(L_j(g)),$$
  and its maximum equals the optimal transport cost from $\mu$ to $\nu$.
  A vector $g$ is a maximizer exactly when every cell has mass
  $\mu(L_j(g))=b_j$. The map sending $L_j(g)$ to $y_j$ is then the optimal
  transport map, piecewise constant on the power diagram. Thus semidiscrete
  transport, such as transport to an empirical measure, is a smooth
  finite-dimensional concave maximization. Gradient and Newton methods
  apply. The differentiability uses that $\mu$ does not charge cell
  boundaries.

### Tangent space, linearization, and Fréchet means

Let $\gamma\in\mathcal P_2(\mathbb R^d)$ be absolutely continuous, and for
$\mu\in\mathcal P_2(\mathbb R^d)$ let $t_\gamma^\mu$ be the Brenier map from
$\gamma$ to $\mu$. The **tangent space** $\mathop{\mathrm{Tan}}_\gamma$ is the
closure in $L^2(\gamma;\mathbb R^d)$ of $\{s(t_\gamma^\mu-\mathrm{id}):s>0,\ \mu\in\mathcal P_2\}$.
It equals the $L^2(\gamma)$ closure of the gradients of smooth compactly
supported functions, and is therefore a linear space. The **log map** is
$\log_\gamma\mu=t_\gamma^\mu-\mathrm{id}$, and the **exponential map** is
$\exp_\gamma r=(\mathrm{id}+r)_\#\gamma$. A family $\mathcal C$ of absolutely
continuous laws is **compatible** if
$t_\gamma^\mu\circ t_\nu^\gamma=t_\nu^\mu$ in $L^2(\nu)$ for all
$\gamma,\mu,\nu\in\mathcal C$.

* **26. Tangent-space linearization.** For $\gamma$ absolutely continuous,
  $\|\log_\gamma\mu\|_{L^2(\gamma)}=W_2(\gamma,\mu)$, and
  $s\mapsto\exp_\gamma(s\log_\gamma\mu)$, $0\le s\le1$, is the constant-speed
  geodesic from $\gamma$ to $\mu$ (CKMA SYNOPSIS39, item 48). For all
  $\mu,\nu$,
  $$W_2(\mu,\nu)\le\|\log_\gamma\mu-\log_\gamma\nu\|_{L^2(\gamma)},$$
  because $(t_\gamma^\mu,t_\gamma^\nu)_\#\gamma$ couples $\mu$ and $\nu$. On a
  compatible family containing $\gamma$, equality holds, so $\log_\gamma$
  is an isometric embedding into a Hilbert space. The Fréchet mean of
  compatible $\mu_1,\ldots,\mu_N$ is then $(N^{-1}\sum_it_\gamma^{\mu_i})_\#\gamma$.
  All absolutely continuous laws on $\mathbb R$ are compatible, recovering
  item 10. A family of centered nondegenerate Gaussian laws containing
  the standard Gaussian is compatible exactly when the covariances commute,
  consistent with item 11. In
  general the inequality is strict, reflecting the nonnegative curvature
  of $W_2$ in dimension at least two.

* **27. First-order conditions for barycenters.** Let
  $F(\gamma)=\frac1{2N}\sum_{i=1}^NW_2^2(\gamma,\mu_i)$. At absolutely continuous
  $\gamma$, $F$ is Fréchet differentiable along $W_2$ with gradient
  $$F'(\gamma)=-\frac1N\sum_{i=1}^N\log_\gamma\mu_i
  =-\frac1N\sum_{i=1}^N(t_\gamma^{\mu_i}-\mathrm{id})\in\mathop{\mathrm{Tan}}_\gamma.$$
  An absolutely continuous $\gamma$ with $F'(\gamma)=0$ is a **Karcher
  mean**. That is, $N^{-1}\sum_it_\gamma^{\mu_i}=\mathrm{id}$ holds $\gamma$-almost
  everywhere. If one $\mu_i$ has a bounded density, the Fréchet mean is
  absolutely continuous and hence a Karcher mean. The converse can fail,
  but holds under regularity. Suppose the $\mu_i$ and $\gamma$ have bounded,
  strictly positive densities on an open convex $U$. Suppose further that
  $U=\mathbb R^d$ with Hölder continuous densities, or that $U$ is bounded
  with densities bounded below. Then a Karcher mean is the Fréchet mean.
  The Agueh–Carlier criterion is sufficient in general. Let the $\mu_i$
  be absolutely continuous. Suppose the closed convex potentials $\phi_i$
  of the maps $t_\gamma^{\mu_i}$ satisfy
  $N^{-1}\sum_i\phi_i(x)\le\tfrac12\|x\|^2$ everywhere, with equality
  $\gamma$-almost everywhere, then $\gamma$ is the unique Fréchet mean.

* **28. Procrustes iteration for barycenters.** Start from an absolutely
  continuous $\gamma_0$ and set
  $\gamma_{j+1}=\bigl(N^{-1}\sum_it_{\gamma_j}^{\mu_i}\bigr)_\#\gamma_j$. This is
  steepest descent for $F$ with unit step. That step minimizes the bound
  $F(\gamma_{j+1})-F(\gamma_j)\le-\|F'(\gamma_j)\|^2(\tau-\tau^2/2)$, and
  steps in $[0,1]$ preserve absolute continuity. If one $\mu_i$ has a
  bounded density, then $F(\gamma_j)$ decreases and the iterates stay in
  a $W_2$-compact set. Every limit point is a Karcher mean. If $F$ has a
  unique stationary point, then $\gamma_j\to\bar\mu$ in $W_2$, and the
  maps $t_{\gamma_j}^{\mu_i}$ converge uniformly on compacta of full
  measure. For positive definite Gaussian laws the iteration converges to
  the barycenter of item 11. It is the Wasserstein analogue of generalized
  Procrustes analysis: register to the template through log maps,
  average linearly, retract by the exponential map.

<a id="synopsis-111b"></a>

## 111B. Kernel Mean Embeddings and Integral Probability Metrics

Let $\mathcal F$ be a class of real functions. The **integral probability
metric** induced by $\mathcal F$ is
$$\gamma_{\mathcal F}(\mu,\nu)
=\sup_{f\in\mathcal F}\Bigl|\int f\,d\mu-\int f\,d\nu\Bigr|.$$
Let $\mathcal H$ be a separable reproducing-kernel Hilbert space on a
Polish space with a bounded continuous kernel $k$, and let
$\Phi(\mu)=\int k(x,\cdot)\,\mu(dx)$ be the **kernel mean embedding**,
whenever the integral converges in $\mathcal H$. The **maximum mean
discrepancy** is $\mathop{\mathrm{MMD}}(\mu,\nu)=\|\Phi(\mu)-\Phi(\nu)\|_{\mathcal H}$.
The kernel is **characteristic** when $\Phi$ is injective on the space of
Borel probabilities.

* **6. Maximum mean discrepancy.** The discrepancy equals the integral
  probability metric over the unit ball of $\mathcal H$, and
  $$
  \mathop{\mathrm{MMD}}(\mu,\nu)^2
  =\mathbb E k(X,X')+\mathbb E k(Y,Y')-2\mathbb E k(X,Y)
  $$
  for independent copies $X,X'\sim\mu$ and $Y,Y'\sim\nu$. The Gaussian and
  Laplace kernels on $\mathbb R^d$ are characteristic. A continuous
  translation-invariant positive definite kernel on $\mathbb R^d$ is
  characteristic when the support of its spectral measure is all of
  $\mathbb R^d$; item 29 gives the converse and further criteria.

For independent samples of equal size $n\ge2$, use the unbiased estimator
$$\mathop{\mathrm{MMD}}_{u,n}^2
=\frac{\sum_{i\ne j}k(X_i,X_j)+\sum_{i\ne j}k(Y_i,Y_j)}{n(n-1)}
-\frac2{n^2}\sum_{i,j}k(X_i,Y_j).$$
The biased estimator $\mathop{\mathrm{MMD}}_{b,n}^2$ is
$\|\Phi(\mu_n)-\Phi(\nu_n)\|_{\mathcal H}^2$. Let
$(\lambda_j)_{j\ge1}$ be the eigenvalues of the integral operator of the
centered kernel $\tilde k(x,y)=k(x,y)-\mathbb Ek(x,X')-\mathbb Ek(X,y)+\mathbb Ek(X,X')$
on $L^2(\mu)$.

* **7. Limits of the empirical discrepancy.** For the bounded kernel
  above, under $\mu=\nu$,
  $$n\mathop{\mathrm{MMD}}_{u,n}^2\Rightarrow
  2\sum_j\lambda_j(Z_j^2-1),\qquad
  n\mathop{\mathrm{MMD}}_{b,n}^2\Rightarrow2\sum_j\lambda_jZ_j^2.$$
  Here $Z_j$ are independent standard normals and $\lambda_j$ are the
  eigenvalues of the centered one-sample kernel specified above.
  Under a fixed alternative, with $\Delta=\Phi(\mu)-\Phi(\nu)$,
  the $\sqrt n$-normalized centered unbiased statistic has a normal
  limit with variance
  $$4\mathop{\mathrm{Var}}_\mu\langle k(X,\cdot),\Delta\rangle
  +4\mathop{\mathrm{Var}}_\nu\langle k(Y,\cdot),\Delta\rangle.$$
  This variance may be zero, even for a characteristic kernel and unequal
  laws. A nondegenerate normal limit requires it to be positive.

On $\mathbb R^d$, with $X,X'$ independent copies of $\mu$ and $Y,Y'$
independent copies of $\nu$, all four variables independent, the **energy
distance** is
$$
D^2(\mu,\nu)
=2\mathbb E\|X-Y\|-\mathbb E\|X-X'\|-\mathbb E\|Y-Y'\|,
$$
when the first moments are finite. For a pair $(X,Y)$, let $a(x,x')$ be $\|x-x'\|$ centered in both
arguments under the marginal law of $X$, and define $b(y,y')$ similarly.
The squared **distance covariance** is
$\mathcal V^2(X,Y)=\mathbb E[a(X,X')b(Y,Y')]$ for independent copies
of the pair, whenever the expectations exist. Finite second moments are
a sufficient condition. This is not the ordinary Euclidean energy distance
on the concatenated vector space.

* **8. Energy distance and independence.** For laws on $\mathbb R^d$
  with finite first moment, $D^2(\mu,\nu)\ge0$, with equality exactly
  when $\mu=\nu$. For
  $$k_0(x,y)=\tfrac12(\|x\|+\|y\|-\|x-y\|),$$
  one has $D^2(\mu,\nu)=2\mathop{\mathrm{MMD}}_{k_0}(\mu,\nu)^2$.
  Under the stated sufficient moment condition, $\mathcal V^2(X,Y)$
  is nonnegative and vanishes exactly at independence. With these
  distance-induced kernels on the two coordinates,
  $\mathcal V^2(X,Y)=4\mathop{\mathrm{HSIC}}_{k_0,\ell_0}(X,Y)$.
  The factor follows by centering each kernel, which gives $-a/2$
  and $-b/2$, respectively.

Let $k$ and $\ell$ be kernels on the two coordinates of a pair $(X,Y)$, and
let $\mathcal H\otimes\mathcal G$ be the product reproducing-kernel Hilbert
space. The **Hilbert–Schmidt independence criterion** is the
squared Hilbert–Schmidt norm of the cross-covariance operator from
$\mathcal G$ to $\mathcal H$, equivalently the squared maximum mean
discrepancy between the joint law and the product of the marginals for
the product kernel $k\otimes\ell$.

* **9. Hilbert–Schmidt independence criterion.** For bounded continuous
  kernels, assume the product kernel is characteristic on the product
  space, as for Gaussian kernels on Euclidean coordinates. Then HSIC
  vanishes if and only if $X$ and $Y$ are independent. An unbiased
  estimator based on paired observations is a $U$-statistic of order
  four, because both marginal embeddings must also be estimated.
  Under independence its first projection vanishes and its scaled limit
  is a centered weighted chi-squared series. Under alternatives its
  $\sqrt n$ limit is normal, possibly degenerate. The biased Gram-matrix
  estimator in item 17 has an uncentered null limit.

### Kernel estimation, witnesses, and test calibration

* **14. Empirical kernel means.** If $k(x,x)\le\kappa^2$, then
  $$\mathbb E\|\Phi(\mu_n)-\Phi(\mu)\|_{\mathcal H}^2
  =\frac1n\left(\mathbb E k(X,X)-\|\Phi(\mu)\|_{\mathcal H}^2\right)
  \le\frac{\kappa^2}{n}.$$
  With probability at least $1-\delta$,
  $$\|\Phi(\mu_n)-\Phi(\mu)\|_{\mathcal H}
  \le\frac\kappa{\sqrt n}
  +\kappa\sqrt{\frac{2\log(1/\delta)}n}.$$
  The second statement follows from bounded differences. The constants
  do not contain the input dimension, although the chosen kernel's
  ability to distinguish the alternatives still matters.

* **15. Witness function.** If $\Delta=\Phi(\mu)-\Phi(\nu)\ne0$, the
  function attaining the MMD supremum is
  $$f^*(x)=\frac{\mathbb E_\mu k(x,X)-\mathbb E_\nu k(x,Y)}
  {\|\Delta\|_{\mathcal H}}.$$
  It has RKHS norm one, and its mean difference is the MMD.
  The unnormalized numerator describes where the distributions differ
  at the resolution selected by the kernel.

* **16. Permutation calibration.** Under equality of two independent
  sample laws, labels are uniform over all allocations of the pooled
  observations to the two fixed sample sizes. Recomputing any fixed
  statistic under those allocations gives a test of conditional level
  at most $\alpha$, or exactly $\alpha$ with boundary randomization.
  This applies to MMD, energy, and empirical transport statistics
  without estimating their asymptotic null laws. For independence
  testing, permuting one coordinate of independent observed pairs
  gives the analogous calibration under the product-law null.

* **17. Gram-matrix independence statistic.** Let $K,L$ be the Gram
  matrices of the two coordinates of $n$ independent pairs and put
  $H=I-11^\top/n$. The biased HSIC estimator is
  $$\widehat{\mathop{\mathrm{HSIC}}}_b=n^{-2}\mathop{\mathrm{tr}}(KHLH).$$
  Under independence its $n$-scaled limit is
  $\sum_{r,s}\lambda_r\eta_sZ_{rs}^2$, where $\lambda_r,\eta_s$
  are eigenvalues of the two centered marginal kernel operators.
  The unbiased order-four estimator has the corresponding centered
  series $\sum_{r,s}\lambda_r\eta_s(Z_{rs}^2-1)$.
  There is one sample of pairs here, unlike the two independent
  samples and factor two in item 7.

### Characteristic kernels and comparison of metrics

Reproducing-kernel Hilbert spaces and the Moore–Aronszajn theorem are
[CKMA SYNOPSIS21](../lean-CKMA/SYNOPSIS21.md), item 53; Mercer's expansion
is [CKMA SYNOPSIS25](../lean-CKMA/SYNOPSIS25.md), item 8; Bochner's theorem
is recalled in [SYNOPSIS108](SYNOPSIS108.md), item 46. A bounded measurable
kernel $k$ on a topological space is **integrally strictly positive definite**
if $\iint k\,d\eta\,d\eta>0$ for every finite nonzero signed Borel measure
$\eta$. A continuous kernel on a compact metric space is **universal** if its
reproducing-kernel Hilbert space is dense in the continuous functions for
the supremum norm.

* **29. Criteria for characteristic kernels.** For a bounded measurable
  kernel, there exist distinct probabilities $\mu\ne\nu$ with
  $\mathop{\mathrm{MMD}}(\mu,\nu)=0$ exactly when some finite nonzero signed
  measure $\eta$ of total mass zero has $\iint k\,d\eta\,d\eta=0$. Hence:
  (a) integrally strictly positive definite kernels are characteristic, for
  example the Gaussian, Laplace, and inverse multiquadric kernels
  $(c^2+\|x-y\|^2)^{-\beta}$, $c,\beta>0$, on $\mathbb R^d$;
  (b) universal kernels on compact metric spaces are characteristic;
  (c) let $k(x,y)=\psi(x-y)$ with $\psi$ bounded, continuous, and positive
  definite on $\mathbb R^d$, with spectral measure $\Lambda$. Then $k$ is
  characteristic **if and only if** $\mathop{\mathrm{supp}}\Lambda=\mathbb R^d$. This is
  the converse of the sufficient condition in item 6. In particular, every
  nonzero such $\psi$ of compact support is characteristic, since its
  Fourier transform is analytic. The sinc kernel, with band-limited
  spectrum, is not characteristic.
  (d) Polynomial kernels see only finitely many moments. For instance, for
  $k(x,y)=(1+x^\top y)^2$,
  $$\mathop{\mathrm{MMD}}^2(\mu,\nu)=2\|m_\mu-m_\nu\|^2
  +\|\Sigma_\mu-\Sigma_\nu+m_\mu m_\mu^\top-m_\nu m_\nu^\top\|_F^2,$$
  with means $m$ and covariances $\Sigma$. This vanishes for distinct laws
  with equal first two moments.

On a metric space $(M,\rho)$, write $\|f\|_{\mathrm{BL}}=\sup|f|+\mathop{\mathrm{Lip}}(f)$.
The **Dudley metric** $\beta$ is the integral probability metric over
$\{\|f\|_{\mathrm{BL}}\le1\}$. Let $d_{\mathrm{TV}}(\mu,\nu)=\sup_A|\mu(A)-\nu(A)|$
as in [CKMA SYNOPSIS06](../lean-CKMA/SYNOPSIS06.md), and let $W_1$ be the
Kantorovich–Rubinstein integral probability metric over $1$-Lipschitz
functions (CKMA SYNOPSIS39, item 44).

* **30. Comparison of distances between distributions.** Let $k$ be
  measurable with $\sup_xk(x,x)\le C$, and put
  $\tilde\rho(x,y)=\|k(\cdot,x)-k(\cdot,y)\|_{\mathcal H}$. Then
  $$\mathop{\mathrm{MMD}}(\mu,\nu)\le\inf_{\pi\in\Pi(\mu,\nu)}\int\tilde\rho\,d\pi,
  \qquad
  \mathop{\mathrm{MMD}}(\mu,\nu)\le2\sqrt C\,d_{\mathrm{TV}}(\mu,\nu).$$
  If $\tilde\rho\le L\rho$, then $\mathop{\mathrm{MMD}}\le L\,W_1$. For the
  Gaussian kernel $e^{-\|x-y\|^2/(2\sigma^2)}$ one may take $L=1/\sigma$.
  Moreover $\beta\le W_1$, $\beta\le2d_{\mathrm{TV}}$, and on a bounded space
  $W_1\le\mathop{\mathrm{diam}}(M)\,d_{\mathrm{TV}}$. On a separable metric space,
  $\beta$ metrizes weak convergence and is equivalent to the Prokhorov
  metric. Wasserstein and total variation are strictly stronger. For
  $\mu_n=(1-\frac1n)\delta_0+\frac1n\delta_n$ on $\mathbb R$, $\mu_n\Rightarrow\delta_0$
  while $W_1(\mu_n,\delta_0)=1$. For the Gaussian, Laplace, or inverse
  multiquadric kernel, $\mathop{\mathrm{MMD}}(\mu_n,\delta_0)\to0$. These
  inequalities hold whether or not the kernel is characteristic.

* **31. Metrization of weak convergence.** For a bounded continuous
  characteristic kernel on a Polish space, $\mu_n\Rightarrow\mu$ implies
  $\mathop{\mathrm{MMD}}(\mu_n,\mu)\to0$. Conversely, if $(\mu_n)$ is tight and
  $\mathop{\mathrm{MMD}}(\mu_n,\mu)\to0$, then $\mu_n\Rightarrow\mu$, by
  Prokhorov's theorem (CKMA SYNOPSIS06, item 17). Without tightness, two
  sufficient conditions are standard. (a) On a compact metric space, the
  MMD of a continuous universal kernel metrizes the weak topology on the
  probabilities. (b) On $\mathbb R^d$, let $k(x,y)=\psi(x-y)$, where
  $\psi\in C_0\cap L^1$ is real, bounded, and strictly positive definite with
  Fourier transform $\hat\psi$. If
  $\int(\hat\psi(\omega)(1+\|\omega\|^2)^l)^{-1}\,d\omega<\infty$ for some
  integer $l$, the MMD metrizes weak convergence. This covers the Matérn
  family. It does not cover the Gaussian kernel, whose spectrum decays too
  fast for this criterion. For a kernel that is not characteristic, the
  MMD is not even a metric, as in item 29(d).

### Kernel Stein discrepancies

Let $P$ have a positive continuously differentiable density $p$ on
$\mathbb R^d$ with **score** $b=\nabla\log p$. The **Langevin Stein
operator** acts on $g:\mathbb R^d\to\mathbb R^d$ by
$(\mathcal T_Pg)(x)=\langle g(x),b(x)\rangle+\nabla\cdot g(x)$. For a kernel $k$
with reproducing-kernel Hilbert space $\mathcal H$, the **kernel Stein set**
consists of $g=(g_1,\ldots,g_d)$ with $g_j\in\mathcal H$ and
$\sum_j\|g_j\|_{\mathcal H}^2\le1$. The **kernel Stein discrepancy** of a
probability $\mu$ is
$\mathop{\mathrm{KSD}}(\mu)=\sup_g|\mathbb E_\mu(\mathcal T_Pg)(X)|$.
It depends on $P$ only through the score, so normalizing constants are not
needed. The **Stein kernel** is
$$k_P(x,y)=\sum_{j=1}^d\bigl[b_j(x)b_j(y)k(x,y)+b_j(x)\partial_{y_j}k(x,y)
+b_j(y)\partial_{x_j}k(x,y)+\partial_{x_j}\partial_{y_j}k(x,y)\bigr].$$

* **32. Kernel Stein discrepancy.** Let $k$ be bounded with bounded
  continuous derivatives $\partial_{x_j}k$, $\partial_{y_j}k$,
  $\partial_{x_j}\partial_{y_j}k$, and suppose the score is integrable
  under $P$. Then $\mathbb E_P(\mathcal T_Pg)(Z)=0$ for every $g$ in the
  kernel Stein set. If $\mathbb E_\mu k_P(X,X)<\infty$, then
  $$\mathop{\mathrm{KSD}}(\mu)^2=\mathbb E\,k_P(X,X'),\qquad X,X'\ \text{independent with law }\mu.$$
  For an empirical or weighted sample this is a double sum over sample
  pairs. Each coordinate term is a maximum mean discrepancy between $\mu$
  and $P$ for a kernel whose $P$-embedding vanishes. The associated
  degenerate $U$-statistic is the kernel goodness-of-fit statistic of Liu,
  Lee, and Jordan, and of Chwialkowski, Strathmann, and Gretton. Its limit
  theory follows SYNOPSIS103, items 27–28.

A target $P$ is **distantly dissipative** if
$\liminf_{r\to\infty}\kappa(r)>0$, where
$\kappa(r)=\inf\{-2\langle b(x)-b(y),x-y\rangle/\|x-y\|^2:\|x-y\|=r\}$.
Examples are finite Gaussian mixtures with a common covariance and laws
that are strongly log-concave outside a compact set.

* **33. Convergence control by kernel Stein discrepancies.** Let $P$ be
  distantly dissipative with Lipschitz score.
  (a) If $k$ has bounded continuous derivatives up to order two in each
  argument and $\mathbb E_P\|b(Z)\|^2<\infty$, then $W_1(\mu_m,P)\to0$
  implies $\mathop{\mathrm{KSD}}(\mu_m)\to0$.
  (b) For the inverse multiquadric kernel $(c^2+\|x-y\|^2)^\beta$ with
  $c>0$ and $\beta\in(-1,0)$, $\mathop{\mathrm{KSD}}(\mu_m)\to0$ implies $\mu_m\Rightarrow P$.
  (c) For a translation-invariant $C^2$ kernel with nonvanishing
  generalized Fourier transform, the same conclusion holds for
  uniformly tight sequences, and for all sequences when $d=1$.
  (d) Tightness is the real issue. Let $d\ge3$, $P=N(0,I)$, and let the
  kernel and its first derivatives decay like $o(r^{-\alpha})$ at distance
  $r$, with $\alpha=(\tfrac12-\tfrac1d)^{-1}$. Then
  $\mathop{\mathrm{KSD}}$ can tend to zero along sequences that converge to no
  probability. This includes the Gaussian, Matérn, and compactly
  supported Wendland kernels. The slowly decaying inverse multiquadric
  of (b) generates coercive test functions that enforce tightness.

### Conditional embeddings and random features

Let $k$ on $\mathcal X$ and $\ell$ on $\mathcal Y$ be kernels with
reproducing-kernel Hilbert spaces $\mathcal H$ and $\mathcal G$, and let
$(X,Y)$ be a random pair with $\mathbb E k(X,X)<\infty$ and
$\mathbb E\ell(Y,Y)<\infty$. The (uncentered) **covariance operators** are
$C_{XX}f=\mathbb E[k(\cdot,X)f(X)]$ on $\mathcal H$ and
$C_{XY}g=\mathbb E[k(\cdot,X)g(Y)]$ from $\mathcal G$ to $\mathcal H$, with
adjoint $C_{YX}$.

* **34. Conditional mean embeddings.** If $g\in\mathcal G$ and
  $x\mapsto\mathbb E[g(Y)\mid X=x]$ belongs to $\mathcal H$, then
  $$C_{XX}\,\mathbb E[g(Y)\mid X=\cdot\,]=C_{XY}g.$$
  Suppose this holds for every $g\in\mathcal G$. Suppose also that
  $C_{XX}$ is injective and $k(x,\cdot)$ lies in its range. Then
  $U_{Y\mid x}=C_{YX}C_{XX}^{-1}k(x,\cdot)\in\mathcal G$ satisfies
  $\mathbb E[g(Y)\mid X=x]=\langle g,U_{Y\mid x}\rangle_{\mathcal G}$. This is
  the **conditional mean embedding**. The hypothesis can fail: for
  Gaussian kernels and independent $X,Y$ the conditional expectations are
  nonzero constants, which do not lie in a Gaussian reproducing-kernel
  Hilbert space. One therefore uses the regularized empirical estimator
  $$\hat U_{Y\mid x}=\sum_{i=1}^n\beta_i(x)\,\ell(y_i,\cdot),\qquad
  \beta(x)=(K+n\lambda I)^{-1}\bigl(k(x,x_i)\bigr)_{i=1}^n,$$
  with Gram matrix $K$. This is kernel ridge regression of the feature
  $\ell(Y,\cdot)$ on $X$, a vector-valued form of the estimator in
  SYNOPSIS107, item 37. The weights need be neither
  positive nor normalized. Its rates are slower than the $n^{-1/2}$ rate
  of marginal embeddings in item 14.

* **35. Random Fourier features.** Let $k(x,y)=\psi(x-y)$ be continuous
  and positive definite on $\mathbb R^d$ with $\psi(0)=1$, so its spectral
  measure $\Lambda$ is a probability. Let $\omega_1,\ldots,\omega_D\sim\Lambda$
  and $b_1,\ldots,b_D$ uniform on $[0,2\pi]$ be independent. Put
  $z(x)=\sqrt{2/D}\,(\cos(\omega_j^\top x+b_j))_{j\le D}$. Then
  $\mathbb E\,z(x)^\top z(y)=k(x,y)$. For fixed $x,y$,
  $\mathbb P(|z(x)^\top z(y)-k(x,y)|\ge\varepsilon)\le2e^{-D\varepsilon^2/4}$ by
  Hoeffding's inequality. If $\sigma^2=\int\|\omega\|^2\Lambda(d\omega)<\infty$
  and $M\subset\mathbb R^d$ is compact, then
  $$\mathbb P\Bigl(\sup_{x,y\in M}|z(x)^\top z(y)-k(x,y)|\ge\varepsilon\Bigr)
  \le2^8\Bigl(\frac{\sigma\mathop{\mathrm{diam}}M}{\varepsilon}\Bigr)^2
  \exp\Bigl(-\frac{D\varepsilon^2}{4(d+2)}\Bigr),$$
  as stated by Rahimi and Recht; later analyses refine the constants.
  Hence $D$ of order $d\varepsilon^{-2}\log(\sigma\mathop{\mathrm{diam}}M/\varepsilon)$ features
  suffice for uniform error $\varepsilon$. For laws on $M$, the squared MMD
  of the feature map $z$ is
  $\|\int z\,d\mu-\int z\,d\nu\|^2$. It is computable in linear time and
  differs from $\mathop{\mathrm{MMD}}_k^2$ by at most $4\varepsilon$ on that event. For
  the Gaussian kernel $e^{-\gamma\|x-y\|^2}$, $\sigma^2=2d\gamma$.

## Reference guide

### Correspondence with the subdivisions

- **[111A](#synopsis-111a)**: Villani, Santambrogio, and Ambrosio, Gigli, and
  Savaré carry the analytic theory already numbered in CKMA SYNOPSIS39.
  Peyré and Cuturi carry computational optimal transport and entropic
  regularization. Fournier and Guillin carry empirical Wasserstein rates.
  Agueh and Carlier carry barycenters. Mémoli carries the Gromov–Wasserstein
  distance. Feydy, Séjourné, Vialard, and Peyré carry the debiased Sinkhorn
  divergence.
- **[111B](#synopsis-111b)**: Gretton, Borgwardt, Rasch, Schölkopf, and Smola
  carry the maximum mean discrepancy and its limits. Sejdinovic, Sriperumbudur,
  Gretton, and Fukumizu carry the equivalence of energy distance and a
  kernel discrepancy. Székely, Rizzo, and Bakirov carry distance covariance.
  Gretton, Bousquet, Smola, and Schölkopf carry the Hilbert–Schmidt
  independence criterion.

### Source comparisons and local copies

Panaretos–Zemel is present in `ReferencesSuppl`. Section 1.6.3, the
one-dimensional barycenter theorem in Section 3.2.2, and the Gaussian
covariance equation in Section 5.4.1 were read for items 10 and 11.
Chewi–Niles-Weed–Rigollet is also present there; Chapter 2 develops the
distribution-free empirical bounds and why they need not be sharp for
each law. The quantile-process limit in item 12 specializes SYNOPSIS103,
items 5 and 26, under compact-support density bounds.

For item 1, [Fournier–Guillin, Theorem 1](https://arxiv.org/abs/1312.2128),
was read online. It gives upper bounds with moment remainders, not an
exact rate for every measure. The bounded-domain positivity statement
in item 5 follows [Feydy and coauthors, Theorem 1](https://proceedings.mlr.press/v89/feydy19a.html).
The entropic cost convention is fixed by CKMA SYNOPSIS39, item 90;
debiasing subtracts the two self-costs.

[Gretton and coauthors, Theorem 12](https://www.jmlr.org/papers/v13/gretton12a.html),
was checked for the equal-sample normalization in item 7. Centered
one-sample kernel eigenvalues give the factor two there. The generic
projection argument is SYNOPSIS103, items 27–28. Empirical kernel means,
witnesses, and permutation calibration are the elementary Hilbert-space
and exchangeability consequences recorded in items 14–16.

Energy distance uses a distance-induced kernel with its explicit factor
in item 8. Distance covariance uses products of centered coordinate
distances; the Euclidean energy distance of concatenated pairs is a
different discrepancy. HSIC is the squared norm convention, its unbiased
estimator has order four, and a nonzero discrepancy does not by itself
force a positive first-projection variance. The energy–kernel comparison
is treated by Sejdinovic and coauthors, listed in the bibliography; that
paper was not consulted as a local full text in this expansion.

For the third expansion (items 19–35) the following passages were read.
In the local Chewi–Niles-Weed–Rigollet: Section 2.5 (plug-in estimation and
testing), Theorems 2.14–2.15 (lower bounds), Proposition 2.17 and
Theorem 2.18 (smooth torus estimator and its projection), Definition 2.23
and Theorem 2.24 (smoothed Wasserstein), Section 2.8.2 (MMD and Gaussian
characteristic kernels), all for items 19–20. Theorem 3.1, Assumption 3.3,
condition (3.5), Theorems 3.7 and 3.15, and the discussion in Section 3.7
were read for items 21–22. Propositions 4.3 and 4.5, the Sinkhorn updates
(4.11)–(4.12), Theorems 4.9–4.11, Exercise 3, and Section 4.5 were read for
items 23–24. The Hütter–Rigollet minimax statement in item 22 was checked
against [Hütter and Rigollet, Theorems 2, 6, and 8](https://arxiv.org/abs/1905.05828),
read online. The gradient of the entropic potential in item 23 was
recomputed from the Gibbs form. The cost $\|x-y\|^2$ carries no factor
one half. Peyré–Cuturi, Section 5.2, eqs. (5.6)–(5.8), gives the
semidiscrete dual, the Laguerre cells, and the gradient formula of item 25.
Panaretos–Zemel, Section 2.3.1 and Definition 2.3.1 with the Gaussian
compatibility example, and Theorem 3.1.9 were read for item 26.
Proposition 3.1.10 and Theorems 3.1.14–3.1.15 were read for item 27.
Lemmas 5.1.1–5.1.2, Algorithm 1, Theorems 5.3.1 and 5.3.3, and
Corollary 5.3.2 were read for item 28. The text states item 27 with equal
weights $1/N$, as here.

For 111B, [Sriperumbudur, Gretton, Fukumizu, Schölkopf, and Lanckriet,
“Hilbert Space Embeddings and Metrics on Probability Measures” (JMLR 11,
2010)](https://www.jmlr.org/papers/v11/sriperumbudur10a.html) was read online.
Lemma 8, Theorem 7, Theorem 9, Corollary 10, and the polynomial-kernel
example of Section 3 were used for item 29. Proposition 20, Theorem 21,
and the Gibbs–Su relations of Section 5 were used for item 30. That paper's total variation is twice
$d_{\mathrm{TV}}$, and the factor in item 30 is adjusted accordingly.
Theorems 23–24 were used for item 31. The local Berlinet–Thomas-Agnan,
Chapter 4, Section 7, Theorems 100–101 (after Guilbart), give the
compact-space metrization in item 31(a). The tightness argument in item 31
is elementary. [Gorham and Mackey, “Measuring Sample Quality with Kernels”
(ICML 2017)](https://arxiv.org/abs/1703.01717) was read online for
items 32–33: Propositions 1, 2, and 9, Definition 4, and Theorems 5–8.
The [Muandet–Fukumizu–Sriperumbudur–Schölkopf review](https://arxiv.org/abs/1605.09522)
was read online. Section 3.2 (Theorem 3.2), Section 4.1 (Definition 4.1,
Theorems 4.1–4.2, and footnote 2 on the Gaussian counterexample),
Theorem 3.4, and Section 3.3.1 were used for items 14, 29, and 34.
[Rahimi and Recht, “Random Features for Large-Scale Kernel Machines”
(NIPS 2007)](https://people.eecs.berkeley.edu/~brecht/papers/07.rah.rec.nips.pdf),
Claim 1 and the Hoeffding remark preceding it, was read online for
item 35. The linear-time MMD consequence there is a triangle-inequality
corollary. Other papers named in items 24 and 32 (Genevay and coauthors;
Mena and Niles-Weed; Liu, Lee, and Jordan; Chwialkowski, Strathmann, and
Gretton) are cited through these sources and were not read here.

Local sources and online papers are distinguished here. The local transport
books supply the analytic background; missing local copies of an original
paper were not taken to preclude consulting its primary online version.

Local texts directly consulted or identified for this selection:

- [Panaretos and Zemel, *An Invitation to Statistics in Wasserstein Space*](../lean-CKMA/ReferencesSuppl/PanaretosZemel2020InvitationStatisticsWassersteinSpace-Springer.BriefsPMS.pdf).
  The one-dimensional and Gaussian geometries and barycenter formulas were read,
  together with the tangent bundle (Section 2.3), Fréchet means and Karcher
  means (Sections 3.1.4–3.1.6), and the steepest-descent algorithm (Chapter 5).
- [Chewi, Niles-Weed, and Rigollet, *Statistical Optimal Transport*](../lean-CKMA/ReferencesSuppl/ChewiNilesWeedRigollet2025StatisticalOptimalTransportÉcoledÉtéProbabilitésSaintFlourXLIX2019-Springer.LNM2364.pdf).
  Chapter 2 was consulted for empirical measures and dimension-dependent bounds,
  including the lower bounds and smoothed distances. Chapters 3 and 4 were
  read for transport-map estimation and entropic sample complexity.
- [Peyré and Cuturi, *Computational Optimal Transport*](../lean-CKMA/References/PeyréCuturi2019ComputationalOptimalTransportApplicationsDataSciences-NowPublishers.FnTML11.pdf).
  The entropic problem, Gaussian costs, and sliced transport were consulted;
  the original empirical-rate theorem was checked separately. Chapter 5 was
  read for semidiscrete transport.
- [Villani, *Optimal Transport: Old and New*](../lean-CKMA/References/Villani2009OptimalTransportOldNew-SpringerGL338.pdf).
- [Santambrogio, *Optimal Transport for Applied Mathematicians*](../lean-CKMA/References/Santambrogio2015OptimalTransportAppliedMathematiciansCalculusVariationsPDEsModeling-Birkhäuser.PNDE87.pdf).
- [Ambrosio, Gigli, and Savaré, *Gradient Flows*](../lean-CKMA/References/AmbrosioGigliSavaré2008GradientFlowsMetricSpacesSpaceProbabilityMeasures2ndEd-Birkhäuser.LMETH.pdf).
- [Galichon, *Optimal Transport Methods in Economics*](../lean-CKMA/References/Galichon2016OptimalTransportMethodsEconomics-Princeton.pdf).
- [Berlinet and Thomas-Agnan, *Reproducing Kernel Hilbert Spaces in Probability and Statistics*](../lean-CKMA/ReferencesSuppl/BerlinetThomasAgnan2001rep2004ReproducingKernelHilbertSpacesProbabilityStatistics-KluwerSpringer.pdf).
  Chapter 4, Section 7 was read for the inner-product and weak topologies.
