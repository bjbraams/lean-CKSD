# Synopsis: Geometry of data: manifolds, topology, optimal transport, and kernels

Part of the [mathematical synopsis series](SYNOPSIS.md).
[Bibliographical scope and references](CKSD-bib.md#cks-108).

This synopsis follows Section 108. Subdivision 108A is spectral embeddings,
statistics on manifolds, and shape, together with simplicial and persistent
homology, stability of persistence, and topological inference. Subdivision
108B records the statistical uses of Wasserstein distance (empirical and
minimax rates, transport-map and entropic estimation, semidiscrete
transport, and the tangent-space geometry of barycenters) and of kernel
discrepancies (mean embeddings, characteristic kernels, comparison and
metrization of distances, kernel Stein discrepancies, conditional
embeddings, and random features). The Riemannian Cheeger inequality is
[CKMA SYNOPSIS14](../lean-CKMA/SYNOPSIS14.md), items 20 and 68, and the
Laplace–Beltrami operator is the subject of CKMA Section 53. Existence of
optimal plans, Kantorovich duality, cyclical monotonicity, completeness of
$W_p$, the Kantorovich–Rubinstein formula, the one-dimensional quantile
coupling, Brenier's theorem, displacement interpolation, the
Benamou–Brenier formula, and entropic transport are
[CKMA SYNOPSIS39](../lean-CKMA/SYNOPSIS39.md), items 39–49 and 90; the heat
flow as a Wasserstein gradient flow is CKMA SYNOPSIS39, item 62. The von
Mises–Fisher model is [SYNOPSIS105](SYNOPSIS105.md), item 27. Subsampling is [SYNOPSIS102](SYNOPSIS102.md), item 57. The representer
theorem and the Hilbertian central limit theorem are [SYNOPSIS103](SYNOPSIS103.md), items 8 and 29. Kernel
Rademacher complexity is [SYNOPSIS107](SYNOPSIS107.md), item 3.

Numbered definitions and results have stable identifiers. Additions take the
next free number and are placed beside related material; numbers need not
increase in reading order. Proofs are outside the scope of this synopsis.

<a id="synopsis-108a"></a>

## 108A. Manifold Learning, Geometric Statistics, Shape, and Persistent Homology

### Manifold learning, geometric statistics, and shape

Let $G$ be a finite connected undirected graph with at least two vertices,
no loops, and positive weights on its edges. The **volume** of a vertex set $S$ is the sum of the weighted
degrees in $S$. Chung's **Cheeger constant** is
$$
h(G)=\min_{\varnothing\ne S\subsetneq V(G)}\frac{|\partial S|}{\min(\mathop{\mathrm{vol}}S,\mathop{\mathrm{vol}}S^c)},
$$
where $|\partial S|$ is the total weight of the edges with one end in $S$.
The **normalized Laplacian** is
$\mathcal L=I-D^{-1/2}AD^{-1/2}$, with eigenvalues
$0=\lambda_0<\lambda_1\le\cdots\le\lambda_{n-1}\le2$. The **normalized cut**
of a bipartition $(S,S^c)$ is
$$
\mathop{\mathrm{Ncut}}(S,S^c)
=|\partial S|\Bigl(\frac1{\mathop{\mathrm{vol}}S}
+\frac1{\mathop{\mathrm{vol}}S^c}\Bigr).
$$

* **1. Cheeger inequality for the normalized Laplacian.** For a finite
  connected graph,
  $$\frac{\lambda_1}2\le h(G)\le\sqrt{2\lambda_1}.$$
  The sharper lower bound $\lambda_1\ge1-\sqrt{1-h(G)^2}$ holds as well.
  Both comparisons are Chung's Theorems 2.2 and 2.3. The continuous
  Dirichlet inequality is CKMA SYNOPSIS14, item 20.

* **2. Spectral relaxation of the normalized cut.** Every bipartition
  satisfies $\mathop{\mathrm{Ncut}}(S,S^c)\ge\lambda_1$. The minimum of the
  Rayleigh quotient $f^\top\mathcal L f/f^\top f$ over vectors orthogonal to
  $D^{1/2}\mathbf 1$ equals $\lambda_1$, and a bipartition is read from a
  corresponding eigenvector. This is the spectral clustering relaxation of
  Shi and Malik.

Let $P$ be an irreducible reversible Markov matrix on a finite state space,
with stationary probability $\pi$, eigenvalues
$1=\lambda_0>\lambda_1\ge\cdots\ge-1$, and eigenvectors $(\psi_j)$
orthonormal in $L^2(\pi)$. The **diffusion distance** at integer time
$t\ge1$ is
$$
D_t(x,y)^2
=\sum_{j\ge1}\lambda_j^{2t}\bigl(\psi_j(x)-\psi_j(y)\bigr)^2.
$$

* **3. Diffusion distance.** One has
  $$D_t(x,y)^2=\sum_z\frac{(P^t(x,z)-P^t(y,z))^2}{\pi(z)}.$$
  The truncated spectral sum is the squared Euclidean distance in
  $x\mapsto(\lambda_j^t\psi_j(x))_{1\le j\le m}$. The identity extends
  to reversible integral operators when a discrete spectral expansion
  and the required square-integrability hold. For manifold samples,
  a graph operator generally has a density-dependent limiting drift.
  Recovering the Laplace–Beltrami operator requires uniform sampling or
  an appropriate density correction, as well as bandwidth and smoothness
  assumptions; bounded positive sampling density alone is insufficient.

Let $M\subset\mathbb R^D$ be a compact Riemannian submanifold. A
neighborhood graph joins sample points at Euclidean distance at most
$\varepsilon$. **Isomap** replaces Euclidean distances by shortest-path
distances in that graph and applies classical multidimensional scaling.

* **4. Geodesic approximation.** Let $M$ be a compact connected smooth
  submanifold of positive reach, and let a noiseless sample be a
  $\delta_n$-net in its intrinsic metric. Join pairs at Euclidean
  distance at most $\varepsilon_n$, weighting edges by their Euclidean
  lengths. If $\varepsilon_n\to0$ and
  $\delta_n/\varepsilon_n\to0$, the graph shortest-path distances
  converge uniformly to intrinsic distances between sample points.
  On a manifold isometric to a convex Euclidean domain, the limiting
  geodesic distances are Euclidean distances in intrinsic coordinates.
  Multidimensional scaling then recovers those coordinates in the limit,
  subject to the spectral nondegeneracy needed for stability. Finite
  neighborhood-graph distances do not generally give exact recovery.

On a metric space $(M,d)$, the **Fréchet function** of a Borel probability
$\mu$ with finite second moment is
$F(x)=\int_M d(x,y)^2\,\mu(dy)$. A **Fréchet mean** is a minimizer of $F$.

* **5. Fréchet means.** In a complete Hadamard space every probability
  with finite second moment has a unique Fréchet mean. On a general
  Riemannian manifold neither uniqueness nor a normal limit is automatic;
  a convex support neighborhood must satisfy the relevant curvature and
  squared-distance convexity conditions; item 13 gives a sufficient
  ball condition. Suppose the population mean
  $m$ is unique, empirical means $\hat m_n$ are consistent, and
  $F$ has a differentiable score expansion in normal coordinates near
  $m$, with positive definite Hessian $H$, an integrable local Hessian
  envelope, and finite score covariance $\Sigma$. Then
  $$\sqrt n\,\log_m(\hat m_n)\Rightarrow
  N(0,H^{-1}\Sigma H^{-\top}).$$
  Here the score is the coordinate gradient of $d(\cdot,X)^2$ at $m$;
  cut-locus effects must be excluded or controlled in the expansion.

A **planar shape** of $k\ge3$ labeled landmarks, not all coincident, is an
equivalence class of $k$-ads in $\mathbb R^2$ under translation, rotation,
and scaling.

* **6. Kendall's planar shape space.** Centering a configuration of
  $k\ge3$ landmarks and normalizing its size gives a preshape on
  $S^{2k-3}\subset\mathbb C^{k-1}$. Quotienting by planar rotations
  identifies shape space with $\mathbb{CP}^{k-2}$. For unit preshapes
  $z,w$, the squared full Procrustes distance is
  $$d_F([z],[w])^2=1-|z^*w|^2.$$
  The full Procrustes mean is represented by a unit eigenvector for the
  largest eigenvalue of $\mathbb E[ZZ^*]$; it is unique as a shape if
  that eigenvalue is simple. A positive eigenvalue gap gives consistency
  and a tangent-space normal limit for the sample mean by spectral
  perturbation. This requires no choice of rotation for each observation.

* **7. Hausdorff estimation of a submanifold.** For noiseless sampling
  on a fixed compact $d$-dimensional manifold from a density bounded below,
  the sample is within $O_P((\log n/n)^{1/d})$ of the manifold in
  Hausdorff distance. In the perpendicular-noise model of Genovese and
  coauthors, the manifold lies in a fixed compact set, has reach at least
  $\kappa>0$, and each observation is a uniform manifold point displaced
  uniformly in its normal ball of fixed radius $0<\sigma<\kappa$.
  For that model their minimax expected Hausdorff risk satisfies
  $$c n^{-2/(d+2)}\le R_n\le
  C(\log n/n)^{2/(d+2)}.$$
  The bounds match up to a logarithmic factor; compactly supported noise
  without this model restriction does not imply the same rate.

Locally linear embedding, $t$-SNE, and UMAP construct a low-dimensional
layout from neighborhood weights.

### Spectral coordinates and extrinsic statistics

* **8. Classical multidimensional scaling.** For a symmetric matrix
  of proposed squared distances $D^{(2)}$, with zero diagonal, put
  $J=I-11^\top/n$ and $B=-JD^{(2)}J/2$. These are squared Euclidean
  distances if and only if $B$ is positive semidefinite. If
  $B=U\Lambda U^\top\ge0$, the rows of $U\Lambda^{1/2}$ are centered
  coordinates realizing them, unique up to a Euclidean isometry.
  Keeping the largest $k$ positive eigenvalues gives the best rank-at-most-$k$
  positive semidefinite approximation to $B$ in Frobenius norm.
  This optimizes the Gram-matrix criterion, rather than every definition
  of distance stress.

* **9. Locally linear embedding.** Suppose neighborhood reconstruction
  weights $W_{ij}$ vanish off chosen neighborhoods and satisfy
  $\sum_jW_{ij}=1$. For $1\le k<n$, among embeddings with $Z^\top Z=I_k$ and
  $Z^\top1=0$, minimizing
  $$\sum_i\left\|z_i-\sum_jW_{ij}z_j\right\|^2
  =\mathop{\mathrm{tr}}[Z^\top(I-W)^\top(I-W)Z]$$
  selects the $k$ lowest eigenvectors of $(I-W)^\top(I-W)$ on
  $1^\perp$. Reconstruction weights may need regularization if the
  local covariance is singular. This variational characterization is
  independent of a consistency claim for a sampled manifold.

Let $j:M\to\mathbb R^D$ be an embedding with closed image. An
**extrinsic mean** minimizes $\mathbb E\|j(X)-j(m)\|^2$ over $m\in M$.

* **10. Extrinsic projection mean.** If $j(X)\in L^2$, put
  $\mu=\mathbb E j(X)$. The extrinsic means are the nearest points
  in $j(M)$ to $\mu$. Suppose this projection $P$ is single-valued
  and continuously differentiable in a neighborhood of $\mu$. Then
  $$\sqrt n\left(P\left(n^{-1}\sum_i j(X_i)\right)-P(\mu)\right)
  \Rightarrow N(0,DP_\mu\Sigma DP_\mu^\top),$$
  where $\Sigma=\mathop{\mathrm{Cov}}(j(X))$ and the limit is supported
  on the tangent space at $P(\mu)$. Focal points can destroy uniqueness
  or the smooth projection expansion. Intrinsic means instead minimize
  squared geodesic distance, as in item 5.

### Graph Laplacians and eigenmaps

Let $W=(w_{ij})$ be a symmetric nonnegative $n\times n$ weight matrix with
zero diagonal, let $D$ be the diagonal matrix of degrees
$d_i=\sum_jw_{ij}$, and put $L=D-W$. When every degree is positive, the
normalized Laplacian is $\mathcal L=D^{-1/2}LD^{-1/2}$ and the
**random-walk Laplacian** is $L_{\mathrm{rw}}=D^{-1}L=I-D^{-1}W$. The
components of the graph are those of the graph of positive weights.

* **11. Laplacian quadratic form and connected components.** For every
  $f\in\mathbb R^n$,
  $$f^\top Lf=\frac12\sum_{i,j}w_{ij}(f_i-f_j)^2 .$$
  Hence $L$ is positive semidefinite, the multiplicity of its eigenvalue
  $0$ equals the number of connected components, and its kernel is
  spanned by the indicator vectors $\mathbf 1_C$ of the components. If
  all degrees are positive, the same multiplicity holds for $\mathcal L$,
  with kernel spanned by the vectors $D^{1/2}\mathbf 1_C$, and for
  $L_{\mathrm{rw}}$, with kernel spanned by the $\mathbf 1_C$. The
  eigenvalues of $\mathcal L$ lie in $[0,2]$, and $2$ is an eigenvalue
  exactly when some component with at least two vertices is bipartite.
  Thus for $k$ exactly disconnected clusters the bottom eigenspace is
  spanned by cluster indicators; spectral clustering perturbs this ideal
  case.

* **12. Laplacian eigenmaps.** Let the weighted graph be connected with
  generalized eigenvalues $0=\lambda_0<\lambda_1\le\cdots\le\lambda_{n-1}$
  of $Lf=\lambda Df$, and let $1\le k<n$. Among $Y\in\mathbb R^{n\times k}$
  with $Y^\top DY=I_k$ and $Y^\top D\mathbf 1=0$,
  $$\frac12\sum_{i,j}w_{ij}\|y_i-y_j\|^2=\mathop{\mathrm{tr}}(Y^\top LY)$$
  has minimum $\lambda_1+\cdots+\lambda_k$. It is attained by
  $D$-orthonormal generalized eigenvectors for
  $\lambda_1,\dots,\lambda_k$, equivalently by $Y=D^{-1/2}U$ with $U$
  holding orthonormal eigenvectors of $\mathcal L$ orthogonal to
  $D^{1/2}\mathbf 1$. The rows $y_i$ are the Laplacian eigenmap
  coordinates of Belkin and Niyogi. The minimizer is determined up to a
  right orthogonal factor, and its column space is unique when
  $\lambda_k<\lambda_{k+1}$. The trace minimization is the Ky Fan
  principle, CKMA SYNOPSIS13, item 6.

### Fréchet means and Procrustes analysis

* **13. Uniqueness of Fréchet means in small balls.** Let $M$ be a
  complete Riemannian manifold with sectional curvature at most
  $\Delta$ and injectivity radius $\mathop{\mathrm{inj}}(M)$. Put
  $r^*=\frac12\min\{\mathop{\mathrm{inj}}(M),\pi/\sqrt\Delta\}$, read as
  $\frac12\mathop{\mathrm{inj}}(M)$ when $\Delta\le0$. If the data, or
  the support of a probability, lie in an open geodesic ball of radius
  $r^*$, the Fréchet mean is unique. This is the Karcher–Kendall
  condition in Afsari's form. On the unit sphere $S^2$ it covers every
  open hemisphere, whereas two antipodal points have the whole equator
  as Fréchet mean set.

* **14. Strong consistency of Fréchet mean sets.** Let $(M,\rho)$ be a
  metric space whose closed bounded sets are compact, and let
  $F(p)=\int\rho(p,x)^\beta\,Q(dx)$ be finite for some $p$, where
  $\beta\ge1$. Then the mean set $C_Q$ of minimizers is nonempty and
  compact. For every $\varepsilon>0$, almost surely the sample mean sets
  $C_{Q_n}$ lie in the $\varepsilon$-neighborhood of $C_Q$ for all large
  $n$. If $C_Q=\{\mu\}$, every measurable choice of sample Fréchet mean
  is strongly consistent for $\mu$. On a compact space any continuous
  loss of the distance may be used. The sample sets need not fill out a
  nonsingleton $C_Q$.

* **15. Barycentric equation.** Let $M$ be a complete Riemannian manifold
  and $Q$ a probability with finite second moment. At a point $p$ whose
  cut locus has $Q$-measure zero, the Fréchet function is differentiable,
  with
  $$\nabla F(p)=-2\int\mathop{\mathrm{Log}}_p(x)\,Q(dx).$$
  Hence a Fréchet mean at such a point satisfies
  $\int\mathop{\mathrm{Log}}_p(x)\,Q(dx)=0$. Solutions of this equation
  are called exponential barycenters, or Karcher means. They are critical
  points of $F$ and need not minimize it. The gradient iteration
  $p_{j+1}=\mathop{\mathrm{Exp}}_{p_j}\bigl(\tau n^{-1}
  \sum_i\mathop{\mathrm{Log}}_{p_j}X_i\bigr)$ is the standard algorithm
  for sample means; its convergence needs concentration conditions such
  as those of item 13. Tangent principal component analysis
  diagonalizes the sample covariance of the vectors
  $\mathop{\mathrm{Log}}_{\hat p}X_i$. Principal geodesic analysis instead
  maximizes projected variance over geodesic submanifolds through
  $\hat p$.

A configuration of $k$ labeled landmarks in $\mathbb R^m$ is a $k\times m$
matrix. After centering, a nonzero configuration $X$ has **preshape**
$Z=X/\|X\|$ in the Frobenius norm. Its shape is the orbit
$\{Z\Gamma:\Gamma\in SO(m)\}$. For $k>m$, Kendall's shape space
$\Sigma^k_m$ has dimension $km-m-1-m(m-1)/2$. For $m=2$ this is
$\mathbb{CP}^{k-2}$, as in item 6.

* **16. Ordinary Procrustes analysis.** For centered nonzero
  configurations $X_1,X_2$ with preshapes $Z_1,Z_2$, write
  $Z_2^\top Z_1=V\Lambda U^\top$ with $U,V\in SO(m)$ and
  $\Lambda=\mathop{\mathrm{diag}}(\lambda_1,\dots,\lambda_m)$,
  $\lambda_1\ge\cdots\ge\lambda_{m-1}\ge|\lambda_m|$. Here $\lambda_m<0$
  exactly when $\det(Z_2^\top Z_1)<0$. The minimum of
  $\|X_2-\beta X_1\Gamma-\mathbf 1\gamma^\top\|^2$ over
  $\Gamma\in SO(m)$, $\beta>0$, and $\gamma\in\mathbb R^m$ is attained at
  $$\gamma=0,\qquad\Gamma=UV^\top,\qquad
  \beta=\frac{\mathop{\mathrm{tr}}(X_2^\top X_1\Gamma)}{\|X_1\|^2}.$$
  The minimum is $\|X_2\|^2\sin^2\rho$, where
  $\cos\rho=\sum_i\lambda_i$ and $\rho\in[0,\pi/2]$. The Riemannian shape
  distance is $\rho$. The full and partial Procrustes distances are
  $$d_F=\sin\rho=\Bigl(1-\Bigl(\sum_i\lambda_i\Bigr)^2\Bigr)^{1/2},
  \qquad d_P=2\sin(\rho/2).$$
  The optimal rotation is the same with or without scaling. Rotations
  are restricted to $SO(m)$, which accounts for the sign of $\lambda_m$.
  For $m=2$, $\sum_i\lambda_i=|z^*w|$ as in item 6.

* **17. Generalized Procrustes analysis and the full Procrustes mean.**
  For configurations $X_1,\dots,X_n$, full generalized Procrustes
  analysis minimizes
  $$\frac1n\sum_{i<j}\bigl\|(\beta_iX_i\Gamma_i+\mathbf 1\gamma_i^\top)
  -(\beta_jX_j\Gamma_j+\mathbf 1\gamma_j^\top)\bigr\|^2$$
  over similarity parameters, subject to unit centroid size of the
  average fitted configuration. The full Procrustes mean shape is
  $$[\hat\mu]=\mathop{\mathrm{arg\,min}}_{\|\mu\|=1}
  \sum_{i=1}^n d_F(X_i,\mu)^2 .$$
  It has the same shape as the arithmetic mean of the full Procrustes
  fits from the minimizing superimposition. For $m=2$ it is the leading
  eigenvector of item 6. The usual algorithm alternates ordinary
  Procrustes fits to the current mean with averaging and rescaling.

### Persistent homology and computational topology

A **persistence module** indexed by the real line, with coefficients in a
field, assigns a vector space $V_t$ to each $t\in\mathbb R$ and a linear
map $V_s\to V_t$ to each $s\le t$, compatibly with composition. The module
is **pointwise finite-dimensional** when every $V_t$ is finite-dimensional,
and **$q$-tame** when the rank of $V_s\to V_t$ is finite for every $s<t$.
An **interval module** has one-dimensional spaces on an interval, with
identity maps between indices inside it, and zero spaces and maps elsewhere.
A **barcode** records interval summands when such a decomposition exists.
A persistence diagram records off-diagonal birth and death multiplicities;
$q$-tameness allows its definition even without a pointwise finite-dimensional
interval decomposition. The diagonal is available for matching at zero cost.

* **18. Interval decomposition.** A pointwise finite-dimensional persistence
  module over a field decomposes as a direct sum of interval modules. The
  multiset of intervals is unique.

For tame functions $f,g$ on a triangulable space, let
$\mathop{\mathrm{Dgm}}(f)$ be the persistence diagram of a sublevel-set, or
other standard, filtration. The **bottleneck distance** $d_B$ is the
infimum, over bijections of the diagrams with the diagonal available, of
the largest $\ell^\infty$ displacement of a point.

* **19. Bottleneck stability.** For tame functions,
  $$d_B\bigl(\mathop{\mathrm{Dgm}}(f),\mathop{\mathrm{Dgm}}(g)\bigr)
  \le\|f-g\|_\infty.$$

An **$\varepsilon$-interleaving** consists of maps
$f_t:U_t\to V_{t+\varepsilon}$ and $g_t:V_t\to U_{t+\varepsilon}$
commuting with structure maps, such that
$g_{t+\varepsilon}f_t=U_{t,t+2\varepsilon}$ and
$f_{t+\varepsilon}g_t=V_{t,t+2\varepsilon}$.
The **interleaving distance** is the infimum of such $\varepsilon\ge0$;
it can vanish for distinct modules that differ only in endpoint decorations.

* **20. Isometry theorem.** For $q$-tame persistence modules the
  interleaving distance equals the bottleneck distance between their
  persistence diagrams.

Let $S$ be a finite set in a metric space. The **Čech complex** at radius
$r\ge0$ is the nerve of the closed balls of radius $r$ centered at the
points of $S$. In the parameterization of Edelsbrunner and Harer, the
**Vietoris–Rips complex** at parameter $r$ consists of the subsets of $S$
of diameter at most $2r$.

* **21. Čech, Rips, and the nerve.** In Euclidean space,
  $$\mathrm{Cech}(r)
  \subseteq\mathrm{Rips}(r)
  \subseteq\mathrm{Cech}(\sqrt2\,r).$$
  The two complexes have the same edges. If the Rips parameter is redefined
  to be the maximum edge length, then in any metric space
  $\mathrm{Rips}_r
  \subseteq\mathrm{Cech}_r
  \subseteq\mathrm{Rips}_{2r}$.
  The nerve of a finite collection of closed convex sets in Euclidean space
  has the homotopy type of the union of those sets.

The **reach** of a closed set is the largest radius at which the distance
function has a unique nearest point throughout the open tubular
neighborhood.

* **22. Homology from a sample.** Let $M\subset\mathbb R^D$ be a compact
  smooth $d$-dimensional submanifold without boundary and with reach
  $\tau>0$. Let $P$ be finite with Hausdorff distance
  $d_H(P,M)=\varepsilon<\sqrt{3/20}\,\tau$. Then for every
  $r\in(2\varepsilon,\sqrt{3/5}\,\tau)$ the offset
  $P^r=\{x:d(x,P)\le r\}$, a union of balls, deformation retracts onto
  $M$. Niyogi, Smale, and Weinberger prove this for $P\subset M$; Oudot
  states it for a point cloud near $M$. By the nerve theorem of item 21,
  the Čech complex of radius $r$ then has the homotopy type of $M$.
  For independent sampling with
  a density bounded below, an $\varepsilon$-net has probability at least
  $1-\delta$ once
  $$n\ge C\varepsilon^{-d}
  (\log(1/\varepsilon)+\log(1/\delta)),$$
  for small $\varepsilon$, with constants depending on the manifold and
  density bound. The logarithm of the covering number cannot generally
  be omitted when the net scale tends to zero.

A **persistence landscape** converts a barcode into a sequence of functions
by taking the successive largest values of the tent functions over its bars.
Its $L^p$ interpretation requires the corresponding integrability.

* **23. Central limit theorem for landscapes.** Realize a landscape
  as $\Lambda\in L^p(\mathbb N\times\mathbb R)$, using counting and
  Lebesgue measure. For independent copies, if $1\le p<\infty$ and
  $\mathbb E\|\Lambda\|_p<\infty$, their mean converges almost surely
  in $L^p$ to $\mathbb E\Lambda$. If $2\le p<\infty$ and
  $\mathbb E\|\Lambda\|_p^2<\infty$, the centered mean multiplied by
  $\sqrt n$ converges to a Gaussian random element in $L^p$.
  These spaces have type 2 for $p\ge2$. A finite second moment alone
  does not give a central limit theorem in an arbitrary separable
  Banach space.

For a probability $\mu$ and a mass $m\in(0,1]$, the **distance to the
measure** $d_{\mu,m}(x)$ is determined by the distances from $x$ to the
smallest masses of $\mu$: its square averages, up to mass $m$, the squared
radius needed to capture each intermediate mass.

* **24. Stability of the distance to a measure.** For probabilities with
  finite second moment,
  $$\|d_{\mu,m}-d_{\nu,m}\|_\infty
  \le m^{-1/2}W_2(\mu,\nu).$$
  The right-hand side uses the Wasserstein distance of
  CKMA SYNOPSIS39, item 42.

* **25. Confidence sets for diagrams.** Suppose a population diagram
  $D$ and empirical diagram $\hat D_n$ satisfy
  $d_B(\hat D_n,D)\le\|\hat f_n-f\|_\infty$ by stability. Any radius
  $r_n$ with $P(\|\hat f_n-f\|_\infty\le r_n)\ge1-\alpha$
  gives a bottleneck confidence ball of coverage at least $1-\alpha$.
  An estimated quantile can replace the radius only when its calibration
  is justified. In particular, subsampling requires a continuous limiting
  law for the normalized statistic and the scale and centering conditions
  of SYNOPSIS102, item 57. There is no unconditional subsampling theorem
  for every density or distance filtration.

The **Mapper** construction pulls a cover back along a filter function,
refines the pullback into connected components, and takes their nerve.
For finite data a chosen clustering rule provides the pullback components;
the resulting summary depends on that rule and the cover.

### Persistent summaries and perturbation certificates

For a finite filtered simplicial complex $K_s\subseteq K_t$, homology
with coefficients in a field gives the **persistent Betti number**
$\beta_q(s,t)=\mathop{\mathrm{rank}}[H_q(K_s)\to H_q(K_t)]$.

* **26. Rank invariant and barcode.** With half-open interval convention
  $[b,d)$, $\beta_q(s,t)$ is the number of degree-$q$ bars with
  $b\le s$ and $d>t$. Thus the two-parameter rank function determines
  the finite barcode with multiplicities. The ordinary Betti number
  $\beta_q(t,t)$ counts bars alive at $t$; it loses the information
  about which classes survive from one scale to another.

* **27. Hausdorff perturbations and offsets.** For nonempty compact
  subsets $A,B$ of a Euclidean space,
  $$\|d(\cdot,A)-d(\cdot,B)\|_\infty=d_H(A,B).$$
  If $d_H(A,B)\le\eta$, their offset filtrations satisfy
  $A^r\subseteq B^{r+\eta}$ and $B^r\subseteq A^{r+\eta}$.
  Consequently their $q$-tame persistence diagrams are within $\eta$
  in bottleneck distance. This turns geometric sampling control into
  a topological error bound without choosing one reconstruction scale.

* **28. Empirical distance to a measure.** Define
  $\delta_{\mu,u}(x)=\inf\{r\ge0:\mu(\overline B(x,r))\ge u\}$ and
  $$d_{\mu,m}(x)^2=\frac1m\int_0^m\delta_{\mu,u}(x)^2\,du.$$
  For an empirical measure with $n$ atoms and $m=k/n$, this is
  $k^{-1}\sum_{i=1}^k\|x-X_{(i)}(x)\|^2$, where the observations are
  ordered by distance to $x$. Averaging nearby mass replaces dependence
  on the single closest observation. The function $d_{\mu,m}$ is
  1-Lipschitz, and its perturbation under a change of measure is item 24.

* **29. Landscape stability.** For a finite barcode, replace each bar
  $[b,d)$ by the tent $t\mapsto\max(0,\min(t-b,d-t))$.
  The $k$th landscape function is the $k$th largest tent value at each
  $t$. For two finite diagrams,
  $$\|\Lambda_D-\Lambda_E\|_\infty\le d_B(D,E).$$
  Thus landscape evaluation and averaging are compatible with bottleneck
  perturbation control. A bound in $L^p$ additionally depends on the
  number, lengths, or total persistence of bars; a uniform bound alone
  does not give it on an unbounded domain.

* **30. Persistence beyond the error scale.** If $d_B(D,\hat D)\le\eta$,
  every finite bar in $\hat D$ of length greater than $2\eta$ must
  match an off-diagonal bar of $D$, with birth and death errors at most
  $\eta$. Such a bar cannot be matched to the diagonal. Applying this
  statement on the confidence event in item 25 gives a simultaneous
  certificate for all bars longer than the error threshold. Shorter
  bars may be genuine; the certificate makes no converse assertion.

### Simplicial homology and the persistence algorithm

A finite **simplicial complex** $K$ is a finite family of nonempty finite
sets closed under passage to nonempty subsets; a $p$-simplex has $p+1$
vertices. Over a field, the chain space $C_p(K)$ has the oriented
$p$-simplices as a basis, and the boundary map
$\partial_p[v_0,\dots,v_p]=\sum_i(-1)^i[v_0,\dots,\widehat{v_i},\dots,v_p]$
satisfies $\partial_{p-1}\partial_p=0$. The cycles
$Z_p=\ker\partial_p$ and boundaries $B_p=\mathop{\mathrm{im}}\partial_{p+1}$
give the homology $H_p=Z_p/B_p$ and the **Betti number**
$\beta_p=\dim H_p$. With $n_p$ the number of $p$-simplices, the
**Euler characteristic** is $\chi(K)=\sum_p(-1)^pn_p$.

* **31. Euler–Poincaré formula.** For homology over any field,
  $$\chi(K)=\sum_p(-1)^p\beta_p .$$
  Betti numbers are homotopy invariants of the underlying space, so
  $\chi$ does not depend on the triangulation. Individual Betti numbers
  may depend on the field, but $\chi$ does not. If a $p$-simplex is
  added to a complex containing its faces, either $\beta_p$ rises by one
  or $\beta_{p-1}$ falls by one. These **positive** and **negative**
  simplices are the births and deaths of persistence.

A **simplexwise filtration** orders the simplices as
$\sigma_1,\dots,\sigma_m$ so that every initial segment is a subcomplex.
Its boundary matrix $D$ over $\mathbb Z/2$ has $D_{ij}=1$ exactly when
$\sigma_i$ is a codimension-one face of $\sigma_j$. For a nonzero column
$j$, $\mathop{\mathrm{low}}(j)$ is the largest row index of a nonzero
entry. A matrix is **reduced** when distinct nonzero columns have
distinct lows. Adding columns to later columns gives $R=DV$ with $R$
reduced and $V$ invertible upper triangular. Let $D^i_j$ be the submatrix
of rows $i,\dots,m$ and columns $1,\dots,j$.

* **32. Persistence pairing by matrix reduction.** For every such
  reduction, $\mathop{\mathrm{low}}_R(j)=i$ exactly when
  $$\mathop{\mathrm{rank}}D^i_j-\mathop{\mathrm{rank}}D^{i+1}_j
  +\mathop{\mathrm{rank}}D^{i+1}_{j-1}-\mathop{\mathrm{rank}}D^i_{j-1}=1 .$$
  Hence the pairing does not depend on the reduction. If
  $\mathop{\mathrm{low}}_R(j)=i$, then $\sigma_i$ is a positive
  $p$-simplex, $\sigma_j$ is a negative $(p+1)$-simplex, and $[i,j)$ is
  a degree-$p$ bar. If column $j$ of $R$ is zero and $j$ is the low of no
  column, then $[j,\infty)$ is an essential bar of degree
  $\dim\sigma_j$. Function values replace indices for a filtration by a
  monotone function on simplices. The same holds over any field with
  signed boundary matrices. Standard reduction uses at most cubic time in
  $m$.

* **33. Zero-dimensional persistence and single linkage.** Let $(X,d)$
  be a finite metric space with $n$ points, filtered by Rips complexes
  with the maximum-edge parameter of item 21. The degree-zero barcode
  has $n$ bars born at $0$, one of them infinite. The $n-1$ finite death
  times are, as a multiset, the edge lengths of any minimum spanning tree
  of the complete graph weighted by $d$. They are the merge heights of
  single-linkage hierarchical clustering, as computed by Kruskal's
  algorithm. In the diameter-$2r$ parameter they are halved.

* **34. Sublevel persistence of a Morse function.** Let $f$ be a Morse
  function on a closed smooth manifold $M$ with distinct critical
  values, and use field coefficients for $M_{\le a}=f^{-1}(-\infty,a]$.
  The homotopy type of $M_{\le a}$ changes only at critical values.
  Passing an index-$q$ critical value attaches a $q$-cell, so either a
  degree-$q$ bar is born or a degree-$(q-1)$ bar dies there. Thus every
  finite endpoint of the diagram is a critical value. Each critical point
  is an endpoint of exactly one bar. With $c_q$ the number of index-$q$
  critical points,
  $$c_q=\#\{\text{degree-}q\text{ bars}\}
  +\#\{\text{finite degree-}(q-1)\text{ bars}\},$$
  and exactly $\beta_q(M)$ degree-$q$ bars are infinite. The Morse
  inequalities follow; see CKMA SYNOPSIS36, item 67.

### Stability and inference for geometric filtrations

For persistence diagrams $X,Y$ and $1\le q<\infty$, the **$q$-Wasserstein
distance** is
$$
W_q(X,Y)=\inf_\eta\Bigl(\sum_{x\in X}\|x-\eta(x)\|_\infty^q\Bigr)^{1/q},
$$
over bijections $\eta$ with the diagonal available, as for $d_B$. A
triangulable compact metric space has **polynomially growing
triangulations** if triangulations of mesh at most $r$ with at most
$cr^{-j}$ simplices exist for small $r$.

* **35. Wasserstein stability.** For tame Lipschitz functions $f,g$ on
  such a space, there are constants $C$ and $k\ge1$ with $k>j$ such that
  $$W_q\bigl(\mathop{\mathrm{Dgm}}_p(f),\mathop{\mathrm{Dgm}}_p(g)\bigr)
  \le C\|f-g\|_\infty^{1-k/q}\qquad(q\ge k).$$
  The constants depend on the space and the Lipschitz constants. For
  monotone functions on the simplices of a finite complex $K$, meaning
  $f(\tau)\le f(\sigma)$ whenever $\tau$ is a face of $\sigma$,
  $$W_q\bigl(\mathop{\mathrm{Dgm}}_p(f),\mathop{\mathrm{Dgm}}_p(g)\bigr)
  \le\Bigl(\sum_{\sigma\in K}|f(\sigma)-g(\sigma)|^q\Bigr)^{1/q}.$$
  No bound in $\|f-g\|_\infty$ alone can hold for $W_q$: many narrow
  wrinkles of height $\varepsilon$ produce arbitrarily many bars of
  persistence about $2\varepsilon$.

A **correspondence** between metric spaces $X,Y$ is a relation
$C\subseteq X\times Y$ projecting onto both factors. Its distortion is
$\sup|d_X(x,x')-d_Y(y,y')|$ over $(x,y),(x',y')\in C$. The
Gromov–Hausdorff distance of CKMA SYNOPSIS39 equals half the infimum of
distortions. A metric space is **totally bounded** if it has a finite
$\varepsilon$-net for every $\varepsilon>0$.

* **36. Gromov–Hausdorff stability of Rips persistence.** For totally
  bounded metric spaces $X,Y$, the homology of their Rips filtrations is
  $q$-tame. In the diameter-$2r$ parameter of item 21,
  $$d_B\bigl(\mathop{\mathrm{Dgm}}\mathrm{Rips}(X),
  \mathop{\mathrm{Dgm}}\mathrm{Rips}(Y)\bigr)\le d_{GH}(X,Y),$$
  in every degree; in the maximum-edge parameter the bound is
  $2d_{GH}(X,Y)$. For finite subsets of one metric space, the Rips and
  ambient Čech diagrams are within the Hausdorff distance $d_H$. The
  intrinsic Čech diagrams of finite metric spaces are within
  $2d_{GH}$. Thus Rips diagrams are isometry invariants that give lower
  bounds for $d_{GH}$.

Let $K\subset\mathbb R^D$ be compact with distance function $d_K$. A point
$x\notin K$ is **critical** for $d_K$ if it lies in the convex hull of its
nearest points in $K$. The **weak feature size** $\mathrm{wfs}(K)$ is the
infimum of the positive critical values of $d_K$. It is at least the
reach, and it is positive for all compact polyhedra. If $[i,j]$ contains
no critical value, with $0<i<j$, the offset $K^j$ deformation retracts
onto $K^i$.

* **37. Homology inference with positive weak feature size.** Let
  $d_H(K,P)=\varepsilon<\mathrm{wfs}(K)/4$ for a finite $P$. If
  $\varepsilon<i$ and $i+2\varepsilon\le j<\mathrm{wfs}(K)-\varepsilon$,
  the image of $H_*(P^i)\to H_*(P^j)$ is isomorphic to $H_*(K^r)$ for
  every $r\in(0,\mathrm{wfs}(K))$. By the nerve theorem the same holds for
  the Čech complexes of radii $i$ and $j$. If
  $\varepsilon<\mathrm{wfs}(K)/9$ and
  $2\varepsilon\le\alpha\le(\mathrm{wfs}(K)-\varepsilon)/4$, the image of
  $H_*(\mathrm{Rips}(\alpha/2))\to H_*(\mathrm{Rips}(2\alpha))$ is
  isomorphic to $H_*(K^r)$, in the parameter of item 21. Single offsets
  of $P$ need not have the homology of $K^r$, and $K$ itself need not
  have the homotopy type of its small offsets.

* **38. Rips pairs on a manifold.** Let $M\subset\mathbb R^D$ be a compact
  smooth submanifold with reach $\tau>0$, and let $d_H(P,M)\le\varepsilon$
  for a finite $P$. If
  $3\varepsilon\le\alpha\le\frac3{16}\sqrt{3/5}\,\tau$, then in the
  parameter of item 21
  $$\mathop{\mathrm{rank}}\bigl(H_*(\mathrm{Rips}(\alpha))
  \to H_*(\mathrm{Rips}(2\alpha))\bigr)=\dim H_*(M).$$
  The proof sandwiches the Rips complexes between Čech complexes whose
  homology is that of $M$, by item 21 and the offset theorem of item 22.

A probability $\mu$ with compact support $X_\mu$ in a metric space is
**$(a,b)$-standard** if $\mu(B(x,r))\ge\min(1,ar^b)$ for all $x\in X_\mu$
and $r>0$.

* **39. Rates for persistence diagram estimation.** Let $\hat X_n$ be an
  independent sample of size $n$ from an $(a,b)$-standard $\mu$. A
  covering argument gives
  $\mathbb E\,d_H(\hat X_n,X_\mu)\le C(\log n/n)^{1/b}$ with $C$
  depending on $a$ and $b$. Since $d_{GH}\le d_H$, item 36 gives
  $$\mathbb E\,d_B\bigl(\mathop{\mathrm{Dgm}}\mathrm{Rips}(\hat X_n),
  \mathop{\mathrm{Dgm}}\mathrm{Rips}(X_\mu)\bigr)
  \le C\Bigl(\frac{\log n}n\Bigr)^{1/b}.$$
  The target
  is the diagram of the support; outliers or ambient noise call instead
  for the distance to a measure of items 24 and 28.

<a id="synopsis-108b"></a>

## 108B. Optimal Transport and Kernel Discrepancies

### Optimal transport and Wasserstein statistics

Throughout, for $p\ge1$, $W_p$ is the $p$-Wasserstein distance on the space
$\mathcal P_p$ of Borel probabilities with finite $p$th moment, as in
CKMA SYNOPSIS39.

Let $\mu_n$ be the empirical measure of $n$ independent copies of a
probability $\mu$ on $\mathbb R^d$.

* **40. Empirical Wasserstein bounds.** For a probability supported in
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

* **41. Uniqueness of the barycenter.** If at least one $\mu_i$ is
  absolutely continuous, the barycenter exists and is unique.

* **42. Consistency of Brenier maps.** Let $\mu\in\mathcal P_2(\mathbb R^d)$
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

* **43. Gromov–Wasserstein distance.** With the normalization above,
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

* **44. Debiased Sinkhorn divergence.** On a compact Euclidean domain
  with quadratic cost, for every $\varepsilon>0$,
  $S_\varepsilon(\mu,\nu)\ge0$, with equality exactly when $\mu=\nu$.
  Moreover $S_\varepsilon(\mu_n,\mu)\to0$ if and only if
  $\mu_n\Rightarrow\mu$. A sufficient general setting is a compact
  metric space with Lipschitz symmetric cost whose Gibbs kernel
  $e^{-c/\varepsilon}$ is positive and universal. These hypotheses
  distinguish the theorem from a claim for arbitrary costs or tails.

### Explicit geometries and empirical inference

* **45. Barycenters on the line.** For $\mu_i\in\mathcal P_2(\mathbb R)$,
  the unique weighted barycenter has quantile function
  $$F_{\bar\mu}^{-1}(u)=\sum_i\lambda_iF_{\mu_i}^{-1}(u).$$
  More generally, for a random measure $\Lambda$ with
  $\mathbb E\int x^2\Lambda(dx)<\infty$, the population barycenter
  has quantile $\mathbb E F_\Lambda^{-1}$ almost everywhere. The quantile
  embedding
  makes this a Hilbert-space mean. Such an averaging formula does not
  hold for arbitrary multivariate transport maps.

* **46. Gaussian transport and barycenters.** For covariance matrices
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

* **47. One-dimensional empirical transport limit.** Suppose $\mu$ is
  supported on $[a,b]$ and has a continuous density bounded above and
  below by positive constants there. Then
  $$nW_2^2(\mu_n,\mu)\Rightarrow
  \int_0^1\frac{B^0(u)^2}{f(F^{-1}(u))^2}\,du,$$
  by the quantile-process delta method. Thus $W_2(\mu_n,\mu)=O_P(n^{-1/2})$
  under these assumptions, faster than the distribution-free bound
  inferred from item 40. Atoms, gaps, and unbounded tails can change
  the rate or invalidate this integral limit.

* **48. Sliced Wasserstein distance.** Let $\sigma$ be uniform probability
  on $S^{d-1}$ and $P_\theta(x)=\theta^\top x$. Then
  $$\mathop{\mathrm{SW}}_p(\mu,\nu)
  =\left(\int W_p^p((P_\theta)_\#\mu,(P_\theta)_\#\nu)
  \,\sigma(d\theta)\right)^{1/p}$$
  defines a metric on $\mathcal P_p(\mathbb R^d)$ and is at most
  $W_p(\mu,\nu)$. Vanishing projected distances imply equality of
  the laws by continuity of characteristic functions and the
  Cramér–Wold characterization. A finite collection of directions alone
  does not determine every multivariate law.

* **49. Consistency of empirical barycenters.** Suppose independent
  identically distributed random measures $\Lambda_i$ are supported in a common compact set
  $K\subset\mathbb R^d$, and the population Fréchet functional
  $\mathbb E W_2^2(\mu,\Lambda_1)$ has a unique minimizer $\bar\mu$.
  Any sequence minimizing $n^{-1}\sum_iW_2^2(\mu,\Lambda_i)$ converges
  almost surely to $\bar\mu$ in $W_2$. Minimizers can be confined to
  the compact convex hull of $K$; uniform convergence there gives the
  argmin conclusion. Noncompact versions require suitable moment and
  compactness control.

### Minimax limits, smoothness, and smoothing

* **50. Minimax lower bounds for transport estimation.** Let $d\ge3$
  and let $\lambda$ be the uniform law on $[0,1]^d$. Every probability
  $\tilde\mu$ supported on at most $n$ points satisfies
  $$W_1(\tilde\mu,\lambda)\ge\frac{n^{-1/d}}{108\,d};$$
  in particular this holds for the empirical measure, almost surely.
  More strongly, for $n\ge8$ and every estimator $\tilde\mu_n$, that is,
  every measurable function of $n$ independent observations,
  $$\sup_\mu\mathbb E_\mu W_1(\tilde\mu_n,\mu)\ge\tfrac1{16}(2n)^{-1/d},$$
  the supremum over probabilities supported in $[0,1]^d$. Thus the rate
  $n^{-1/d}$ of item 40 for $p=1$ cannot be improved uniformly by any
  estimator. The plug-in estimator $W_1(\mu_m,\nu_n)$ of $W_1(\mu,\nu)$ from two
  independent samples has error of order $(m\wedge n)^{-1/d}$, which is
  sharp in general, and a goodness-of-fit or two-sample test based on the
  empirical $W_1$ needs thresholds, hence separations, of order at least
  $n^{-1/d}$. The
  adversarial laws in the proof are atomic; item 51 shows how smoothness
  changes the picture.

On the torus $\mathbb T^d=\mathbb R^d/(2\pi\mathbb Z)^d$ with its quotient
metric, the Sobolev space $H^s$, $s$ a positive integer, consists of
densities whose derivatives of order at most $s$ are square integrable.
For $\sigma>0$, the **smoothed Wasserstein distance** is
$W_p^{(\sigma)}(\mu,\nu)=W_p(\mu*N(0,\sigma^2I),\nu*N(0,\sigma^2I))$;
it is a metric on $\mathcal P_p(\mathbb R^d)$.

* **51. Smooth laws and smoothed distances.** Let $d\ge3$. If $\mu$ has a
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
  in $d$. That growth reflects the difficulty of item 50 and is not
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

* **52. Semidual stability.** If $\nu=(\nabla\varphi)_\#\mu$ and $\phi$ is
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

* **53. Rates for transport-map estimation.** Let $\mu$ and $\nu$ be
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

* **54. Entropic duality and the entropic map.** One has
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

* **55. Dimension-free sample complexity of entropic transport.** Let
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
  to unregularized transport as $\varepsilon\downarrow0$, by item 50.

### Semidiscrete transport

Let $\mu\in\mathcal P_2(\mathbb R^d)$ be absolutely continuous, and let
$\nu=\sum_{j=1}^m b_j\delta_{y_j}$ with distinct $y_j$ and $b_j>0$. For quadratic
cost $c$ and $g\in\mathbb R^m$, put
$g^c(x)=\min_j\bigl(c(x,y_j)-g_j\bigr)$. The **Laguerre cells**
$L_j(g)=\{x:c(x,y_j)-g_j\le c(x,y_k)-g_k\ \text{for all }k\}$ are
convex polyhedra covering $\mathbb R^d$ (a power diagram), with
overlaps of Lebesgue measure zero.

* **56. Semidiscrete dual.** The function
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

* **57. Tangent-space linearization.** For $\gamma$ absolutely continuous,
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
  item 45. A family of centered nondegenerate Gaussian laws containing
  the standard Gaussian is compatible exactly when the covariances commute,
  consistent with item 46. In
  general the inequality is strict, reflecting the nonnegative curvature
  of $W_2$ in dimension at least two.

* **58. First-order conditions for barycenters.** Let
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

* **59. Procrustes iteration for barycenters.** Start from an absolutely
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
  the barycenter of item 46. It is the Wasserstein analogue of generalized
  Procrustes analysis: register to the template through log maps,
  average linearly, retract by the exponential map.

### Kernel mean embeddings and integral probability metrics

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

* **60. Maximum mean discrepancy.** The discrepancy equals the integral
  probability metric over the unit ball of $\mathcal H$, and
  $$
  \mathop{\mathrm{MMD}}(\mu,\nu)^2
  =\mathbb E k(X,X')+\mathbb E k(Y,Y')-2\mathbb E k(X,Y)
  $$
  for independent copies $X,X'\sim\mu$ and $Y,Y'\sim\nu$. The Gaussian and
  Laplace kernels on $\mathbb R^d$ are characteristic. A continuous
  translation-invariant positive definite kernel on $\mathbb R^d$ is
  characteristic when the support of its spectral measure is all of
  $\mathbb R^d$; item 68 gives the converse and further criteria.

For independent samples of equal size $n\ge2$, use the unbiased estimator
$$\mathop{\mathrm{MMD}}_{u,n}^2
=\frac{\sum_{i\ne j}k(X_i,X_j)+\sum_{i\ne j}k(Y_i,Y_j)}{n(n-1)}
-\frac2{n^2}\sum_{i,j}k(X_i,Y_j).$$
The biased estimator $\mathop{\mathrm{MMD}}_{b,n}^2$ is
$\|\Phi(\mu_n)-\Phi(\nu_n)\|_{\mathcal H}^2$. Let
$(\lambda_j)_{j\ge1}$ be the eigenvalues of the integral operator of the
centered kernel $\tilde k(x,y)=k(x,y)-\mathbb Ek(x,X')-\mathbb Ek(X,y)+\mathbb Ek(X,X')$
on $L^2(\mu)$.

* **61. Limits of the empirical discrepancy.** For the bounded kernel
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

* **62. Energy distance and independence.** For laws on $\mathbb R^d$
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

* **63. Hilbert–Schmidt independence criterion.** For bounded continuous
  kernels, assume the product kernel is characteristic on the product
  space, as for Gaussian kernels on Euclidean coordinates. Then HSIC
  vanishes if and only if $X$ and $Y$ are independent. An unbiased
  estimator based on paired observations is a $U$-statistic of order
  four, because both marginal embeddings must also be estimated.
  Under independence its first projection vanishes and its scaled limit
  is a centered weighted chi-squared series. Under alternatives its
  $\sqrt n$ limit is normal, possibly degenerate. The biased Gram-matrix
  estimator in item 67 has an uncentered null limit.

### Kernel estimation, witnesses, and test calibration

* **64. Empirical kernel means.** If $k(x,x)\le\kappa^2$, then
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

* **65. Witness function.** If $\Delta=\Phi(\mu)-\Phi(\nu)\ne0$, the
  function attaining the MMD supremum is
  $$f^*(x)=\frac{\mathbb E_\mu k(x,X)-\mathbb E_\nu k(x,Y)}
  {\|\Delta\|_{\mathcal H}}.$$
  It has RKHS norm one, and its mean difference is the MMD.
  The unnormalized numerator describes where the distributions differ
  at the resolution selected by the kernel.

* **66. Permutation calibration.** Under equality of two independent
  sample laws, labels are uniform over all allocations of the pooled
  observations to the two fixed sample sizes. Recomputing any fixed
  statistic under those allocations gives a test of conditional level
  at most $\alpha$, or exactly $\alpha$ with boundary randomization.
  This applies to MMD, energy, and empirical transport statistics
  without estimating their asymptotic null laws. For independence
  testing, permuting one coordinate of independent observed pairs
  gives the analogous calibration under the product-law null.

* **67. Gram-matrix independence statistic.** Let $K,L$ be the Gram
  matrices of the two coordinates of $n$ independent pairs and put
  $H=I-11^\top/n$. The biased HSIC estimator is
  $$\widehat{\mathop{\mathrm{HSIC}}}_b=n^{-2}\mathop{\mathrm{tr}}(KHLH).$$
  Under independence its $n$-scaled limit is
  $\sum_{r,s}\lambda_r\eta_sZ_{rs}^2$, where $\lambda_r,\eta_s$
  are eigenvalues of the two centered marginal kernel operators.
  The unbiased order-four estimator has the corresponding centered
  series $\sum_{r,s}\lambda_r\eta_s(Z_{rs}^2-1)$.
  There is one sample of pairs here, unlike the two independent
  samples and factor two in item 61.

### Characteristic kernels and comparison of metrics

Reproducing-kernel Hilbert spaces and the Moore–Aronszajn theorem are
[CKMA SYNOPSIS21](../lean-CKMA/SYNOPSIS21.md), item 53; Mercer's expansion
is [CKMA SYNOPSIS25](../lean-CKMA/SYNOPSIS25.md), item 8; Bochner's theorem
is recalled in [SYNOPSIS106](SYNOPSIS106.md), item 24. A bounded measurable
kernel $k$ on a topological space is **integrally strictly positive definite**
if $\iint k\,d\eta\,d\eta>0$ for every finite nonzero signed Borel measure
$\eta$. A continuous kernel on a compact metric space is **universal** if its
reproducing-kernel Hilbert space is dense in the continuous functions for
the supremum norm.

* **68. Criteria for characteristic kernels.** For a bounded measurable
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
  the converse of the sufficient condition in item 60. In particular, every
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

* **69. Comparison of distances between distributions.** Let $k$ be
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

* **70. Metrization of weak convergence.** For a bounded continuous
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
  MMD is not even a metric, as in item 68(d).

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

* **71. Kernel Stein discrepancy.** Let $k$ be bounded with bounded
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
  theory follows SYNOPSIS102, items 29 and 30.

A target $P$ is **distantly dissipative** if
$\liminf_{r\to\infty}\kappa(r)>0$, where
$\kappa(r)=\inf\{-2\langle b(x)-b(y),x-y\rangle/\|x-y\|^2:\|x-y\|=r\}$.
Examples are finite Gaussian mixtures with a common covariance and laws
that are strongly log-concave outside a compact set.

* **72. Convergence control by kernel Stein discrepancies.** Let $P$ be
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

* **73. Conditional mean embeddings.** If $g\in\mathcal G$ and
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
  SYNOPSIS107, item 13. The weights need be neither
  positive nor normalized. Its rates are slower than the $n^{-1/2}$ rate
  of marginal embeddings in item 64.

* **74. Random Fourier features.** Let $k(x,y)=\psi(x-y)$ be continuous
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
  as stated by Rahimi and Recht.
  Hence $D$ of order $d\varepsilon^{-2}\log(\sigma\mathop{\mathrm{diam}}M/\varepsilon)$ features
  suffice for uniform error $\varepsilon$. For laws on $M$, the squared MMD
  of the feature map $z$ is
  $\|\int z\,d\mu-\int z\,d\nu\|^2$. It is computable in linear time and
  differs from $\mathop{\mathrm{MMD}}_k^2$ by at most $4\varepsilon$ on that event. For
  the Gaussian kernel $e^{-\gamma\|x-y\|^2}$, $\sigma^2=2d\gamma$.

## Reference guide

### Correspondence with the subdivisions

- **[108A](#synopsis-108a)**: Chung carries the normalized Laplacian and the
  Cheeger inequality. von Luxburg carries spectral clustering. Coifman and
  Lafon carry diffusion distances, and Belkin and Niyogi carry the
  Laplace–Beltrami limit of the graph Laplacian. Tenenbaum, de Silva, and
  Langford carry Isomap. Bhattacharya and Bhattacharya carry Fréchet means on
  manifolds. Dryden and Mardia carry Kendall shape space. Genovese,
  Perone-Pacifico, Verdinelli, and Wasserman carry the noisy Hausdorff rate.
  Pennec, Sommer, and Fletcher carry Fréchet-mean uniqueness, exponential
  barycenters, and principal geodesic analysis. Dryden and Mardia also carry
  ordinary and generalized Procrustes analysis. Edelsbrunner and Harer carry
  Čech and Rips complexes, the nerve theorem, and bottleneck stability.
  Chazal, de Silva, Glisse, and Oudot carry the isometry theorem. Oudot
  carries the algebraic theory of barcodes. Niyogi, Smale, and Weinberger
  carry homology recovery. Bubenik carries persistence landscapes. Chazal,
  Cohen-Steiner, and Mérigot carry the distance to a measure. Fasy, Lecci,
  Rinaldo, Wasserman, Balakrishnan, and Singh carry confidence sets. Dey and
  Wang carry the reduction algorithm, Wasserstein and Gromov–Hausdorff
  stability, and homology inference from Rips pairs. Chazal and Lieutier,
  through Oudot, carry the weak feature size and the sampling rates for
  diagram estimation.
- **[108B](#synopsis-108b)**: Villani, Santambrogio, and Ambrosio, Gigli, and
  Savaré carry the analytic theory already numbered in CKMA SYNOPSIS39. Peyré
  and Cuturi carry computational optimal transport and entropic
  regularization. Fournier and Guillin carry empirical Wasserstein rates.
  Agueh and Carlier carry barycenters. Mémoli carries the Gromov–Wasserstein
  distance. Feydy, Séjourné, Vialard, and Peyré carry the debiased Sinkhorn
  divergence. Gretton, Borgwardt, Rasch, Schölkopf, and Smola carry the
  maximum mean discrepancy and its limits. Sejdinovic, Sriperumbudur, Gretton,
  and Fukumizu carry the equivalence of energy distance and a kernel
  discrepancy. Székely, Rizzo, and Bakirov carry distance covariance. Gretton,
  Bousquet, Smola, and Schölkopf carry the Hilbert–Schmidt independence
  criterion.

### Source comparisons and local copies

#### Geometric and topological data analysis

The local Edelsbrunner–Harer manuscript, Parts B and C, supplies the
nerve construction, persistent Betti numbers, diagrams, and stability.
Chazal–de Silva–Glisse–Oudot, especially the isometry theorem in Chapter 5,
distinguishes $q$-tameness from a pointwise finite-dimensional interval
decomposition. The new rank and offset statements make the passage from
geometric perturbations to persistence explicit. The Čech–Rips constants
retain the radius convention already used here.

Bhattacharya–Bhattacharya, Chapter 4 and Proposition 4.3, was read for the
extrinsic projection and normal limit; the planar-shape chapters give the
matrix representation of a Procrustes mean. Intrinsic inference instead
needs the score and cut-locus assumptions in item 5. Mere geodesic convexity
of a support ball is not used as a sufficient uniqueness theorem.

The original [Genovese and coauthors paper](https://www.jmlr.org/papers/v13/genovese12a.html),
Theorems 1–2 and Section 2, was read online: item 7 now includes its
perpendicular-noise model and logarithmic gap. For landscapes,
[Bubenik's paper](https://www.jmlr.org/papers/v16/bubenik15a.html),
Theorems 8–10, supplies the type-2 requirement. The finite-net size in
item 22 includes the covering logarithm; confidence calibration in item 25
requires more than persistence stability.

The local Chung text remains the source for normalized spectral quantities.
The added multidimensional-scaling and locally-linear-embedding formulas
record their finite-dimensional variational problems. They do not assume
that graph shortest-path distances are already exact intrinsic coordinates,
or that uncorrected nonuniform sampling gives a Laplace–Beltrami limit.

Lee–Verleysen and Boissonnat–Chazal–Yvinec were not located in the two local
reference directories. The Genovese and Bubenik papers above were consulted
online, rather than described as local copies. Niyogi–Smale–Weinberger was
not read as a local full text; the reconstruction framework is also developed
in the local topology monographs. The Mapper cover is refined into its
connected pullback components before taking its nerve.

For the third expansion (items 11–17 and 31–39 and the revision of item 22), the
following local passages were read. Chung, Lemma 1.7, gives the kernel and
spectral range of the normalized Laplacian in item 11. Wang, *Geometric
Structure of High-Dimensional Data*, Chapter 12.1, gives the Laplacian
eigenmap optimization of item 12, and Section 8.5 the Isomap justification
behind item 4. Pennec–Sommer–Fletcher, Chapter 2 (Theorems 2.1–2.2,
Example 2.4, Sections 2.2.2 and 2.3.2) and Chapter 5 (exponential
barycenters), give items 13 and 15. Bhattacharya–Bhattacharya,
Theorems 3.2–3.3 and Corollary 3.4, give item 14. Dryden–Mardia,
Results 4.1–4.2, Definitions 4.12–4.14, Result 5.1, Definitions 5.3–5.5,
and Result 5.2, give items 16 and 17; the dimension formula is from their
Section 4.1. Edelsbrunner–Harer, Chapter IV (Euler–Poincaré), Chapter VI
(handles and the PL Morse inequalities), Chapter VII (Pairing Lemma), and
Chapter VIII.2 (Wasserstein stability), give items 31, 32, 34, and 35.
Dey–Wang, Theorems 1.3–1.4, 3.2–3.6 and Fact 3.6, Section 3.5 on minimum
spanning trees, Theorem 6.3, Proposition 6.10, Theorem 6.11,
Proposition 6.12, and Theorem 6.13, give items 32–38; their Rips
parameter is the diameter-$2r$ one of item 21. Oudot, Chapter 2.2.3,
Chapter 4.1 (Theorem 4.1, Lemma 4.3, Theorem 4.4), and Chapter 7
(Theorems 7.2 and 7.5, maximum-edge parameter), give items 22, 33, 36, and 37. Carlsson–Vejdemo-Johansson, Section 4.1, gives single linkage.
Item 22 was sharpened to the Niyogi–Smale–Weinberger constants as stated
in Oudot, Theorem 4.1, and item 5 now points to item 13.

Some statements were not checked against a local full text. Two
earlier entries, on density-corrected Laplace–Beltrami limits (after
Coifman–Lafon and Hein–Audibert–von Luxburg) and on the consistency of
spectral clustering (after von Luxburg–Belkin–Bousquet), were removed for
that reason; see [SYNOPSIS-CONCORDANCE.md](SYNOPSIS-CONCORDANCE.md). The Skraba–Turner cellular bound in item 35
is checked only against its statement in Dey–Wang, Theorem 3.4. The
bound in item 39 follows from a covering argument and item 36; the
matching minimax lower bound of Chazal, Glisse, Labruère, and Michel is
cited in Oudot, Chapter 8, but was not checked and is not stated. Afsari's form
of the uniqueness radius in item 13 is as quoted by Pennec–Sommer–Fletcher.
Federer's reach theory is in his 1959 curvature-measures paper rather than
in the local *Geometric Measure Theory*, so reach is taken from Oudot and
Dey–Wang.

#### Optimal transport and kernel discrepancies

Panaretos–Zemel is present in `ReferencesSuppl`. Section 1.6.3, the
one-dimensional barycenter theorem in Section 3.2.2, and the Gaussian
covariance equation in Section 5.4.1 were read for items 45 and 46.
Chewi–Niles-Weed–Rigollet is also present there; Chapter 2 develops the
distribution-free empirical bounds and why they need not be sharp for
each law. The quantile-process limit in item 47 specializes SYNOPSIS102, items 6 and 28, under compact-support density bounds.

For item 40, [Fournier–Guillin, Theorem 1](https://arxiv.org/abs/1312.2128),
was read online. It gives upper bounds with moment remainders, not an
exact rate for every measure. The bounded-domain positivity statement
in item 44 follows [Feydy and coauthors, Theorem 1](https://proceedings.mlr.press/v89/feydy19a.html).
The entropic cost convention is fixed by CKMA SYNOPSIS39, item 90;
debiasing subtracts the two self-costs.

[Gretton and coauthors, Theorem 12](https://www.jmlr.org/papers/v13/gretton12a.html),
was checked for the equal-sample normalization in item 61. Centered
one-sample kernel eigenvalues give the factor two there. The generic
projection argument is SYNOPSIS102, items 29 and 30. Empirical kernel means,
witnesses, and permutation calibration are the elementary Hilbert-space
and exchangeability consequences recorded in items 64–66.

Energy distance uses a distance-induced kernel with its explicit factor
in item 62. Distance covariance uses products of centered coordinate
distances; the Euclidean energy distance of concatenated pairs is a
different discrepancy. HSIC is the squared norm convention, its unbiased
estimator has order four, and a nonzero discrepancy does not by itself
force a positive first-projection variance. The energy–kernel comparison
is treated by Sejdinovic and coauthors, listed in the bibliography; that
paper was not consulted as a local full text in this expansion.

For the third expansion (items 50–59 and 68–74) the following passages were read.
In the local Chewi–Niles-Weed–Rigollet: Section 2.5 (plug-in estimation and
testing), Theorems 2.14–2.15 (lower bounds), Proposition 2.17 and
Theorem 2.18 (smooth torus estimator and its projection), Definition 2.23
and Theorem 2.24 (smoothed Wasserstein), Section 2.8.2 (MMD and Gaussian
characteristic kernels), all for items 50 and 51. Theorem 3.1, Assumption 3.3,
condition (3.5), Theorems 3.7 and 3.15, and the discussion in Section 3.7
were read for items 52 and 53. Propositions 4.3 and 4.5, the Sinkhorn updates
(4.11)–(4.12), Theorems 4.9–4.11, Exercise 3, and Section 4.5 were read for
items 54 and 55. The Hütter–Rigollet minimax statement in item 53 was checked
against [Hütter and Rigollet, Theorems 2, 6, and 8](https://arxiv.org/abs/1905.05828),
read online. The gradient of the entropic potential in item 54 was
recomputed from the Gibbs form. The cost $\|x-y\|^2$ carries no factor
one half. Peyré–Cuturi, Section 5.2, eqs. (5.6)–(5.8), gives the
semidiscrete dual, the Laguerre cells, and the gradient formula of item 56.
Panaretos–Zemel, Section 2.3.1 and Definition 2.3.1 with the Gaussian
compatibility example, and Theorem 3.1.9 were read for item 57.
Proposition 3.1.10 and Theorems 3.1.14–3.1.15 were read for item 58.
Lemmas 5.1.1–5.1.2, Algorithm 1, Theorems 5.3.1 and 5.3.3, and
Corollary 5.3.2 were read for item 59. The text states item 58 with equal
weights $1/N$, as here.

For 108B, [Sriperumbudur, Gretton, Fukumizu, Schölkopf, and Lanckriet,
“Hilbert Space Embeddings and Metrics on Probability Measures” (JMLR 11,
2010)](https://www.jmlr.org/papers/v11/sriperumbudur10a.html) was read online.
Lemma 8, Theorem 7, Theorem 9, Corollary 10, and the polynomial-kernel
example of Section 3 were used for item 68. Proposition 20, Theorem 21,
and the Gibbs–Su relations of Section 5 were used for item 69. That paper's total variation is twice
$d_{\mathrm{TV}}$, and the factor in item 69 is adjusted accordingly.
Theorems 23–24 were used for item 70. The local Berlinet–Thomas-Agnan,
Chapter 4, Section 7, Theorems 100–101 (after Guilbart), give the
compact-space metrization in item 70(a). The tightness argument in item 70
is elementary. [Gorham and Mackey, “Measuring Sample Quality with Kernels”
(ICML 2017)](https://arxiv.org/abs/1703.01717) was read online for
items 71 and 72: Propositions 1, 2, and 9, Definition 4, and Theorems 5–8.
The [Muandet–Fukumizu–Sriperumbudur–Schölkopf review](https://arxiv.org/abs/1605.09522)
was read online. Section 3.2 (Theorem 3.2), Section 4.1 (Definition 4.1,
Theorems 4.1–4.2, and footnote 2 on the Gaussian counterexample),
Theorem 3.4, and Section 3.3.1 were used for items 64, 68, and 73.
[Rahimi and Recht, “Random Features for Large-Scale Kernel Machines”
(NIPS 2007)](https://people.eecs.berkeley.edu/~brecht/papers/07.rah.rec.nips.pdf),
Claim 1 and the Hoeffding remark preceding it, was read online for
item 74. The linear-time MMD consequence there is a triangle-inequality
corollary. Other papers named in items 55 and 71 (Genevay and coauthors;
Mena and Niles-Weed; Liu, Lee, and Jordan; Chwialkowski, Strathmann, and
Gretton) are cited through these sources and were not read here.

Local sources and online papers are distinguished here. The local transport
books supply the analytic background; missing local copies of an original
paper were not taken to preclude consulting its primary online version.

Local texts directly consulted or identified for this selection:

- [Chung, *Spectral Graph Theory*](../lean-CKMA/References/Chung1997SpectralGraphTheory-AMS.CBMS92.pdf).
  The Cheeger constant and Theorems 2.2 and 2.3 were read. The scanned
  formulae are partly damaged; the inequalities in item 1 are those
  completed by the proofs in Chapter 2.
- [Edelsbrunner and Harer, *Computational Topology*](../lean-CKMA/References/EdelsbrunnerHarer2008ComputationalTopologyIntroduction-AuthorManuscript.pdf).
  The nerve theorem and the Čech and Vietoris–Rips comparison were read.
- [Chazal, de Silva, Glisse, and Oudot, *The Structure and Stability of Persistence Modules*](../lean-CKMA/References/ChazalDeSilvaGlisseOudot2016StructureStabilityPersistenceModules-SpringerBriefsMath.pdf).
- [Oudot, *Persistence Theory*](../lean-CKMA/References/Oudot2015PersistenceTheoryQuiverRepresentationsDataAnalysis-AMS.MSM209.pdf).
- [Ghrist, *Elementary Applied Topology*](../lean-CKMA/References/Ghrist2014ElementaryAppliedTopology-CreateSpace.pdf).
- [Bhattacharya and Bhattacharya, *Nonparametric Inference on Manifolds*](../lean-CKMA/References/BhattacharyaBhattacharya2012NonparametricInferenceManifoldsApplicationsShapeSpaces-Cambridge.IMSMonographs.pdf).
- [Dryden and Mardia, *Statistical Shape Analysis*](../lean-CKMA/References/DrydenMardia1998StatisticalShapeAnalysis-Wiley.SerProbStat.pdf).
- [Marron and Dryden, *Object Oriented Data Analysis*](../lean-CKMA/References/MarronDryden2022ObjectOrientedDataAnalysis-ChapmanHallCRC.MSAP169.pdf).
- [Dey and Wang, *Computational Topology for Data Analysis*](../lean-CKMA/References/DeyWang2022ComputationalTopologyDataAnalysis-CambridgeUP.pdf).
- [Pennec, Sommer, and Fletcher (eds.), *Riemannian Geometric Statistics in Medical Image Analysis*](../lean-CKMA/References/PennecSommerFletcherEds2020RiemannianGeometricStatisticsMedicalImageAnalysis-AcademicPress.MICCAI.pdf).
- [Wang, *Geometric Structure of High-Dimensional Data and Dimensionality Reduction*](../lean-CKMA/References/Wang2012GeometricStructureHighDimensionalDataDimensionalityReduction-Springer.pdf).
- [Carlsson and Vejdemo-Johansson, *Topological Data Analysis with Applications*](../lean-CKMA/References/CarlssonVejdemoJohansson2022TopologicalDataAnalysisApplications-Cambridge.pdf).
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
