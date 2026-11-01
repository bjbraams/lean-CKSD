# Synopsis: Geometric and topological data analysis

Part of the [mathematical synopsis series](SYNOPSIS.md).
[Bibliographical scope and references](CKSD-bib.md#cks-110).

This synopsis follows Section 110. Subdivision 110A is spectral embeddings,
statistics on manifolds, and shape. Subdivision 110B is simplicial and
persistent homology, stability of persistence, and topological inference.
The Riemannian Cheeger inequality is
[CKMA SYNOPSIS14](../lean-CKMA/SYNOPSIS14.md), items 20 and 68. The
Laplace–Beltrami operator is the subject of CKMA Section 53. Metric geometry
and Wasserstein distance are [CKMA SYNOPSIS39](../lean-CKMA/SYNOPSIS39.md).
The von Mises–Fisher model is [SYNOPSIS106](SYNOPSIS106.md), item 13.
Subsampling is [SYNOPSIS103](SYNOPSIS103.md), item 21. The Hilbertian central
limit theorem is [SYNOPSIS104](SYNOPSIS104.md), item 20.

Numbered definitions and results have stable identifiers. Additions take the
next free number and are placed beside related material; numbers need not
increase in reading order. Proofs are outside the scope of this synopsis.

<a id="synopsis-110a"></a>

## 110A. Manifold Learning, Geometric Statistics, and Shape

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
  squared-distance convexity conditions; item 28 gives a sufficient
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

* **16. Classical multidimensional scaling.** For a symmetric matrix
  of proposed squared distances $D^{(2)}$, with zero diagonal, put
  $J=I-11^\top/n$ and $B=-JD^{(2)}J/2$. These are squared Euclidean
  distances if and only if $B$ is positive semidefinite. If
  $B=U\Lambda U^\top\ge0$, the rows of $U\Lambda^{1/2}$ are centered
  coordinates realizing them, unique up to a Euclidean isometry.
  Keeping the largest $k$ positive eigenvalues gives the best rank-at-most-$k$
  positive semidefinite approximation to $B$ in Frobenius norm.
  This optimizes the Gram-matrix criterion, rather than every definition
  of distance stress.

* **17. Locally linear embedding.** Suppose neighborhood reconstruction
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

* **18. Extrinsic projection mean.** If $j(X)\in L^2$, put
  $\mu=\mathbb E j(X)$. The extrinsic means are the nearest points
  in $j(M)$ to $\mu$. Suppose this projection $P$ is single-valued
  and continuously differentiable in a neighborhood of $\mu$. Then
  $$\sqrt n\left(P\left(n^{-1}\sum_i j(X_i)\right)-P(\mu)\right)
  \Rightarrow N(0,DP_\mu\Sigma DP_\mu^\top),$$
  where $\Sigma=\mathop{\mathrm{Cov}}(j(X))$ and the limit is supported
  on the tangent space at $P(\mu)$. Focal points can destroy uniqueness
  or the smooth projection expansion. Intrinsic means instead minimize
  squared geodesic distance, as in item 5.

### Graph Laplacians, eigenmaps, and their limits

Let $W=(w_{ij})$ be a symmetric nonnegative $n\times n$ weight matrix with
zero diagonal, let $D$ be the diagonal matrix of degrees
$d_i=\sum_jw_{ij}$, and put $L=D-W$. When every degree is positive, the
normalized Laplacian is $\mathcal L=D^{-1/2}LD^{-1/2}$ and the
**random-walk Laplacian** is $L_{\mathrm{rw}}=D^{-1}L=I-D^{-1}W$. The
components of the graph are those of the graph of positive weights.

* **24. Laplacian quadratic form and connected components.** For every
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

* **25. Laplacian eigenmaps.** Let the weighted graph be connected with
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

Let $M\subset\mathbb R^D$ be a compact connected smooth $d$-dimensional
submanifold without boundary, with volume measure $v$ and nonpositive
Laplace–Beltrami operator $\Delta$, and let $q$ be a smooth positive
probability density on $M$. For a smooth nonnegative kernel profile $h$
with exponential decay and $\varepsilon>0$, put
$k_\varepsilon(x,y)=h(\|x-y\|^2/\varepsilon)$ and
$p_\varepsilon(x)=\int k_\varepsilon(x,y)q(y)\,v(dy)$. For
$\alpha\in[0,1]$, with
$k_\varepsilon^{(\alpha)}(x,y)=k_\varepsilon(x,y)/(p_\varepsilon(x)p_\varepsilon(y))^{\alpha}$,
the **$\alpha$-normalized diffusion operator** is
$$
P_{\varepsilon,\alpha}f(x)
=\frac{\int k_\varepsilon^{(\alpha)}(x,y)f(y)q(y)\,v(dy)}
{\int k_\varepsilon^{(\alpha)}(x,y)q(y)\,v(dy)} .
$$
Its empirical version replaces $q\,dv$ by the empirical measure of a
sample. For $\alpha=0$ that version is $I-L_{\mathrm{rw}}$ for the weights
$k_\varepsilon(X_i,X_j)$, diagonal included.

* **26. Density-corrected Laplace–Beltrami limits.** For smooth $f$,
  uniformly on $M$,
  $$\lim_{\varepsilon\to0}\frac{P_{\varepsilon,\alpha}f-f}{\varepsilon}
  =c_h\,\frac{\Delta(fq^{1-\alpha})-f\,\Delta(q^{1-\alpha})}{q^{1-\alpha}}
  =c_h\bigl(\Delta f+2(1-\alpha)\langle\nabla\log q,\nabla f\rangle\bigr),$$
  where $c_h>0$ depends only on $h$. Thus $\alpha=1$ gives the
  Laplace–Beltrami operator for every density, $\alpha=1/2$ gives the
  generator of the Langevin diffusion with stationary density $q$, and
  the random-walk normalization $\alpha=0$ carries the drift
  $2\nabla\log q$. For uniform $q$ all normalizations give
  $c_h\Delta$, the Belkin–Niyogi limit. For the empirical operator built
  from $n$ independent points of density $q$, Hein, Audibert, and von
  Luxburg obtain almost sure pointwise convergence when
  $\varepsilon_n\to0$ and $n\varepsilon_n^{d/2+1}/\log n\to\infty$.
  Convergence of eigenvectors is a separate spectral statement.

* **27. Consistency of spectral clustering.** Let $\mathcal X$ be a
  compact metric space with a Borel probability $P$, and let $k$ be a
  fixed continuous symmetric similarity with $k\ge\ell>0$. Put
  $d(x)=\int k(x,y)\,P(dy)$, and use weights $k(X_i,X_j)/n$ on an
  independent sample. For the normalized Laplacian, every eigenvalue
  $\lambda\ne1$ of the limit operator $I-T$, where
  $$Tf(x)=\int\frac{k(x,y)}{\sqrt{d(x)d(y)}}f(y)\,P(dy),$$
  is the almost sure limit of sample eigenvalues. The corresponding
  spectral projections converge, with eigenvectors extended to functions
  on $\mathcal X$ and compared in the uniform norm. For the unnormalized
  Laplacian the limit is $f\mapsto df-\int k(\cdot,y)f(y)\,P(dy)$, whose
  essential spectrum is the range of $d$. Eigenvalues outside that range
  converge with their eigenspaces, but inside it convergence can fail.
  This is the result of von Luxburg, Belkin, and Bousquet. Normalized
  spectral clustering is thus consistent under these hypotheses with a
  fixed kernel.

### Fréchet means and Procrustes analysis

* **28. Uniqueness of Fréchet means in small balls.** Let $M$ be a
  complete Riemannian manifold with sectional curvature at most
  $\Delta$ and injectivity radius $\mathop{\mathrm{inj}}(M)$. Put
  $r^*=\frac12\min\{\mathop{\mathrm{inj}}(M),\pi/\sqrt\Delta\}$, read as
  $\frac12\mathop{\mathrm{inj}}(M)$ when $\Delta\le0$. If the data, or
  the support of a probability, lie in an open geodesic ball of radius
  $r^*$, the Fréchet mean is unique. This is the Karcher–Kendall
  condition in Afsari's form. On the unit sphere $S^2$ it covers every
  open hemisphere, whereas two antipodal points have the whole equator
  as Fréchet mean set.

* **29. Strong consistency of Fréchet mean sets.** Let $(M,\rho)$ be a
  metric space whose closed bounded sets are compact, and let
  $F(p)=\int\rho(p,x)^\beta\,Q(dx)$ be finite for some $p$, where
  $\beta\ge1$. Then the mean set $C_Q$ of minimizers is nonempty and
  compact. For every $\varepsilon>0$, almost surely the sample mean sets
  $C_{Q_n}$ lie in the $\varepsilon$-neighborhood of $C_Q$ for all large
  $n$. If $C_Q=\{\mu\}$, every measurable choice of sample Fréchet mean
  is strongly consistent for $\mu$. On a compact space any continuous
  loss of the distance may be used. The sample sets need not fill out a
  nonsingleton $C_Q$.

* **30. Barycentric equation.** Let $M$ be a complete Riemannian manifold
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
  as those of item 28. Tangent principal component analysis
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

* **31. Ordinary Procrustes analysis.** For centered nonzero
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

* **32. Generalized Procrustes analysis and the full Procrustes mean.**
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

<a id="synopsis-110b"></a>

## 110B. Persistent Homology and Computational Topology

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

* **8. Interval decomposition.** A pointwise finite-dimensional persistence
  module over a field decomposes as a direct sum of interval modules. The
  multiset of intervals is unique.

For tame functions $f,g$ on a triangulable space, let
$\mathop{\mathrm{Dgm}}(f)$ be the persistence diagram of a sublevel-set, or
other standard, filtration. The **bottleneck distance** $d_B$ is the
infimum, over bijections of the diagrams with the diagonal available, of
the largest $\ell^\infty$ displacement of a point.

* **9. Bottleneck stability.** For tame functions,
  $$d_B\bigl(\mathop{\mathrm{Dgm}}(f),\mathop{\mathrm{Dgm}}(g)\bigr)
  \le\|f-g\|_\infty.$$

An **$\varepsilon$-interleaving** consists of maps
$f_t:U_t\to V_{t+\varepsilon}$ and $g_t:V_t\to U_{t+\varepsilon}$
commuting with structure maps, such that
$g_{t+\varepsilon}f_t=U_{t,t+2\varepsilon}$ and
$f_{t+\varepsilon}g_t=V_{t,t+2\varepsilon}$.
The **interleaving distance** is the infimum of such $\varepsilon\ge0$;
it can vanish for distinct modules that differ only in endpoint decorations.

* **10. Isometry theorem.** For $q$-tame persistence modules the
  interleaving distance equals the bottleneck distance between their
  persistence diagrams.

Let $S$ be a finite set in a metric space. The **Čech complex** at radius
$r\ge0$ is the nerve of the closed balls of radius $r$ centered at the
points of $S$. In the parameterization of Edelsbrunner and Harer, the
**Vietoris–Rips complex** at parameter $r$ consists of the subsets of $S$
of diameter at most $2r$.

* **11. Čech, Rips, and the nerve.** In Euclidean space,
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

* **12. Homology from a sample.** Let $M\subset\mathbb R^D$ be a compact
  smooth $d$-dimensional submanifold without boundary and with reach
  $\tau>0$. Let $P$ be finite with Hausdorff distance
  $d_H(P,M)=\varepsilon<\sqrt{3/20}\,\tau$. Then for every
  $r\in(2\varepsilon,\sqrt{3/5}\,\tau)$ the offset
  $P^r=\{x:d(x,P)\le r\}$, a union of balls, deformation retracts onto
  $M$. Niyogi, Smale, and Weinberger prove this for $P\subset M$; Oudot
  states it for a point cloud near $M$. By the nerve theorem of item 11,
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

* **13. Central limit theorem for landscapes.** Realize a landscape
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

* **14. Stability of the distance to a measure.** For probabilities with
  finite second moment,
  $$\|d_{\mu,m}-d_{\nu,m}\|_\infty
  \le m^{-1/2}W_2(\mu,\nu).$$
  The right-hand side uses the Wasserstein distance of
  CKMA SYNOPSIS39, item 42.

* **15. Confidence sets for diagrams.** Suppose a population diagram
  $D$ and empirical diagram $\hat D_n$ satisfy
  $d_B(\hat D_n,D)\le\|\hat f_n-f\|_\infty$ by stability. Any radius
  $r_n$ with $P(\|\hat f_n-f\|_\infty\le r_n)\ge1-\alpha$
  gives a bottleneck confidence ball of coverage at least $1-\alpha$.
  An estimated quantile can replace the radius only when its calibration
  is justified. In particular, subsampling requires a continuous limiting
  law for the normalized statistic and the scale and centering conditions
  of SYNOPSIS103, item 21. There is no unconditional subsampling theorem
  for every density or distance filtration.

The **Mapper** construction pulls a cover back along a filter function,
refines the pullback into connected components, and takes their nerve.
For finite data a chosen clustering rule provides the pullback components;
the resulting summary depends on that rule and the cover.

### Persistent summaries and perturbation certificates

For a finite filtered simplicial complex $K_s\subseteq K_t$, homology
with coefficients in a field gives the **persistent Betti number**
$\beta_q(s,t)=\mathop{\mathrm{rank}}[H_q(K_s)\to H_q(K_t)]$.

* **19. Rank invariant and barcode.** With half-open interval convention
  $[b,d)$, $\beta_q(s,t)$ is the number of degree-$q$ bars with
  $b\le s$ and $d>t$. Thus the two-parameter rank function determines
  the finite barcode with multiplicities. The ordinary Betti number
  $\beta_q(t,t)$ counts bars alive at $t$; it loses the information
  about which classes survive from one scale to another.

* **20. Hausdorff perturbations and offsets.** For nonempty compact
  subsets $A,B$ of a Euclidean space,
  $$\|d(\cdot,A)-d(\cdot,B)\|_\infty=d_H(A,B).$$
  If $d_H(A,B)\le\eta$, their offset filtrations satisfy
  $A^r\subseteq B^{r+\eta}$ and $B^r\subseteq A^{r+\eta}$.
  Consequently their $q$-tame persistence diagrams are within $\eta$
  in bottleneck distance. This turns geometric sampling control into
  a topological error bound without choosing one reconstruction scale.

* **21. Empirical distance to a measure.** Define
  $\delta_{\mu,u}(x)=\inf\{r\ge0:\mu(\overline B(x,r))\ge u\}$ and
  $$d_{\mu,m}(x)^2=\frac1m\int_0^m\delta_{\mu,u}(x)^2\,du.$$
  For an empirical measure with $n$ atoms and $m=k/n$, this is
  $k^{-1}\sum_{i=1}^k\|x-X_{(i)}(x)\|^2$, where the observations are
  ordered by distance to $x$. Averaging nearby mass replaces dependence
  on the single closest observation. The function $d_{\mu,m}$ is
  1-Lipschitz, and its perturbation under a change of measure is item 14.

* **22. Landscape stability.** For a finite barcode, replace each bar
  $[b,d)$ by the tent $t\mapsto\max(0,\min(t-b,d-t))$.
  The $k$th landscape function is the $k$th largest tent value at each
  $t$. For two finite diagrams,
  $$\|\Lambda_D-\Lambda_E\|_\infty\le d_B(D,E).$$
  Thus landscape evaluation and averaging are compatible with bottleneck
  perturbation control. A bound in $L^p$ additionally depends on the
  number, lengths, or total persistence of bars; a uniform bound alone
  does not give it on an unbounded domain.

* **23. Persistence beyond the error scale.** If $d_B(D,\hat D)\le\eta$,
  every finite bar in $\hat D$ of length greater than $2\eta$ must
  match an off-diagonal bar of $D$, with birth and death errors at most
  $\eta$. Such a bar cannot be matched to the diagonal. Applying this
  statement on the confidence event in item 15 gives a simultaneous
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

* **33. Euler–Poincaré formula.** For homology over any field,
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

* **34. Persistence pairing by matrix reduction.** For every such
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

* **35. Zero-dimensional persistence and single linkage.** Let $(X,d)$
  be a finite metric space with $n$ points, filtered by Rips complexes
  with the maximum-edge parameter of item 11. The degree-zero barcode
  has $n$ bars born at $0$, one of them infinite. The $n-1$ finite death
  times are, as a multiset, the edge lengths of any minimum spanning tree
  of the complete graph weighted by $d$. They are the merge heights of
  single-linkage hierarchical clustering, as computed by Kruskal's
  algorithm. In the diameter-$2r$ parameter they are halved.

* **36. Sublevel persistence of a Morse function.** Let $f$ be a Morse
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

* **37. Wasserstein stability.** For tame Lipschitz functions $f,g$ on
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

* **38. Gromov–Hausdorff stability of Rips persistence.** For totally
  bounded metric spaces $X,Y$, the homology of their Rips filtrations is
  $q$-tame. In the diameter-$2r$ parameter of item 11,
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

* **39. Homology inference with positive weak feature size.** Let
  $d_H(K,P)=\varepsilon<\mathrm{wfs}(K)/4$ for a finite $P$. If
  $\varepsilon<i$ and $i+2\varepsilon\le j<\mathrm{wfs}(K)-\varepsilon$,
  the image of $H_*(P^i)\to H_*(P^j)$ is isomorphic to $H_*(K^r)$ for
  every $r\in(0,\mathrm{wfs}(K))$. By the nerve theorem the same holds for
  the Čech complexes of radii $i$ and $j$. If
  $\varepsilon<\mathrm{wfs}(K)/9$ and
  $2\varepsilon\le\alpha\le(\mathrm{wfs}(K)-\varepsilon)/4$, the image of
  $H_*(\mathrm{Rips}(\alpha/2))\to H_*(\mathrm{Rips}(2\alpha))$ is
  isomorphic to $H_*(K^r)$, in the parameter of item 11. Single offsets
  of $P$ need not have the homology of $K^r$, and $K$ itself need not
  have the homotopy type of its small offsets.

* **40. Rips pairs on a manifold.** Let $M\subset\mathbb R^D$ be a compact
  smooth submanifold with reach $\tau>0$, and let $d_H(P,M)\le\varepsilon$
  for a finite $P$. If
  $3\varepsilon\le\alpha\le\frac3{16}\sqrt{3/5}\,\tau$, then in the
  parameter of item 11
  $$\mathop{\mathrm{rank}}\bigl(H_*(\mathrm{Rips}(\alpha))
  \to H_*(\mathrm{Rips}(2\alpha))\bigr)=\dim H_*(M).$$
  The proof sandwiches the Rips complexes between Čech complexes whose
  homology is that of $M$, by item 11 and the offset theorem of item 12.

A probability $\mu$ with compact support $X_\mu$ in a metric space is
**$(a,b)$-standard** if $\mu(B(x,r))\ge\min(1,ar^b)$ for all $x\in X_\mu$
and $r>0$.

* **41. Rates for persistence diagram estimation.** Let $\hat X_n$ be an
  independent sample of size $n$ from an $(a,b)$-standard $\mu$. A
  covering argument gives
  $\mathbb E\,d_H(\hat X_n,X_\mu)\le C(\log n/n)^{1/b}$ with $C$
  depending on $a$ and $b$. Since $d_{GH}\le d_H$, item 38 gives
  $$\mathbb E\,d_B\bigl(\mathop{\mathrm{Dgm}}\mathrm{Rips}(\hat X_n),
  \mathop{\mathrm{Dgm}}\mathrm{Rips}(X_\mu)\bigr)
  \le C\Bigl(\frac{\log n}n\Bigr)^{1/b}.$$
  Chazal, Glisse, Labruère, and Michel show that this rate is minimax
  over $(a,b)$-standard measures up to the logarithmic factor. The target
  is the diagram of the support; outliers or ambient noise call instead
  for the distance to a measure of items 14 and 21.

## Reference guide

### Correspondence with the subdivisions

- **[110A](#synopsis-110a)**: Chung carries the normalized Laplacian and the
  Cheeger inequality. von Luxburg carries spectral clustering. Coifman and
  Lafon carry diffusion distances, and Belkin and Niyogi carry the
  Laplace–Beltrami limit of the graph Laplacian. Tenenbaum, de Silva, and
  Langford carry Isomap. Bhattacharya and Bhattacharya carry Fréchet means
  on manifolds. Dryden and Mardia carry Kendall shape space. Genovese,
  Perone-Pacifico, Verdinelli, and Wasserman carry the noisy Hausdorff rate.
  von Luxburg, Belkin, and Bousquet carry the consistency of spectral
  clustering, and Hein, Audibert, and von Luxburg the sampled graph
  Laplacian. Pennec, Sommer, and Fletcher carry Fréchet-mean uniqueness,
  exponential barycenters, and principal geodesic analysis. Dryden and
  Mardia also carry ordinary and generalized Procrustes analysis.
- **[110B](#synopsis-110b)**: Edelsbrunner and Harer carry Čech and Rips
  complexes, the nerve theorem, and bottleneck stability. Chazal, de Silva,
  Glisse, and Oudot carry the isometry theorem. Oudot carries the algebraic
  theory of barcodes. Niyogi, Smale, and Weinberger carry homology recovery.
  Bubenik carries persistence landscapes. Chazal, Cohen-Steiner, and Mérigot
  carry the distance to a measure. Fasy, Lecci, Rinaldo, Wasserman,
  Balakrishnan, and Singh carry confidence sets. Dey and Wang carry the
  reduction algorithm, Wasserstein and Gromov–Hausdorff stability, and
  homology inference from Rips pairs. Chazal and Lieutier, through Oudot,
  carry the weak feature size. Chazal, Glisse, Labruère, and Michel carry
  minimax rates for diagram estimation.

### Source comparisons and local copies

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
item 12 includes the covering logarithm; confidence calibration in item 15
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

For the third expansion (items 24–41 and the revision of item 12), the
following local passages were read. Chung, Lemma 1.7, gives the kernel and
spectral range of the normalized Laplacian in item 24. Wang, *Geometric
Structure of High-Dimensional Data*, Chapter 12.1, gives the Laplacian
eigenmap optimization of item 25, and Section 8.5 the Isomap justification
behind item 4. Pennec–Sommer–Fletcher, Chapter 2 (Theorems 2.1–2.2,
Example 2.4, Sections 2.2.2 and 2.3.2) and Chapter 5 (exponential
barycenters), give items 28 and 30. Bhattacharya–Bhattacharya,
Theorems 3.2–3.3 and Corollary 3.4, give item 29. Dryden–Mardia,
Results 4.1–4.2, Definitions 4.12–4.14, Result 5.1, Definitions 5.3–5.5,
and Result 5.2, give items 31 and 32; the dimension formula is from their
Section 4.1. Edelsbrunner–Harer, Chapter IV (Euler–Poincaré), Chapter VI
(handles and the PL Morse inequalities), Chapter VII (Pairing Lemma), and
Chapter VIII.2 (Wasserstein stability), give items 33, 34, 36, and 37.
Dey–Wang, Theorems 1.3–1.4, 3.2–3.6 and Fact 3.6, Section 3.5 on minimum
spanning trees, Theorem 6.3, Proposition 6.10, Theorem 6.11,
Proposition 6.12, and Theorem 6.13, give items 34–40; their Rips
parameter is the diameter-$2r$ one of item 11. Oudot, Chapter 2.2.3,
Chapter 4.1 (Theorem 4.1, Lemma 4.3, Theorem 4.4), and Chapter 7
(Theorems 7.2 and 7.5, maximum-edge parameter), give items 12, 35, 38,
and 39. Carlsson–Vejdemo-Johansson, Section 4.1, gives single linkage.
Item 12 was sharpened to the Niyogi–Smale–Weinberger constants as stated
in Oudot, Theorem 4.1, and item 5 now points to item 28.

Some statements were not checked against a local full text. Item 26 is
recorded from Coifman–Lafon (*Diffusion maps*, 2006, Theorem 2) for the
population limit and from Hein, Audibert, and von Luxburg (COLT 2005 and
JMLR 2007) for the sampled bandwidth condition. Item 27 is recorded from von
Luxburg, Belkin, and Bousquet, *Consistency of spectral clustering*
(Annals of Statistics, 2008). The Skraba–Turner cellular bound in item 37
is checked only against its statement in Dey–Wang, Theorem 3.4. The
minimax lower bound in item 41 is from Chazal, Glisse, Labruère, and
Michel (JMLR, 2015), cited but not reproduced in Oudot, Chapter 8; the
upper bound follows from a covering argument and item 38. Afsari's form
of the uniqueness radius in item 28 is as quoted by Pennec–Sommer–Fletcher.
Federer's reach theory is in his 1959 curvature-measures paper rather than
in the local *Geometric Measure Theory*, so reach is taken from Oudot and
Dey–Wang.

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
