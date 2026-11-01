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
Mises–Fisher model is [SYNOPSIS105](SYNOPSIS105.md), item 27. The representer
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
  satisfies $\mathop{\mathrm{Ncut}}(S,S^c)\ge\lambda_1$. Indeed, the minimum
  of the Rayleigh quotient $f^\top\mathcal L f/f^\top f$ over nonzero vectors
  orthogonal to $D^{1/2}\mathbf 1$ equals $\lambda_1$, and the vector
  $f=D^{1/2}g$ with $g=1/\mathop{\mathrm{vol}}S$ on $S$ and
  $g=-1/\mathop{\mathrm{vol}}S^c$ on $S^c$ is such a vector with Rayleigh
  quotient $\mathop{\mathrm{Ncut}}(S,S^c)$. This is the spectral clustering
  relaxation of Shi and Malik.

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
  $x\mapsto(\lambda_j^t\psi_j(x))_{1\le j\le m}$.

Let $M\subset\mathbb R^D$ be a compact Riemannian submanifold. A
neighborhood graph joins sample points at Euclidean distance at most
$\varepsilon$. **Isomap** replaces Euclidean distances by shortest-path
distances in that graph and applies classical multidimensional scaling.

* **4. Geodesic approximation.** Let $M$ be a compact connected smooth
  submanifold of positive reach, and let a noiseless sample be a
  $\delta_n$-net in its intrinsic metric. Join pairs at Euclidean
  distance at most $\varepsilon_n$, weighting edges by their Euclidean
  lengths. If $\varepsilon_n\to0$ and
  $\delta_n/\varepsilon_n\to0$, then the maximum over pairs of sample
  points of $|d_{G_n}(x,y)-d_M(x,y)|$ tends to $0$, where $d_{G_n}$ is the
  graph shortest-path distance and $d_M$ the intrinsic distance. If
  $\varphi:M\to\Omega$ is an isometry onto a convex domain
  $\Omega\subset\mathbb R^d$, then $d_M(x,y)=\|\varphi(x)-\varphi(y)\|$,
  so classical multidimensional scaling (item 8) applied to the squared
  intrinsic distances of a finite sample returns the points
  $\varphi(x_i)$ up to a Euclidean isometry.

On a metric space $(M,d)$, the **Fréchet function** of a Borel probability
$\mu$ with finite second moment is
$F(x)=\int_M d(x,y)^2\,\mu(dy)$. A **Fréchet mean** is a minimizer of $F$.

* **5. Fréchet means.** In a complete Hadamard space every probability
  with finite second moment has a unique Fréchet mean; item 13 gives a
  sufficient ball condition on a general Riemannian manifold. Let
  $X_1,X_2,\ldots$ be independent with law $Q$ on a $d$-dimensional
  Riemannian manifold $M$ with geodesic distance $\rho$, and let $\hat m_n$
  be a measurable selection of sample Fréchet means. Suppose that $Q$ has a
  unique Fréchet mean $m$, that $\hat m_n\to m$ almost surely, and that $Q$
  is supported in the domain $U$ of a chart $\phi:U\to\mathbb R^d$. Put
  $h(x,y)=\rho(\phi^{-1}x,\phi^{-1}y)^2$ and $\tilde X=\phi(X_1)$, and
  write $D$ for derivatives in $y$. Assume that for every $x$ the map
  $y\mapsto h(x,y)$ is twice continuously differentiable near
  $\phi(m)$, that $\mathbb E\|Dh(\tilde X,\phi(m))\|^2<\infty$, that
  $\mathbb E\sup_{\|u-v\|\le\varepsilon}\|D^2h(\tilde X,u)-D^2h(\tilde X,v)\|
  \to0$ as $\varepsilon\to0$, and that
  $\Lambda=\mathbb E\,D^2h(\tilde X,\phi(m))$ is nonsingular. Then
  $$\sqrt n\,\bigl(\phi(\hat m_n)-\phi(m)\bigr)\Rightarrow
  N(0,\Lambda^{-1}\Sigma\Lambda^{-1}),\qquad
  \Sigma=\mathop{\mathrm{Cov}}Dh(\tilde X,\phi(m)).$$
  The usual chart is $\phi=\log_m$, the inverse of the exponential map
  on a ball where it is a diffeomorphism.

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
  that eigenvalue is simple. The matrix $ZZ^*$ does not depend on the
  choice of preshape representative $Z$ of the shape. If the largest
  eigenvalue of $\mathbb E[ZZ^*]$ is simple and $Z_1,Z_2,\ldots$ are
  independent copies of $Z$, the sample full Procrustes mean shape, given
  by a top eigenvector of $n^{-1}\sum_iZ_iZ_i^*$, converges almost surely
  to the population mean shape.

* **7. Hausdorff estimation of a submanifold.** Let $M\subset\mathbb R^D$
  be a compact smooth $d$-dimensional submanifold without boundary, and let
  $X_1,\ldots,X_n$ be independent with a law on $M$ whose density with
  respect to volume is bounded below by a positive constant. Then
  $d_H(\{X_1,\ldots,X_n\},M)=O_P((\log n/n)^{1/d})$ as $n\to\infty$. In
  the perpendicular-noise model of Genovese and coauthors, the class
  consists of compact $d$-dimensional submanifolds without boundary
  contained in a fixed compact set and with reach at least $\kappa>0$, and
  each observation is a uniform point of $M$ displaced uniformly in its
  normal ball of fixed radius $0<\sigma<\kappa$. For that model the
  minimax risk $R_n=\inf_{\hat M}\sup_M\mathbb E\,d_H(\hat M,M)$, the
  infimum over estimators from $n$ observations, satisfies, for constants
  $0<c\le C$ independent of $n$ and all large $n$,
  $$c n^{-2/(d+2)}\le R_n\le
  C(\log n/n)^{2/(d+2)}.$$

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

* **9. Locally linear embedding.** Suppose neighborhood reconstruction
  weights $W_{ij}$ vanish off chosen neighborhoods and satisfy
  $\sum_jW_{ij}=1$. For $1\le k<n$, among embeddings with $Z^\top Z=I_k$ and
  $Z^\top1=0$, minimizing
  $$\sum_i\left\|z_i-\sum_jW_{ij}z_j\right\|^2
  =\mathop{\mathrm{tr}}[Z^\top(I-W)^\top(I-W)Z]$$
  is a problem on $1^\perp$, which $(I-W)^\top(I-W)$ maps into itself
  because $(I-W)1=0$. The minimum is the sum of the $k$ smallest
  eigenvalues of $(I-W)^\top(I-W)$ restricted to $1^\perp$, and it is
  attained when the columns of $Z$ are orthonormal eigenvectors in
  $1^\perp$ for those eigenvalues.

Let $j:M\to\mathbb R^D$ be an embedding with closed image. An
**extrinsic mean** minimizes $\mathbb E\|j(X)-j(m)\|^2$ over $m\in M$.

* **10. Extrinsic projection mean.** Let $X_1,X_2,\ldots$ be independent
  copies of $X$. If $j(X)\in L^2$, put
  $\mu=\mathbb E j(X)$. The extrinsic means are the nearest points
  in $j(M)$ to $\mu$. Suppose this projection $P$ is single-valued
  and continuously differentiable in a neighborhood of $\mu$. Then
  $$\sqrt n\left(P\left(n^{-1}\sum_i j(X_i)\right)-P(\mu)\right)
  \Rightarrow N(0,DP_\mu\Sigma DP_\mu^\top),$$
  where $\Sigma=\mathop{\mathrm{Cov}}(j(X))$ and the limit is supported
  on the tangent space at $P(\mu)$. Intrinsic means instead minimize
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
  coordinates of Belkin and Niyogi. For a fixed minimizing column space,
  its orthonormal bases differ by a right orthogonal factor. The column
  space is unique when $k=n-1$ or when $k<n-1$ and
  $\lambda_k<\lambda_{k+1}$; a tie across the truncation boundary allows
  different minimizing column spaces. The trace minimization is the Ky Fan
  principle, CKMA SYNOPSIS13, item 6.

### Fréchet means and Procrustes analysis

* **13. Uniqueness of Fréchet means in small balls.** Let $M$ be a
  complete Riemannian manifold with sectional curvature at most
  $\Delta$ and injectivity radius $\mathop{\mathrm{inj}}(M)$. Put
  $r^*=\frac12\min\{\mathop{\mathrm{inj}}(M),\pi/\sqrt\Delta\}$, read as
  $\frac12\mathop{\mathrm{inj}}(M)$ when $\Delta\le0$. If the support
  of a probability $Q$ lies in an open geodesic ball $B(o,\rho)$ with
  $\rho<r^*$, the Fréchet mean, the global minimizer of
  $p\mapsto\int d(p,x)^2\,Q(dx)$, is unique and lies in $B(o,\rho)$.
  A compact set inside an open ball of radius $r^*$ lies in a concentric
  ball of smaller radius, so for finitely many data points, or any
  compact support, an open ball of radius $r^*$ suffices. This is the
  Karcher–Kendall condition in Afsari's form. On the unit sphere $S^2$
  it covers finite data in any open hemisphere, whereas two antipodal
  points have the whole equator as Fréchet mean set.

* **14. Strong consistency of Fréchet mean sets.** Let $(M,\rho)$ be a
  metric space whose closed bounded sets are compact, and let
  $F(p)=\int\rho(p,x)^\beta\,Q(dx)$ be finite for some $p$, where
  $\beta\ge1$. Then the mean set $C_Q$ of minimizers is nonempty and
  compact. Let $Q_n$ be the empirical measure of $n$ independent
  observations from $Q$. For every $\varepsilon>0$, almost surely the
  sample mean sets $C_{Q_n}$ lie in the $\varepsilon$-neighborhood of
  $C_Q$ for all large $n$. If $C_Q=\{\mu\}$, every measurable choice of
  sample Fréchet mean is strongly consistent for $\mu$. On a compact
  metric space the same holds with $\rho^\beta$ replaced by $f\circ\rho$
  for any continuous $f:[0,\infty)\to\mathbb R$.

* **15. Barycentric equation.** Let $M$ be a complete Riemannian manifold
  and $Q$ a probability with finite second moment. At a point $p$ whose
  cut locus has $Q$-measure zero, the Fréchet function is differentiable,
  with
  $$\nabla F(p)=-2\int\mathop{\mathrm{Log}}_p(x)\,Q(dx).$$
  Hence a Fréchet mean at such a point satisfies
  $\int\mathop{\mathrm{Log}}_p(x)\,Q(dx)=0$. Solutions of this equation
  are called exponential barycenters, or Karcher means. They are critical
  points of $F$ and need not minimize it.

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
  $\Gamma\in SO(m)$, $\beta\ge0$, and $\gamma\in\mathbb R^m$ is attained at
  $$\gamma=0,\qquad\Gamma=UV^\top,\qquad
  \beta=\frac{\mathop{\mathrm{tr}}(X_2^\top X_1\Gamma)}{\|X_1\|^2}.$$
  The minimum is $\|X_2\|^2\sin^2\rho$, where
  $\cos\rho=\sum_i\lambda_i$ and $\rho\in[0,\pi/2]$. If scale is
  restricted to $\beta>0$, attainment
  requires $\sum_i\lambda_i>0$; when this sum is zero the same value is
  only an infimum, approached as $\beta\downarrow0$. The Riemannian shape
  distance remains $\rho$. The full and partial Procrustes distances are
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
  eigenvector of item 6, for the matrix $\sum_iZ_iZ_i^*$ of the
  preshapes.

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

Let $f$ be a continuous function on a triangulable space $X$, write
$X_a=f^{-1}(-\infty,a]$, and fix a field of coefficients. A value $a$ is a
**homological critical value** of $f$ if for no $\varepsilon>0$ the maps
$H_p(X_{a-\varepsilon})\to H_p(X_{a+\varepsilon})$ induced by inclusion
are isomorphisms for every $p$. The function $f$ is **tame** if it has
finitely many homological critical values and every $H_p(X_a)$ is
finite-dimensional. For tame $f$ and each $p$, let
$\mathop{\mathrm{Dgm}}_p(f)$ be the $p$-th persistence diagram of the
sublevel-set filtration: a finite multiset of points $(b,d)$ with
$b<d$, $b\in\mathbb R$, and $d\in\mathbb R\cup\{+\infty\}$, together with
every point of the diagonal with infinite multiplicity. The **bottleneck
distance** $d_B$ between two such diagrams is the infimum, over bijections
between them, of the supremum of the $\ell^\infty$ distances between
matched points, with $|\infty-\infty|=0$.

* **19. Bottleneck stability.** Let $X$ be a triangulable space and
  $f,g:X\to\mathbb R$ tame functions. Then for every $p\ge0$,
  $$d_B\bigl(\mathop{\mathrm{Dgm}}_p(f),\mathop{\mathrm{Dgm}}_p(g)\bigr)
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
  $\tau>0$. Let $P\subset M$ be finite with Hausdorff distance
  $d_H(P,M)=\varepsilon<\sqrt{3/20}\,\tau$. Then for every
  $r\in(2\varepsilon,\sqrt{3/5}\,\tau)$ the offset
  $P^r=\{x:d(x,P)\le r\}$, a union of balls, deformation retracts onto
  $M$. This is the noiseless Niyogi–Smale–Weinberger theorem. Mere
  Hausdorff closeness of an off-manifold cloud does not suffice for this
  radius interval. By the nerve theorem of item 21,
  the Čech complex of radius $r$ then has the homotopy type of $M$.
  If $X_1,\ldots,X_n$ are independent with a law on $M$ whose density
  with respect to volume is bounded below by a positive constant, then
  $d_H(\{X_1,\ldots,X_n\},M)\le\varepsilon$ with probability at least
  $1-\delta$ whenever
  $$n\ge C\varepsilon^{-d}
  (\log(1/\varepsilon)+\log(1/\delta)),$$
  for $0<\varepsilon<\varepsilon_0$ and $0<\delta<1$, where $C$ and
  $\varepsilon_0$ depend only on $M$ and the density bound.

A **persistence landscape** converts a barcode into a sequence of functions
by taking the successive largest values of the tent functions over its bars,
as in item 29.

* **23. Central limit theorem for landscapes.** Realize a landscape
  as $\Lambda\in L^p(\mathbb N\times\mathbb R)$, using counting and
  Lebesgue measure. For independent copies of a random landscape
  $\Lambda$, if $1\le p<\infty$ and
  $\mathbb E\|\Lambda\|_p<\infty$, their mean converges almost surely
  in $L^p$ to $\mathbb E\Lambda$. If $2\le p<\infty$ and
  $\mathbb E\|\Lambda\|_p^2<\infty$, the centered mean multiplied by
  $\sqrt n$ converges in distribution to a centered Gaussian random
  element of $L^p$ with the covariance of $\Lambda$.

For a probability $\mu$ on $\mathbb R^D$, $x\in\mathbb R^D$ and
$u\in(0,1]$, put
$\delta_{\mu,u}(x)=\inf\{r\ge0:\mu(\overline B(x,r))\ge u\}$. For a mass
$m\in(0,1]$, the **distance to the measure** is given by
$$d_{\mu,m}(x)^2=\frac1m\int_0^m\delta_{\mu,u}(x)^2\,du.$$

* **24. Stability of the distance to a measure.** For probabilities on
  $\mathbb R^D$ with finite second moment,
  $$\|d_{\mu,m}-d_{\nu,m}\|_\infty
  \le m^{-1/2}W_2(\mu,\nu).$$
  The right-hand side uses the Wasserstein distance of
  CKMA SYNOPSIS39, item 42.

* **25. Confidence sets for diagrams.** Let $f$ be a tame function on a
  triangulable space and $\hat f_n$ a random tame function on the same
  space, fix $p\ge0$, and write $D=\mathop{\mathrm{Dgm}}_p(f)$ and
  $\hat D_n=\mathop{\mathrm{Dgm}}_p(\hat f_n)$.
  If $r_n$ satisfies $P(\|\hat f_n-f\|_\infty\le r_n)\ge1-\alpha$, then
  by item 19
  $$P\bigl(d_B(\hat D_n,D)\le r_n\bigr)\ge1-\alpha,$$
  so the bottleneck ball of radius $r_n$ about $\hat D_n$ is a confidence
  set for $D$ of coverage at least $1-\alpha$.

The **Mapper** construction pulls a cover back along a filter function,
refines the pullback into connected components, and takes their nerve.
For finite data a chosen clustering rule provides the pullback components.

### Persistent summaries and perturbation certificates

For a finite filtered simplicial complex $K_s\subseteq K_t$, homology
with coefficients in a field gives the **persistent Betti number**
$\beta_q(s,t)=\mathop{\mathrm{rank}}[H_q(K_s)\to H_q(K_t)]$.

* **26. Rank invariant and barcode.** With half-open interval convention
  $[b,d)$, $\beta_q(s,t)$ is the number of degree-$q$ bars with
  $b\le s$ and $d>t$. Thus the two-parameter rank function determines
  the finite barcode with multiplicities. The ordinary Betti number
  $\beta_q(t,t)$ counts bars alive at $t$.

* **27. Hausdorff perturbations and offsets.** For nonempty compact
  subsets $A,B$ of a Euclidean space,
  $$\|d(\cdot,A)-d(\cdot,B)\|_\infty=d_H(A,B).$$
  If $d_H(A,B)\le\eta$, their offset filtrations satisfy
  $A^r\subseteq B^{r+\eta}$ and $B^r\subseteq A^{r+\eta}$.
  Consequently their $q$-tame persistence diagrams are within $\eta$
  in bottleneck distance.

* **28. Empirical distance to a measure.** For the empirical measure of
  $n$ points $X_1,\ldots,X_n$ and $m=k/n$, the square of the distance to
  the measure defined before item 24 is
  $k^{-1}\sum_{i=1}^k\|x-X_{(i)}(x)\|^2$, where the observations are
  ordered by distance to $x$. The function $d_{\mu,m}$ is
  1-Lipschitz, and its perturbation under a change of measure is item 24.

* **29. Landscape stability.** For a finite barcode, replace each bar
  $[b,d)$ by the tent $t\mapsto\max(0,\min(t-b,d-t))$.
  The $k$th landscape function is the $k$th largest tent value at each
  $t$. For two finite diagrams,
  $$\|\Lambda_D-\Lambda_E\|_\infty\le d_B(D,E).$$

* **30. Persistence beyond the error scale.** Let $D,\hat D$ be finite
  diagrams with $d_B(D,\hat D)\le\eta$. Then there is a matching of cost
  at most $\eta$, and under it every finite bar of $\hat D$ of length
  greater than $2\eta$ is matched to a bar of $D$, not to the diagonal,
  with birth and death differing by at most $\eta$. Consequently, on the
  event $d_B(\hat D_n,D)\le r_n$ of item 25, this holds simultaneously for
  all bars of $\hat D_n$ longer than $2r_n$.

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
  $\dim\sigma_j$. For a monotone function $f$ on simplices and an order
  with $f(\sigma_1)\le\cdots\le f(\sigma_m)$, the bars of the sublevel
  filtration of $f$ are the intervals $[f(\sigma_i),f(\sigma_j))$ and
  $[f(\sigma_j),\infty)$ obtained in this way, those of length zero being
  discarded. The same holds over any field with signed boundary matrices.
  The standard column reduction uses $O(m^3)$ field operations.

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

* **35. Wasserstein stability.** Write $D_p^{\mathrm{fin}}(f)$ for the
  finite-death part of the diagram. For tame Lipschitz functions $f,g$ on
  such a space $X$ in a fixed degree $p\ge0$, choose $k\ge1$ with
  $k>j$. For every finite $q\ge k$
  there is $C$ depending on the space, $k,q$, and the Lipschitz constants
  such that, with $\delta=\|f-g\|_\infty>0$,
  $$W_q\bigl(D_p^{\mathrm{fin}}(f),D_p^{\mathrm{fin}}(g)\bigr)
  \le C\delta^{1-k/q}.$$
  The essential bars, whose number is $\beta_p(X)$ in each diagram,
  admit a matching with birth differences at most $\delta$. Consequently
  the full diagrams satisfy
  $$W_q\bigl(\mathop{\mathrm{Dgm}}_p(f),\mathop{\mathrm{Dgm}}_p(g)\bigr)
  \le C\delta^{1-k/q}+\beta_p(X)^{1/q}\delta.$$
  When $\delta=0$ both distances are zero. For
  monotone functions on the simplices of a finite complex $K$, meaning
  $f(\tau)\le f(\sigma)$ whenever $\tau$ is a face of $\sigma$,
  $$W_q\bigl(\mathop{\mathrm{Dgm}}_p(f),\mathop{\mathrm{Dgm}}_p(g)\bigr)
  \le\Bigl(\sum_{\sigma\in K}|f(\sigma)-g(\sigma)|^q\Bigr)^{1/q}.$$

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
  the Čech complexes of radii $i$ and $j$. If instead
  $d_H(K,P)<\varepsilon$ for some $\varepsilon<\mathrm{wfs}(K)/9$ and
  $2\varepsilon\le\alpha\le(\mathrm{wfs}(K)-\varepsilon)/4$, the image of
  $H_*(\mathrm{Rips}(\alpha/2))\to H_*(\mathrm{Rips}(2\alpha))$ is
  isomorphic to $H_*(K^r)$, in the parameter of item 21.

* **38. Rips pairs on a manifold.** Let $M\subset\mathbb R^D$ be a compact
  smooth submanifold with reach $\tau>0$, and let $d_H(P,M)\le\varepsilon$
  for a finite $P$. If
  $3\varepsilon\le\alpha\le\frac3{16}\sqrt{3/5}\,\tau$, then in the
  parameter of item 21
  $$\mathop{\mathrm{rank}}\bigl(H_*(\mathrm{Rips}(\alpha))
  \to H_*(\mathrm{Rips}(2\alpha))\bigr)=\dim H_*(M).$$

A probability $\mu$ with compact support $X_\mu$ in a metric space is
**$(a,b)$-standard** if $\mu(B(x,r))\ge\min(1,ar^b)$ for all $x\in X_\mu$
and $r>0$.

* **39. Rates for persistence diagram estimation.** Let $\hat X_n$ be an
  independent sample of size $n\ge2$ from an $(a,b)$-standard $\mu$. Then
  $\mathbb E\,d_H(\hat X_n,X_\mu)\le C(\log n/n)^{1/b}$ with $C$
  depending on $a$ and $b$. Since $d_{GH}\le d_H$, item 36 gives
  $$\mathbb E\,d_B\bigl(\mathop{\mathrm{Dgm}}\mathrm{Rips}(\hat X_n),
  \mathop{\mathrm{Dgm}}\mathrm{Rips}(X_\mu)\bigr)
  \le C\Bigl(\frac{\log n}n\Bigr)^{1/b}.$$

<a id="synopsis-108b"></a>

## 108B. Optimal Transport and Kernel Discrepancies

### Optimal transport and Wasserstein statistics

Throughout, for $p\ge1$, $W_p$ is the $p$-Wasserstein distance on the space
$\mathcal P_p$ of Borel probabilities with finite $p$th moment, as in
CKMA SYNOPSIS39.

Let $\mu_n$ be the empirical measure of $n$ independent copies of a
probability $\mu$ on $\mathbb R^d$.

* **40. Empirical Wasserstein bounds.** Let $p\ge1$ and let $A$ be a
  bounded subset of $\mathbb R^d$. There is a constant $C$ depending only
  on $p$, $d$, and $A$ such that for every probability $\mu$ supported in
  $A$ and every $n\ge1$,
  $$\mathbb E W_p^p(\mu_n,\mu)\le C
  \begin{cases}n^{-1/2},&p>d/2,\\
  n^{-1/2}\log(1+n),&p=d/2,\\
  n^{-p/d},&p<d/2.
  \end{cases}$$
  More generally, let $q>p$ and
  $M_q(\mu)=\int\|x\|^q\,\mu(dx)<\infty$, and assume $q\ne2p$ if
  $p\ge d/2$ and $q\ne d/(d-p)$ if $p<d/2$. Then the same bound holds
  with $C$ replaced by $CM_q(\mu)^{p/q}$, $C$ depending only on $p,d,q$,
  and with $n^{-(q-p)/q}$ added inside each case.

Let $\mu_1,\ldots,\mu_K\in\mathcal P_2(\mathbb R^d)$ and let
$\lambda_i>0$ sum to one. A **Wasserstein barycenter** minimizes
$\mu\mapsto\sum_{i=1}^K\lambda_i W_2^2(\mu,\mu_i)$.

* **41. Uniqueness of the barycenter.** If at least one $\mu_i$ is
  absolutely continuous, the barycenter exists and is unique.

* **42. Consistency of Brenier maps.** Let $\mu\in\mathcal P_2(\mathbb R^d)$
  be absolutely continuous and let $\nu,\nu_n\in\mathcal P_2(\mathbb R^d)$
  satisfy $W_2(\nu_n,\nu)\to0$. Let $T$ and $T_n$ be the Brenier maps pushing
  $\mu$ forward to $\nu$ and to $\nu_n$, in the sense of CKMA SYNOPSIS39,
  item 46. Then $T_n\to T$ in $L^2(\mu)$.

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
  In particular, $\mathop{\mathrm{GW}}_p(\mu,\nu)=0$ exactly when there is
  an isometry from $\mathop{\mathrm{supp}}\mu$ onto
  $\mathop{\mathrm{supp}}\nu$ pushing $\mu$ forward to $\nu$.

For $\varepsilon>0$ let $\mathop{\mathrm{OT}}_\varepsilon(\mu,\nu)$ be the
entropic transport cost of CKMA SYNOPSIS39, item 90. The **debiased
Sinkhorn divergence** is
$$
S_\varepsilon(\mu,\nu)
=\mathop{\mathrm{OT}}_\varepsilon(\mu,\nu)
-\tfrac12\mathop{\mathrm{OT}}_\varepsilon(\mu,\mu)
-\tfrac12\mathop{\mathrm{OT}}_\varepsilon(\nu,\nu).
$$

* **44. Debiased Sinkhorn divergence.** Let $X$ be a compact metric
  space, $\varepsilon>0$, and $c$ a symmetric Lipschitz cost on $X\times X$
  such that $e^{-c/\varepsilon}$ is a positive definite universal kernel;
  for example, $X$ a compact subset of $\mathbb R^d$ with quadratic cost.
  Then for probabilities on $X$, $S_\varepsilon(\mu,\nu)\ge0$, with
  equality exactly when $\mu=\nu$, and $S_\varepsilon(\mu_n,\mu)\to0$ if
  and only if $\mu_n\Rightarrow\mu$.

### Explicit geometries and empirical inference

* **45. Barycenters on the line.** For $\mu_i\in\mathcal P_2(\mathbb R)$,
  the unique weighted barycenter has quantile function
  $$F_{\bar\mu}^{-1}(u)=\sum_i\lambda_iF_{\mu_i}^{-1}(u).$$
  More generally, for a random measure $\Lambda$ with
  $\mathbb E\int x^2\Lambda(dx)<\infty$, the population barycenter
  has quantile $\mathbb E F_\Lambda^{-1}$ almost everywhere. The map
  $\mu\mapsto F_\mu^{-1}$ is an isometry of $(\mathcal P_2(\mathbb R),W_2)$
  onto the closed convex cone of nondecreasing left-continuous functions
  in $L^2(0,1)$.

* **46. Gaussian transport and barycenters.** For covariance matrices
  $A,B\ge0$,
  $$W_2^2(N(m,A),N(n,B))
  =\|m-n\|^2+\mathop{\mathrm{tr}}
  [A+B-2(A^{1/2}BA^{1/2})^{1/2}].$$
  If $A>0$, the optimal map is
  $x\mapsto n+A^{-1/2}(A^{1/2}BA^{1/2})^{1/2}A^{-1/2}(x-m)$.
  For finitely many Gaussian measures $N(m_i,A_i)$ with $A_i>0$ and
  weights $\lambda_i\ge0$ summing to one, the barycenter is unique and
  Gaussian, with mean $\sum_i\lambda_i m_i$ and covariance the unique
  positive definite solution of
  $$\bar A=\sum_i\lambda_i
  (\bar A^{1/2}A_i\bar A^{1/2})^{1/2}.$$
  If the $A_i$ commute, $\bar A=(\sum_i\lambda_i A_i^{1/2})^2$.

* **47. One-dimensional empirical transport limit.** Suppose $\mu$ is
  supported on $[a,b]$ and has a continuous density bounded above and
  below by positive constants there. Then
  $$nW_2^2(\mu_n,\mu)\Rightarrow
  \int_0^1\frac{B^0(u)^2}{f(F^{-1}(u))^2}\,du,$$
  where $f$ and $F$ are the density and distribution function of $\mu$
  and $B^0$ is a standard Brownian bridge on $[0,1]$. Thus
  $W_2(\mu_n,\mu)=O_P(n^{-1/2})$.

* **48. Sliced Wasserstein distance.** Let $\sigma$ be uniform probability
  on $S^{d-1}$ and $P_\theta(x)=\theta^\top x$. Then
  $$\mathop{\mathrm{SW}}_p(\mu,\nu)
  =\left(\int W_p^p((P_\theta)_\#\mu,(P_\theta)_\#\nu)
  \,\sigma(d\theta)\right)^{1/p}$$
  defines a metric on $\mathcal P_p(\mathbb R^d)$ and is at most
  $W_p(\mu,\nu)$. Definiteness follows from the Cramér–Wold theorem.

* **49. Consistency of empirical barycenters.** Suppose independent
  identically distributed random measures $\Lambda_i$ are supported in a common compact set
  $K\subset\mathbb R^d$, and the population Fréchet functional
  $\mathbb E W_2^2(\mu,\Lambda_1)$ has a unique minimizer $\bar\mu$.
  If $\hat\mu_n$ minimizes $\mu\mapsto n^{-1}\sum_{i=1}^nW_2^2(\mu,\Lambda_i)$
  for each $n$, then $W_2(\hat\mu_n,\bar\mu)\to0$ almost surely.

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
  estimator. For $\mu,\nu$ supported in $[0,1]^d$ and empirical measures
  $\mu_m,\nu_n$ of independent samples, the triangle inequality and
  item 40 give
  $\mathbb E|W_1(\mu_m,\nu_n)-W_1(\mu,\nu)|\le C(m\wedge n)^{-1/d}$, with
  $C$ depending only on $d$.

On the torus $\mathbb T^d=\mathbb R^d/(2\pi\mathbb Z)^d$ with its quotient
metric, the Sobolev space $H^s$, $s$ a positive integer, consists of
densities whose derivatives of order at most $s$ are square integrable.
For $\sigma>0$, the **smoothed Wasserstein distance** is
$W_p^{(\sigma)}(\mu,\nu)=W_p(\mu*N(0,\sigma^2I),\nu*N(0,\sigma^2I))$;
it is a metric on $\mathcal P_p(\mathbb R^d)$.

* **51. Smooth laws and smoothed distances.** Let $d\ge3$, and let
  $\widetilde W_1$ be the dual Lipschitz norm
  $\widetilde W_1(\alpha,\beta)=\sup\{\int f\,d(\alpha-\beta):
  \mathop{\mathrm{Lip}}f\le1\}$, which extends $W_1$ to signed measures of
  equal total mass. Let $\mu$ have a density on $\mathbb T^d$ with $H^s$
  norm at most $L$, and let $\tilde\mu_n$ be the signed measure obtained by
  truncating the empirical Fourier series at frequencies $\|m\|\le M$,
  with $M\asymp n^{1/(d+2s)}$. Then
  $$\mathbb E\widetilde W_1(\tilde\mu_n,\mu)\le Cn^{-(s+1)/(d+2s)},$$
  with $C$ depending only on $d$, $s$, $L$, and the constant in
  $M\asymp n^{1/(d+2s)}$. A probability $\bar\mu_n$ minimizing
  $\widetilde W_1(\cdot,\tilde\mu_n)$ satisfies
  $W_1(\bar\mu_n,\mu)\le2\widetilde W_1(\tilde\mu_n,\mu)$. For the smoothed
  distance and $\mu$ supported in $[-1,1]^d$, with any $d\ge1$,
  $$\mathbb E W_1^{(\sigma)}(\mu_n,\mu)\le C_{\sigma,d}\,n^{-1/2},$$
  with $C_{\sigma,d}$ depending only on $\sigma$ and $d$.

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

* **53. Rates for transport-map estimation.** Let $\mu$ and $\nu$ be
  supported in the unit ball, and let $\nu=(\nabla\varphi)_\#\mu$ with
  $\varphi\in\Phi$. Suppose the potentials in $\Phi$ are uniformly bounded
  there, satisfy $\tfrac12I\preceq\nabla^2\phi\preceq2I$ in the open ball,
  and have covering numbers in the supremum norm on the ball satisfying
  $\log N(\varepsilon,\Phi)\lesssim\varepsilon^{-\gamma}\log(1+\varepsilon^{-1})$
  with $\gamma\in[0,1)$. In this item $\lesssim$ and $\asymp$ hide
  constants independent of $n$ and $\varepsilon$. With $n$ independent
  observations from each law,
  the semidual estimator satisfies
  $\mathbb E\|\nabla\hat\phi-\nabla\varphi\|_{L^2(\mu)}^2\lesssim n^{-1/2}$.
  If moreover $\Phi$ is convex and $\mu$ satisfies a Poincaré
  inequality $\mathop{\mathrm{Var}}_\mu(h)\le C_P\int\|\nabla h\|^2\,d\mu$
  for smooth $h$, the rate improves to
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
  truncated wavelet expansions attains it.

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
  then it is the optimal coupling and $(f,g)$ is dual optimal. Exact maximization in $g$
  for fixed $f$ gives
  $g(y)=-\varepsilon\log\int e^{(f(x)-c(x,y))/\varepsilon}\mu(dx)$, so
  Sinkhorn's iteration is alternating maximization of this dual. With the
  canonical smooth extension
  $f(x)=-\varepsilon\log\int e^{(g(y)-\|x-y\|^2)/\varepsilon}\nu(dy)$,
  $$b_\varepsilon=\nabla\Bigl(\tfrac12\|x\|^2-\tfrac12f(x)\Bigr),$$
  the gradient of a convex function. The entropic map is the
  $L^2(\pi_\varepsilon)$-orthogonal projection of $(x,y)\mapsto y$ onto
  functions of $x$; the pushforward $(b_\varepsilon)_\#\mu$ need not
  equal $\nu$.

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
  Here the implicit constants depend only on $\varepsilon$, growing
  exponentially in $1/\varepsilon$; they do not depend on $d$, $\mu$,
  $\nu$, or $n$.

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
  transport map, piecewise constant on the power diagram.

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
  consistent with item 46.

* **58. First-order conditions for barycenters.** Let
  $F(\gamma)=\frac1{2N}\sum_{i=1}^NW_2^2(\gamma,\mu_i)$. At absolutely continuous
  $\gamma$, $F$ is Fréchet differentiable with gradient
  $$F'(\gamma)=-\frac1N\sum_{i=1}^N\log_\gamma\mu_i
  =-\frac1N\sum_{i=1}^N(t_\gamma^{\mu_i}-\mathrm{id})\in\mathop{\mathrm{Tan}}_\gamma,$$
  in the sense that
  $F(\nu)-F(\gamma)-\langle F'(\gamma),\log_\gamma\nu\rangle_{L^2(\gamma)}
  =o(W_2(\nu,\gamma))$ as $W_2(\nu,\gamma)\to0$.
  An absolutely continuous $\gamma$ with $F'(\gamma)=0$ is a **Karcher
  mean**. That is, $N^{-1}\sum_it_\gamma^{\mu_i}=\mathrm{id}$ holds $\gamma$-almost
  everywhere. If one $\mu_i$ has a bounded density, the Fréchet mean is
  absolutely continuous and hence a Karcher mean. Conversely, let $U$ be
  open and convex, suppose the $\mu_i$ and a Karcher mean $\gamma$ are
  supported in $U$ with bounded, strictly positive densities there, and
  suppose that either $U=\mathbb R^d$ and the densities are Hölder
  continuous, or $U$ is bounded and the densities are bounded below on
  $U$. Then $\gamma$ is the Fréchet mean. (Agueh–Carlier criterion.) Let
  the $\mu_i$ be absolutely continuous. If the closed convex potentials
  $\phi_i$ of the maps $t_\gamma^{\mu_i}$ satisfy
  $N^{-1}\sum_i\phi_i(x)\le\tfrac12\|x\|^2$ everywhere, with equality
  $\gamma$-almost everywhere, then $\gamma$ is the unique Fréchet mean.

* **59. Procrustes iteration for barycenters.** Start from an absolutely
  continuous $\gamma_0$ and set
  $\gamma_{j+1}=\bigl(N^{-1}\sum_it_{\gamma_j}^{\mu_i}\bigr)_\#\gamma_j$, that
  is, $\gamma_{j+1}=\exp_{\gamma_j}(-F'(\gamma_j))$. For absolutely
  continuous $\gamma$ and $\tau\in[0,1]$, the measure
  $\gamma_\tau=\exp_\gamma(-\tau F'(\gamma))$ is absolutely continuous and
  $F(\gamma_\tau)-F(\gamma)\le-\|F'(\gamma)\|_{L^2(\gamma)}^2(\tau-\tau^2/2)$;
  the bound is smallest at $\tau=1$. If one $\mu_i$ has a bounded density,
  then the iterates stay in a $W_2$-compact set and every limit point is a
  Karcher mean. If moreover $F$ has a unique stationary point, then
  $W_2(\gamma_j,\bar\mu)\to0$, where $\bar\mu$ is the Fréchet mean, and
  there is a set $A$ with $\bar\mu(A)=1$ such that
  $t_{\gamma_j}^{\mu_i}\to t_{\bar\mu}^{\mu_i}$ uniformly on compact
  subsets of $A$. For centered Gaussian $\mu_i$ with one covariance
  nonsingular and a nonsingular centered Gaussian $\gamma_0$, the
  iterates converge to the barycenter of item 46. This is the Wasserstein
  analogue of generalized Procrustes analysis.

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
  $\sqrt n\bigl(\mathop{\mathrm{MMD}}_{u,n}^2-\|\Delta\|_{\mathcal H}^2\bigr)$
  converges in distribution to a centered normal law with variance
  $$4\mathop{\mathrm{Var}}_\mu\langle k(X,\cdot),\Delta\rangle
  +4\mathop{\mathrm{Var}}_\nu\langle k(Y,\cdot),\Delta\rangle,$$
  read as the point mass at $0$ when this variance vanishes.

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
a sufficient condition.

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
  four. Under independence its first Hoeffding projection vanishes and
  $n$ times it converges in distribution to the centered series of
  item 67. Under dependence, $\sqrt n$ times its deviation from HSIC
  converges in distribution to a centered normal law, possibly the point
  mass at $0$.

### Kernel estimation, witnesses, and test calibration

* **64. Empirical kernel means.** If $k(x,x)\le\kappa^2$, then
  $$\mathbb E\|\Phi(\mu_n)-\Phi(\mu)\|_{\mathcal H}^2
  =\frac1n\left(\mathbb E k(X,X)-\|\Phi(\mu)\|_{\mathcal H}^2\right)
  \le\frac{\kappa^2}{n}.$$
  With probability at least $1-\delta$,
  $$\|\Phi(\mu_n)-\Phi(\mu)\|_{\mathcal H}
  \le\frac\kappa{\sqrt n}
  +\kappa\sqrt{\frac{2\log(1/\delta)}n}.$$

* **65. Witness function.** If $\Delta=\Phi(\mu)-\Phi(\nu)\ne0$, the
  function attaining the MMD supremum is
  $$f^*(x)=\frac{\mathbb E_\mu k(x,X)-\mathbb E_\nu k(x,Y)}
  {\|\Delta\|_{\mathcal H}}.$$
  It has RKHS norm one, and its mean difference is the MMD.

* **66. Permutation calibration.** Let $X_1,\ldots,X_m\sim\mu$ and
  $Y_1,\ldots,Y_n\sim\nu$ be independent, let $Z$ be the pooled vector
  of length $N=m+n$, and let $T$ be any statistic of $Z$. Given $Z$, let
  $c_\alpha(Z)$ be the $(1-\alpha)$-quantile of the $N!$ values
  $T(Z_\sigma)$ over permutations $\sigma$, and reject when
  $T(Z)>c_\alpha(Z)$. If $\mu=\nu$, the pooled vector is exchangeable,
  and this test has level at most $\alpha$, conditionally on the
  multiset of pooled values; randomizing on the event
  $T(Z)=c_\alpha(Z)$ gives level exactly $\alpha$. This applies to MMD,
  energy, and empirical transport statistics. For $n$ independent pairs
  $(X_i,Y_i)$ and the null hypothesis that $X_i$ and $Y_i$ are
  independent, the same holds with permutations of $(Y_1,\ldots,Y_n)$
  alone.

* **67. Gram-matrix independence statistic.** Let $K,L$ be the Gram
  matrices of the two coordinates of $n$ independent pairs and put
  $H=I-11^\top/n$. The biased HSIC estimator is
  $$\widehat{\mathop{\mathrm{HSIC}}}_b=n^{-2}\mathop{\mathrm{tr}}(KHLH).$$
  Under independence its $n$-scaled limit is
  $\sum_{r,s}\lambda_r\eta_sZ_{rs}^2$, where $\lambda_r,\eta_s$
  are eigenvalues of the two centered marginal kernel operators.
  The unbiased order-four estimator has the corresponding centered
  series $\sum_{r,s}\lambda_r\eta_s(Z_{rs}^2-1)$. Here the $Z_{rs}$ are
  independent standard normals.

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
  the unbounded kernel $k(x,y)=(1+x^\top y)^2$ and laws with finite fourth
  moments,
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
  metric. Convergence in $W_1$ or in $d_{\mathrm{TV}}$ implies weak
  convergence, but not conversely: on $\mathbb R$,
  $\delta_{1/n}\Rightarrow\delta_0$ while
  $d_{\mathrm{TV}}(\delta_{1/n},\delta_0)=1$, and for
  $\mu_n=(1-\frac1n)\delta_0+\frac1n\delta_n$, $\mu_n\Rightarrow\delta_0$
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
  pairs. Since $\mathbb E_Pk_P(Z,y)=0$ for every $y$, this is the squared
  maximum mean discrepancy between $\mu$ and $P$ for the kernel $k_P$.
  The associated
  degenerate $U$-statistic is the kernel goodness-of-fit statistic of Liu,
  Lee, and Jordan, and of Chwialkowski, Strathmann, and Gretton.

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
  (d) Let $d\ge3$ and $P=N(0,I)$, let $k$ be bounded with bounded
  continuous derivatives $\nabla_xk$, $\nabla_yk$, and
  $\langle\nabla_x,\nabla_y\rangle k$, and put
  $\gamma(r)=\sup\{\max(|k(x,y)|,\|\nabla_xk(x,y)\|,
  |\langle\nabla_x,\nabla_y\rangle k(x,y)|):\|x-y\|\ge r\}$. If
  $\gamma(r)=o(r^{-\alpha})$ as $r\to\infty$ with
  $\alpha=(\tfrac12-\tfrac1d)^{-1}$, then there is a sequence of
  probabilities $\mu_m$ with $\mathop{\mathrm{KSD}}(\mu_m)\to0$ that does not
  converge weakly to $P$. This includes the Gaussian, Matérn, and compactly
  supported Wendland kernels.

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
  SYNOPSIS107, item 13.

* **74. Random Fourier features.** Let $k(x,y)=\psi(x-y)$ be continuous
  and positive definite on $\mathbb R^d$ with $\psi(0)=1$, so its spectral
  measure $\Lambda$ is a probability. Let $\omega_1,\ldots,\omega_D\sim\Lambda$
  and $b_1,\ldots,b_D$ uniform on $[0,2\pi]$ be independent. Put
  $z(x)=\sqrt{2/D}\,(\cos(\omega_j^\top x+b_j))_{j\le D}$. Then
  $\mathbb E\,z(x)^\top z(y)=k(x,y)$. For fixed $x,y$,
  $\mathbb P(|z(x)^\top z(y)-k(x,y)|\ge\varepsilon)\le2e^{-D\varepsilon^2/8}$ by
  Hoeffding's inequality, since each of the $D$ summands of
  $z(x)^\top z(y)$ is $D^{-1}$ times a variable with values in $[-2,2]$.
  Let $\sigma^2=\int\|\omega\|^2\Lambda(d\omega)<\infty$ and let
  $M\subset\mathbb R^d$ be compact with $\sigma\mathop{\mathrm{diam}}M\ge\varepsilon$.
  Then
  $$\mathbb P\Bigl(\sup_{x,y\in M}|z(x)^\top z(y)-k(x,y)|\ge\varepsilon\Bigr)
  \le 98\Bigl(\frac{\sigma\mathop{\mathrm{diam}}M}{\varepsilon}\Bigr)^2
  \exp\Bigl(-\frac{D\varepsilon^2}{32(d+1)}\Bigr).$$
  Hence the probability is at most $\delta$ once
  $D\ge32(d+1)\varepsilon^{-2}
  \log\bigl(98(\sigma\mathop{\mathrm{diam}}M/\varepsilon)^2/\delta\bigr)$.
  For probabilities $\mu,\nu$ on $M$, put
  $\mathop{\mathrm{MMD}}_z(\mu,\nu)^2=\|\int z\,d\mu-\int z\,d\nu\|^2$. On the
  event that the supremum above is less than $\varepsilon$,
  $|\mathop{\mathrm{MMD}}_z(\mu,\nu)^2-\mathop{\mathrm{MMD}}_k(\mu,\nu)^2|\le4\varepsilon$
  for all such $\mu,\nu$. For empirical measures of $n$ points,
  $\mathop{\mathrm{MMD}}_z^2$ takes $O(nD)$ operations. For the Gaussian
  kernel $e^{-\gamma\|x-y\|^2}$, $\sigma^2=2d\gamma$.

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
nerve construction, persistent Betti numbers, diagrams, and stability;
item 19 and the definitions before it are the Stability Theorem for Tame
Functions in its Chapter VIII.2, due to Cohen-Steiner, Edelsbrunner, and
Harer (*Discrete Comput. Geom.* 37, 2007).
Chazal–de Silva–Glisse–Oudot, especially the isometry theorem in Chapter 5,
distinguishes $q$-tameness from a pointwise finite-dimensional interval
decomposition. The new rank and offset statements make the passage from
geometric perturbations to persistence explicit. The Čech–Rips constants
retain the radius convention already used here.

Bhattacharya–Bhattacharya, Chapter 4 and Proposition 4.3, was read for the
extrinsic projection and normal limit; the planar-shape chapters give the
matrix representation of a Procrustes mean. Intrinsic inference instead
needs the chart assumptions of their Theorem 3.10, which item 5 states. Mere geodesic convexity
of a support ball is not used as a sufficient uniqueness theorem.

The original [Genovese and coauthors paper](https://www.jmlr.org/papers/v13/genovese12a.html),
Theorems 1–2 and Section 2, was read online: item 7 now includes its
perpendicular-noise model and logarithmic gap. For landscapes,
[Bubenik's paper](https://www.jmlr.org/papers/v16/bubenik15a.html),
Theorems 8–10, supplies the type-2 requirement. The finite-net size in
item 22 includes the covering logarithm; item 25 takes a calibrated
sup-norm radius as given.

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
Item 22 uses the Niyogi–Smale–Weinberger constants with the essential
restriction $P\subset M$. Oudot, Theorem 4.1, states the same constants
for a nearby cloud in the ambient space, but that extension is false.
For example, 100 equally spaced points on the circle of radius $0.7$
have Hausdorff distance about $0.30115$ from the unit circle, of reach
one. At radius $0.75$ the displayed bounds hold, but every sampling ball
contains the origin and their union is star-shaped. The noiseless
restriction avoids this counterexample. Item 5 points to item 13.

Some statements were not checked against a local full text. Two
earlier entries, on density-corrected Laplace–Beltrami limits (after
Coifman–Lafon and Hein–Audibert–von Luxburg) and on the consistency of
spectral clustering (after von Luxburg–Belkin–Bousquet), were removed for
that reason; see [SYNOPSIS-CONCORDANCE.md](SYNOPSIS-CONCORDANCE.md).

The following primary papers were read online for items 13 and 35–39.
Afsari's paper (Proc. Amer. Math. Soc. 139 (2011), 655–673) could not be
fetched; its Theorem 2.1, as restated by Pennec–Sommer–Fletcher,
Theorem 2.2, and in
[Afsari, Tron, and Vidal, Theorem 2.6 and footnote 11](https://arxiv.org/abs/1201.0925),
requires the support to lie in a ball $B(o,\rho)$ with $\rho<r^*$, and
gives a unique global minimizer inside that ball. Item 13 now states that
hypothesis; Pennec–Sommer–Fletcher state the finite-data case.
[Skraba and Turner, Theorem 4.6](https://arxiv.org/abs/2006.16824)
proves the cellular bound of item 35 with the $\ell^q$ ground metric on
diagram points, and degree by degree with the sum restricted to cells of
dimensions $p$ and $p+1$; the $\ell^\infty$ form stated is weaker. Their
Theorem 3.2 restates the Lipschitz bound of Cohen-Steiner, Edelsbrunner,
Harer, and Mileyko with constant $C_X^{1/q}\max(\mathop{\mathrm{Lip}}f,
\mathop{\mathrm{Lip}}g)^{k/q}$, in agreement with Edelsbrunner–Harer,
Chapter VIII.2, for the finite-death diagrams. Item 35 treats essential
bars separately using bottleneck stability; their births cannot satisfy
the same homogeneous bound under arbitrary constant shifts of the
functions. The Čech statements of item 36 are Oudot, Theorem 7.10,
with the ambient Čech complex of item 21 taking the whole space as
witnesses. The Rips pair of item 37 is
[Chazal and Oudot, Theorem 3.6](https://arxiv.org/abs/0712.2638), also
Dey–Wang, Theorem 6.13, which assume $d_H(K,P)<\varepsilon$; their Rips
parameter is the maximum-edge one, and item 37 converts it. Item 38 is
Dey–Wang, Theorem 6.11, in their diameter-$2r$ parameter. For item 39,
[Chazal, Glisse, Labruère, and Michel](https://www.jmlr.org/papers/v16/chazal15a.html),
Theorem 2 gives the Hausdorff tail bound behind the expectation bound and
Theorem 4 gives the diagram bound with $C$ depending only on $a$ and $b$;
the matching minimax lower bound in their Theorem 4 is not stated.
Federer's reach theory is in his 1959 curvature-measures paper rather than
in the local *Geometric Measure Theory*, so reach is taken from Oudot and
Dey–Wang.

#### Optimal transport and kernel discrepancies

Panaretos–Zemel is present in `ReferencesSuppl`. Section 1.6.3, the
one-dimensional barycenter theorem in Section 3.2.2, and the Gaussian
covariance equation in Section 5.4.1 were read for items 45 and 46.
For item 46,
[Álvarez-Esteban, del Barrio, Cuesta-Albertos, and Matrán, Theorem 4.2 and Corollary 4.5](https://arxiv.org/abs/1511.05355)
were read online: the fixed-point equation has a unique positive definite
solution, already when the $A_i$ are positive semidefinite and one of
them is positive definite, and it is the covariance of the Gaussian
barycenter (also Agueh–Carlier, Theorem 6.1, as cited there).
Chewi–Niles-Weed–Rigollet is also present there; Chapter 2 develops the
distribution-free empirical bounds and why they need not be sharp for
each law. The quantile-process limit in item 47 specializes SYNOPSIS102, items 6 and 28, under compact-support density bounds.

For item 40, [Fournier–Guillin, Theorem 1](https://arxiv.org/abs/1312.2128),
was read online. It gives upper bounds with moment remainders, not an
exact rate for every measure. Its excluded exponents are $q=2p$ for
$p\ge d/2$ and $q=d/(d-p)$ for $p<d/2$, as now stated in item 40; the
bounded-support case follows by taking $q$ large. The bounded-domain positivity statement
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
Claim 1, its proof, and the Hoeffding remark preceding it, was read online
for item 74. Their pointwise remark gives the exponent $D\varepsilon^2/4$;
Hoeffding's inequality for summands in $[-2,2]$ gives $D\varepsilon^2/8$,
which item 74 states. Their Claim 1 gives the uniform bound with constant
$2^8$ and exponent $D\varepsilon^2/(4(d+2))$, but the proof treats
$z(x)^\top z(y)$ as a function of $x-y$, which is false for the features
with random phases $b_j$, and its Hoeffding step for the net is too
optimistic. Item 74 therefore states
[Sutherland and Schneider, “On the Error of Random Fourier Features”
(UAI 2015), Proposition 2](https://arxiv.org/abs/1506.02785), which
treats exactly these features, assumes $\varepsilon\le\sigma\mathop{\mathrm{diam}}M$
for the numerical constant 98, and was read online. The MMD comparison
is a direct corollary. Other papers named in item 71 (Liu, Lee, and Jordan; Chwialkowski, Strathmann, and
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
