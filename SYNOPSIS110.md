# Synopsis: Geometric and topological data analysis

Part of the [mathematical synopsis series](SYNOPSIS.md).
[Bibliographical scope and references](CKSD-bib.md#cks-110).

This synopsis follows Section 110. Subdivision 110A is spectral embeddings,
statistics on manifolds, and shape. Subdivision 110B is persistent homology.
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
  squared-distance convexity conditions. Suppose the population mean
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

* **12. Homology from a sample.** Let $M$ be a compact smooth
  $d$-dimensional submanifold without boundary and with reach $\tau>0$.
  If noiseless sample points form a sufficiently fine net relative to a
  ball radius $r$ that is a small fixed fraction of $\tau$, their union
  of balls deformation retracts onto $M$. For independent sampling with
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

## Reference guide

### Correspondence with the subdivisions

- **[110A](#synopsis-110a)**: Chung carries the normalized Laplacian and the
  Cheeger inequality. von Luxburg carries spectral clustering. Coifman and
  Lafon carry diffusion distances, and Belkin and Niyogi carry the
  Laplace–Beltrami limit of the graph Laplacian. Tenenbaum, de Silva, and
  Langford carry Isomap. Bhattacharya and Bhattacharya carry Fréchet means
  on manifolds. Dryden and Mardia carry Kendall shape space. Genovese,
  Perone-Pacifico, Verdinelli, and Wasserman carry the noisy Hausdorff rate.
- **[110B](#synopsis-110b)**: Edelsbrunner and Harer carry Čech and Rips
  complexes, the nerve theorem, and bottleneck stability. Chazal, de Silva,
  Glisse, and Oudot carry the isometry theorem. Oudot carries the algebraic
  theory of barcodes. Niyogi, Smale, and Weinberger carry homology recovery.
  Bubenik carries persistence landscapes. Chazal, Cohen-Steiner, and Mérigot
  carry the distance to a measure. Fasy, Lecci, Rinaldo, Wasserman,
  Balakrishnan, and Singh carry confidence sets.

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
