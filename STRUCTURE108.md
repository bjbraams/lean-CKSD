# Structure 108: Geometry of data: manifolds, topology, optimal transport, and kernels

Part of the [Mathlib, TauCeti, and Statlib coverage series](STRUCTURE.md).
[Mathematical inventory](SYNOPSIS108.md); [bibliographical scope](CKSD-bib.md#cks-108).

This file follows the thematic order and lettered subdivisions of the mathematical inventory. It records definitions, structures, and proved results, with supporting material identified separately. A topic heading locates the recorded statements; it does not assert coverage of every result in the corresponding synopsis. The closing line of each topic section sorts the numbered synopsis entries under that heading.

**Source baseline.** Mathlib `6135ffb78e8bcd3fcc8ec02f3f82ea0b0737358b` of 2026-11-05, TauCeti `afa08a3ed16fb167e35de371afb1eb03fbc5913a` of 2026-11-06, and Statlib `eeaac0283690efaa60c31115400cf561836baeb9` of 2026-11-05, checked against local checkouts on 2026-11-06. See the [revision and source conventions](STRUCTURE.md#source-baseline-and-conventions).

**Mathlib source areas.** `Mathlib.Combinatorics.SimpleGraph.LapMatrix`, `Mathlib.Analysis.InnerProductSpace.Rayleigh`, `Mathlib.Analysis.Matrix.Spectrum`, `Mathlib.Analysis.InnerProductSpace.GramMatrix`, `Mathlib.Analysis.InnerProductSpace.SingularValues`, `Mathlib.Topology.MetricSpace.HausdorffDistance`, `Mathlib.Topology.MetricSpace.GromovHausdorff`, `Mathlib.AlgebraicTopology.SimplicialComplex.Basic`, `Mathlib.Analysis.Convex.SimplicialComplex.Basic`, `Mathlib.Algebra.Homology.EulerCharacteristic`, `Mathlib.Geometry.Manifold.Riemannian.Basic`, `Mathlib.Analysis.InnerProductSpace.Reproducing`, `Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic`, `Mathlib.Probability.CramerWold`, `Mathlib.Probability.StrongLaw`, `Mathlib.Probability.CentralLimitTheorem`, `Mathlib.Probability.Moments.SubGaussian`, `Mathlib.Probability.Moments.CovarianceBilin`, `Mathlib.MeasureTheory.Measure.Prokhorov`, `Mathlib.MeasureTheory.Measure.LevyProkhorovMetric`.

**Namespaces.** Graph Laplacians are `SimpleGraph`. Rayleigh quotients and the spectral theorem are `LinearMap.IsSymmetric` and `Matrix.IsHermitian`; Gram matrices are `Matrix`. Hausdorff distance and distance functions to sets are `Metric`; the Gromov–Hausdorff space is `GromovHausdorff`. Reproducing-kernel Hilbert spaces are the class `RKHS`. Probability limit theorems are `ProbabilityTheory`. In TauCeti, Fréchet barycenters, Wasserstein and Gromov–Wasserstein distances, entropic transport, Bochner's theorem, simplicial chains and Morse theory are in the namespace `TauCeti`, with Wasserstein-space statements under `TauCeti.WassersteinSpace`, Gaussian transport under `TauCeti.Probability`, singular-homology Čech complexes under `TauCeti.TopCat`, Riemannian exponential maps under `TauCeti.Manifold`, kernel mean embeddings under `Matrix.PosSemidef`, Ky Fan sums under `LinearMap`, the Euler–Poincaré identity for chain complexes under `ChainComplex`, Euler characteristics of simplicial realizations under `AbstractSimplicialComplex`, and the discrete Sinkhorn iteration under `Matrix`. Statlib declarations relevant here are the integral forms of the total variation distance in `ProbabilityTheory`.

<a id="structure-108a"></a>

## 108A. Manifold Learning, Geometric Statistics, Shape, and Persistent Homology

[Mathematical scope](SYNOPSIS108.md#synopsis-108a).

Spectral graph methods, Fréchet means, shape analysis, and topological data analysis are grouped here. The formal record is thin. Mathlib has the unweighted graph Laplacian with its component count, the spectral theorem and Rayleigh quotients, Hausdorff and Gromov–Hausdorff distances, and abstract simplicial complexes. TauCeti adds Fréchet barycenters on metric spaces with their strong consistency, CAT(0) uniqueness, Ky Fan and Procrustes inequalities, simplicial chain complexes with Euler–Poincaré identities and their comparison with singular homology, and Riemannian exponential maps. Statlib, a library of statistical divergences and tests, has nothing specific to this subdivision. Persistence modules, barcodes, filtered complexes, Čech and Rips complexes, and every stability or inference theorem of topological data analysis are absent from all three libraries.

### Manifold learning, geometric statistics, and shape

[Mathematical scope](SYNOPSIS108.md#manifold-learning-geometric-statistics-and-shape).

#### Mathlib

**Spectral supporting material.** For a symmetric operator on a finite-dimensional inner product space, the supremum and the infimum of the Rayleigh quotient over nonzero vectors are eigenvalues (`LinearMap.IsSymmetric.hasEigenvalue_iSup_of_finiteDimensional`, `Analysis/InnerProductSpace/Rayleigh.lean`), and a Hermitian matrix is unitarily diagonalizable (`Matrix.IsHermitian.spectral_theorem`, `Analysis/Matrix/Spectrum.lean`). These are the ingredients of item 2, but neither the normalized Laplacian nor any Rayleigh quotient restricted to the orthogonal complement of \(D^{1/2}\mathbf 1\) is formalized. No Cheeger constant, conductance, or normalized cut of a weighted graph is defined. No reversible Markov matrix with its \(L^2(\pi)\) spectral expansion, and hence no diffusion distance, is defined.

**Riemannian supporting material.** Riemannian manifolds, the length of piecewise smooth paths, and the induced distance are set up (`IsRiemannianManifold`, `Geometry/Manifold/Riemannian/Basic.lean`, `Geometry/Manifold/Riemannian/PathELength.lean`). Fréchet means, submanifolds of positive reach, and Hausdorff estimation of a support are not defined. Projective spaces exist as `Projectivization` (`LinearAlgebra/Projectivization/Basic.lean`), but Kendall's shape space is not.

#### TauCeti

**Fréchet barycenters in metric spaces.** For a measure \(\mu\) on a pseudometric space and an exponent \(p\in(0,\infty]\), the Fréchet radius \(R_p(x)=\|d(x,\cdot)\|_{L^p(\mu)}\) is defined, and a Fréchet barycenter is a point of finite radius minimizing it (`TauCeti.frechetRadius`, `TauCeti.IsFrechetBarycenter`, [Fréchet radii](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/MeasureTheory/Measure/FrechetMean/Basic.lean)). For \(p=2\) and a probability \(\mu\) these are the minimizers of the Fréchet function \(F\) of the synopsis. For \(1\le p\), on a proper metric space, a probability law with finite radius at one point has a barycenter, and its set of barycenters is compact (`TauCeti.exists_isFrechetBarycenter`, `TauCeti.isCompact_frechetBarycenters`).

**Nonpositive curvature.** CAT(0) spaces are defined by the Bruhat–Tits CN inequality ([CAT(0)](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Topology/MetricSpace/CATZero.lean)). The quadratic Fréchet functional of a nonzero measure on a CAT(0) metric space is strongly convex along geodesic segments, so there is at most one quadratic barycenter (`TauCeti.IsGeodesicSegment.frechetPower_two_add_le`, `TauCeti.subsingleton_frechetBarycenters_two`, [CAT(0) barycenters](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/MeasureTheory/Measure/FrechetMean/CATZero.lean)). In a proper CAT(0) space, a law with finite second moment has exactly one quadratic barycenter, and empirical quadratic barycenters of an i.i.d. sample converge to it almost surely (`TauCeti.exists_isFrechetBarycenter_two_tendsto_empiricalMeasure_ae`, [empirical barycenters](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/MeasureTheory/Measure/FrechetMean/Empirical.lean)). Existence in a complete Hadamard space that is not proper is not proved. No Riemannian manifold is shown to be CAT(0).

**Riemannian supporting material.** On a smooth finite-dimensional Riemannian manifold, the exponential map is defined on its natural star-shaped open domain, is smooth there, and is a local diffeomorphism at the origin (`TauCeti.Manifold.riemannianExp`, [exponential map](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Geometry/Manifold/Riemannian/Geodesic/Exponential.lean)). The Hopf–Rinow theorem is proved ([Hopf–Rinow](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Geometry/Manifold/Riemannian/Geodesic/HopfRinow.lean)). Sectional curvature of a metric-compatible connection is defined (`CovariantDerivative.sectionalCurvature`, [sectional curvature](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Geometry/Manifold/VectorBundle/CovariantDerivative/Curvature/Sectional/Basic.lean)). The central limit theorem for Fréchet means in a chart, which needs the Riemannian logarithm and second-order expansion of \(\rho^2\), is not formalized.

#### Statlib

No relevant declarations were found.

**Synopsis entries.** Partly covered: 108.5 (uniqueness of quadratic barycenters in CAT(0) metric spaces, and existence with almost-sure convergence of empirical barycenters in proper CAT(0) spaces, in TauCeti; existence in non-proper Hadamard spaces and the central limit theorem on manifolds are absent). Not covered: 108.1, 108.2, 108.3, 108.4, 108.6, 108.7.

### Spectral coordinates and extrinsic statistics

[Mathematical scope](SYNOPSIS108.md#spectral-coordinates-and-extrinsic-statistics).

#### Mathlib

As supporting material, the Gram matrix of a family of vectors is positive semidefinite, and it is positive definite exactly when the family is linearly independent (`Matrix.posSemidef_gram`, `Matrix.posDef_gram_iff_linearIndependent`, `Analysis/InnerProductSpace/GramMatrix.lean`). Singular values of finite-dimensional linear maps are defined (`LinearMap.singularValues`, `Analysis/InnerProductSpace/SingularValues.lean`). The double-centred matrix \(-JD^{(2)}J/2\), Schoenberg's criterion for Euclidean distance matrices, and classical multidimensional scaling are not formalized. No extrinsic mean, nearest-point projection onto an embedded manifold, or delta-method limit on a manifold is present.

#### TauCeti

**Trace and low-rank principles (supporting).** Ky Fan's trace inequality is proved: for a symmetric operator and an orthonormal family with \(k\) members, the diagonal entries \(\mathrm{re}\langle Tw_i,w_i\rangle\) sum to at most the sum of the \(k\) largest eigenvalues (`LinearMap.IsSymmetric.sum_re_inner_apply_self_le_sum_eigenvalues`, [Ky Fan](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Analysis/InnerProductSpace/KyFan.lean)). Applied to \(-T\), this gives the minimum principle behind item 9, but the restriction to \(\mathbf 1^\perp\) and the locally linear embedding problem itself are not stated. The Courant–Fischer min–max theorem is proved (`LinearMap.IsSymmetric.eigenvalues_eq_iSup_iInf_re_inner`, [Courant–Fischer](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Analysis/InnerProductSpace/CourantFischer.lean)). The Eckart–Young theorem is proved in operator norm: the distance from a map to the maps of rank at most \(n\) is its \(n\)-th singular value (`ContinuousLinearMap.singularValue_eq_linearMap_singularValues`, [Eckart–Young](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Analysis/OperatorIdeal/ApproximationNumber/EckartYoung.lean)). The Frobenius best-approximation statement within positive semidefinite matrices, used in item 8, is not stated.

#### Statlib

No relevant declarations were found.

**Synopsis entries.** Not covered: 108.8, 108.9, 108.10.

### Graph Laplacians and eigenmaps

[Mathematical scope](SYNOPSIS108.md#graph-laplacians-and-eigenmaps).

#### Mathlib

**Unweighted graph Laplacian.** For a finite simple graph the Laplacian matrix \(L=D-A\) is defined (`SimpleGraph.lapMatrix`, `Combinatorics/SimpleGraph/LapMatrix.lean`). The quadratic-form identity \(x^{\mathsf T}Lx=\frac12\sum_{i\sim j}(x_i-x_j)^2\) and positive semidefiniteness are proved (`SimpleGraph.lapMatrix_toLinearMap₂'`, `SimpleGraph.posSemidef_lapMatrix`). A vector lies in the kernel exactly when it is constant on reachability classes (`SimpleGraph.lapMatrix_mulVec_eq_zero_iff_forall_reachable`). The dimension of the kernel equals the number of connected components (`SimpleGraph.card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix`), with a basis given by component indicators in the proof. The graphs carry no edge weights, so the general weight matrix \(W\) of the synopsis is not covered. The normalized and random-walk Laplacians, the bound of the spectrum by \(2\), and its characterization of bipartite components are not formalized.

#### TauCeti

As supporting material for item 12, Ky Fan's trace inequality and the Courant–Fischer theorem are recorded under the previous heading. Davis–Kahan and Yu–Wang–Samworth \(\sin\Theta\) bounds for unitarily invariant norms are proved ([sin Θ corollaries](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm/SinTheta/Corollaries.lean)). These are the perturbation tools of spectral embedding. The generalized eigenproblem \(Lf=\lambda Df\) and the Laplacian eigenmap characterization are not stated.

#### Statlib

No relevant declarations were found.

**Synopsis entries.** Partly covered: 108.11 (unweighted simple graphs only: quadratic form, positive semidefiniteness, and kernel dimension equal to the number of components, in Mathlib; the weighted, normalized, and random-walk versions and the bipartite criterion are absent). Not covered: 108.12.

### Fréchet means and Procrustes analysis

[Mathematical scope](SYNOPSIS108.md#fréchet-means-and-procrustes-analysis).

#### Mathlib

No Fréchet mean on a manifold, cut locus, injectivity radius, or shape space is defined. The Riemannian supporting material is recorded under the first heading.

#### TauCeti

**Strong consistency of Fréchet mean sets.** Let \(Y_0,Y_1,\dots\) be independent random points of a separable pseudometric space with law \(\mu\), and let \(\mu\) have finite \(p\)-th moment with \(1\le p<\infty\). Then almost surely, on one event that does not depend on the choice, every cluster point of every sequence of empirical Fréchet barycenters is a Fréchet barycenter of \(\mu\) (`TauCeti.isFrechetBarycenter_of_mapClusterPt_empiricalMeasure_ae`, [empirical barycenters](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/MeasureTheory/Measure/FrechetMean/Empirical.lean)). On a proper metric space, every such sequence has a subsequence converging to a barycenter of \(\mu\), and the whole sequence converges when the barycenter is unique (`TauCeti.exists_isFrechetBarycenter_tendsto_comp_empiricalMeasure_ae`, `TauCeti.tendsto_of_isFrechetBarycenter_empiricalMeasure_ae`). The empirical radii and the minimal empirical radius also converge almost surely (`TauCeti.tendsto_frechetRadius_empiricalMeasure_ae`, `TauCeti.tendsto_iInf_frechetRadius_empiricalMeasure_ae`). The selections need not be measurable. Combined with the compactness of the mean set recorded under the first heading, this is the Ziezold–Bhattacharya–Patrangenaru theorem for the exponent \(\beta=p\). The \(\varepsilon\)-neighbourhood form of the synopsis follows by a short compactness argument but is not stated. The variant with \(f\circ\rho\) on a compact space is not formalized.

**Procrustes alignment.** Ky Fan's maximum principle gives, for an endomorphism \(A\) of an \(n\)-dimensional inner product space, \(\max_Q\|\mathrm{tr}(AQ)\|=\sigma_0(A)+\dots+\sigma_{n-1}(A)\) over linear isometric automorphisms \(Q\), attained with \(\mathrm{tr}(AQ)\) real (`LinearMap.norm_trace_comp_linearIsometryEquiv_le_kyFanSum`, `LinearMap.exists_linearIsometryEquiv_trace_comp_eq_kyFanSum`, [Ky Fan](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Analysis/InnerProductSpace/KyFan.lean)). This is the rotation step of orthogonal Procrustes analysis over the full orthogonal group. For two orthonormal families, an aligned orthonormal basis of the second span minimizes \(\sum_j\|w_j-u_j\|^2\), with minimum \(2\sum_k(1-\cos\theta_k)\) in terms of principal angles (`TauCeti.exists_orthonormal_span_eq_sum_norm_sub_sq_le`, `TauCeti.two_mul_sum_one_sub_cosPrincipalAngles_le_sum_norm_sub_sq`, [Procrustes](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Analysis/InnerProductSpace/Orthonormal/Procrustes.lean)). The restriction to \(SO(m)\) with the sign of \(\lambda_m\), the scale and translation parameters, and the full and partial Procrustes distances are not formalized. Generalized Procrustes analysis is absent.

#### Statlib

No relevant declarations were found.

**Synopsis entries.** Partly covered: 108.14 (nonempty compact mean set on proper spaces, and almost-sure cluster-point and subsequence consistency of empirical barycenters, in TauCeti; the \(\varepsilon\)-neighbourhood form is not stated and the \(f\circ\rho\) variant is absent), 108.16 (the optimal orthogonal rotation via Ky Fan's principle over the full orthogonal group, in TauCeti; the \(SO(m)\) sign correction, scaling, translation, and shape distances are absent). Not covered: 108.13, 108.15, 108.17.

### Persistent homology and computational topology

[Mathematical scope](SYNOPSIS108.md#persistent-homology-and-computational-topology).

#### Mathlib

No persistence module, interval module, barcode, persistence diagram, bottleneck distance, or interleaving is defined. The categorical nerve of a category is defined (`CategoryTheory.nerve`, `AlgebraicTopology/SimplicialSet/Nerve.lean`), but not the nerve of a cover, and the nerve theorem is not proved. No Čech or Vietoris–Rips complex is defined. As supporting material, the Hausdorff distance between subsets of a metric space and its comparison with distance functions are developed (`Metric.hausdorffDist`, `Topology/MetricSpace/HausdorffDistance.lean`), and the Gromov–Hausdorff distance is recorded in [CKMA Structure 39](../lean-CKMA/STRUCTURE39.md). The reach of a set and Wasserstein distances are not defined in Mathlib.

**Probability supporting material.** The strong law of large numbers holds for pairwise independent, identically distributed, integrable random variables in a Banach space with second-countable Borel structure (`ProbabilityTheory.strong_law_ae`, `Probability/StrongLaw.lean`). The central limit theorem is proved for real random variables (`ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum`, `Probability/CentralLimitTheorem.lean`). A Banach-space strong law therefore applies to \(L^p\)-valued random elements once landscapes are defined; no central limit theorem in \(L^p\), \(p\ge2\), is available.

#### TauCeti

**Supporting algebra.** Gabriel's theorem is proved for finite connected quivers: finite representation type is equivalent to positive definiteness of the Tits form, and to the underlying graph being a simply-laced Dynkin diagram (`TauCeti.isFiniteRepType_iff_titsForm_posDef`, [Gabriel](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/RepresentationTheory/Quiver/FiniteRepType/Gabriel.lean)). A persistence module over a finite totally ordered index set is a representation of an equioriented quiver of type \(A_n\). Gabriel's theorem is therefore the natural algebraic input for interval decomposition there. The identification of the indecomposables with interval modules, and decomposition for pointwise finite-dimensional modules over \(\mathbb R\), are not formalized.

**Supporting topology.** For an open cover, the augmentation of the Čech–singular total complex onto the singular chains is a quasi-isomorphism (`TauCeti.TopCat.quasiIso_openCoverSingularTotalAugmentation`, [Čech–singular comparison](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/AlgebraicTopology/Singular/Cech/QuasiIso.lean)). With acyclic intersections this is the homological form of the nerve lemma for open covers. The nerve of a cover as a simplicial complex, the nerve theorem for closed convex sets, and any comparison of Čech and Rips complexes are not formalized.

#### Statlib

No relevant declarations were found.

The deformation-retraction statement in item 22 concerns finite nonempty noiseless samples on the manifold. Its nonemptiness convention is explicit; the theorem and sampling bound are absent.

**Synopsis entries.** Not covered: 108.18, 108.19, 108.20, 108.21, 108.22, 108.23, 108.24, 108.25.

### Persistent summaries and perturbation certificates

[Mathematical scope](SYNOPSIS108.md#persistent-summaries-and-perturbation-certificates).

#### Mathlib

**Distance functions and Hausdorff distance.** For sets \(s,t\) at finite Hausdorff distance, \(\inf\mathrm{dist}(x,t)\le\inf\mathrm{dist}(x,s)+d_H(s,t)\) for every \(x\) (`Metric.infDist_le_infDist_add_hausdorffDist`). Conversely, a uniform bound \(r\ge0\) on the distances from the points of each set to the other bounds \(d_H(s,t)\) by \(r\) (`Metric.hausdorffDist_le_of_infDist`, `Topology/MetricSpace/HausdorffDistance.lean`). Together these give \(\|d(\cdot,A)-d(\cdot,B)\|_\infty=d_H(A,B)\) for nonempty bounded sets, but the equality is not stated. The distance function to a set is \(1\)-Lipschitz (`Metric.lipschitz_infDist_pt`). Offset inclusions \(A^r\subseteq B^{r+\eta}\) and their consequences for diagrams are not stated. Persistent Betti numbers, landscapes, and the distance to a measure are not defined.

#### TauCeti

No relevant declarations were found. Wasserstein distances, needed for the distance to a measure, are recorded under 108B.

#### Statlib

No relevant declarations were found.

**Synopsis entries.** Not covered: 108.26, 108.27 (ingredients only: the two inequalities between distance functions and Hausdorff distance, in Mathlib; the stated equality, offset interleaving, and diagram stability are absent), 108.28, 108.29, 108.30.

### Simplicial homology and the persistence algorithm

[Mathematical scope](SYNOPSIS108.md#simplicial-homology-and-the-persistence-algorithm).

#### Mathlib

Abstract simplicial complexes are defined as downward-closed families of nonempty finite sets containing every singleton (`AbstractSimplicialComplex`, `AlgebraicTopology/SimplicialComplex/Basic.lean`). Geometric simplicial complexes in a real vector space are defined separately (`Geometry.SimplicialComplex`, `Analysis/Convex/SimplicialComplex/Basic.lean`). The Euler characteristic of a homological complex is defined both from its terms and from its homology, by alternating finite sums of ranks (`HomologicalComplex.eulerChar`, `HomologicalComplex.homologyEulerChar`, `Algebra/Homology/EulerCharacteristic.lean`). Mathlib does not prove that the two agree, and it has no simplicial chain complex of an abstract complex.

#### TauCeti

**Simplicial chains and Euler–Poincaré.** For a simplicial complex with linearly ordered vertices, the ordered simplicial chain complex is built over any ring, with the alternating boundary and \(\partial\partial=0\) (`TauCeti.orderedSimplicialChainComplex`, `TauCeti.OrderedSimplicialChain.boundary_boundary`, [simplicial chains](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/AlgebraicTopology/SimplicialComplex/ChainComplex.lean)). For an \(\mathbb N\)-indexed chain complex of finite-dimensional vector spaces vanishing in large degrees, the Euler characteristic of the terms equals that of the homology (`ChainComplex.eulerChar_eq_homologyEulerChar`, [Euler–Poincaré](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Algebra/Homology/EulerCharacteristic/ChainComplex.lean)). The geometric realization of an abstract simplicial complex carries a CW structure whose \(n\)-cells are the faces with \(n+1\) vertices (`TauCeti.realizationCWComplex`, [CW structure](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/AlgebraicTopology/SimplicialComplex/Realization/CWComplex/Basic.lean)). For a finite CW complex and a finite-dimensional coefficient module over a division ring, the alternating sum of the dimensions of singular homology is the dimension of the coefficients times the alternating count of cells (`TauCeti.finsum_finrank_singularHomology_of_finite_cwComplex`, [singular Euler–Poincaré](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/AlgebraicTopology/Cellular/EulerCharacteristic/Singular.lean)). The ordered simplicial homology of a complex is isomorphic to the singular homology of its realization, over any coefficient ring (`TauCeti.orderedSimplicialHomologyIsoSingularHomology`, [simplicial and singular homology](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/AlgebraicTopology/SimplicialComplex/Realization/CWComplex/OrderedChainComplex.lean)). For a complex with finitely many faces, the Euler characteristic of the realization, and of every space it triangulates, is the alternating count of faces (`AbstractSimplicialComplex.eulerChar_realization`, `AbstractSimplicialComplex.eulerChar_eq_finsum_of_homeomorph`, [simplicial Euler characteristic](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/AlgebraicTopology/SimplicialComplex/Realization/CWComplex/EulerCharacteristic.lean)). For a space of finite CW type the Euler characteristic is the alternating sum of the dimensions of singular homology over any division ring, and it is a homotopy invariant (`TauCeti.eulerChar_eq_finsum_finrank_singularHomology`, `ContinuousMap.HomotopyEquiv.eulerChar_eq`, [finite CW type](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/AlgebraicTopology/Cellular/EulerCharacteristic/FiniteCWType.lean)). Together these give the Euler–Poincaré formula for a finite simplicial complex, with field-independence and homotopy invariance of \(\chi\), by combining these identities, but the simplicial statement with simplicial Betti numbers is not stated as one theorem. The positive/negative dichotomy for adding a simplex is not stated.

**Morse supporting material.** The Morse lemma (Morse–Palais) is proved for \(C^{n+2}\) functions on Banach spaces (`TauCeti.IsNondegenerateCriticalPoint.exists_morse_chart`, [Morse lemma](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Analysis/Calculus/Morse/NormalForm.lean)), and the Morse index is defined ([Morse index](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Analysis/Calculus/Morse/Index.lean)). The file named `Morse/Persistence.lean` concerns persistence of nondegenerate critical points under \(C^2\) perturbation, not persistent homology. Cell attachment at critical values and sublevel-set persistence are not formalized.

No boundary-matrix reduction, persistence pairing, minimum spanning tree, Kruskal's algorithm, or single-linkage clustering was found in Mathlib or TauCeti.

#### Statlib

No relevant declarations were found.

**Synopsis entries.** Not covered: 108.31 (ingredients only: in TauCeti: the simplicial chain complex and its identification with singular homology of the realization, the algebraic Euler–Poincaré identity, the Euler characteristic of a finite realization as the alternating face count, and singular Euler–Poincaré over any division ring with homotopy invariance; the simplicial formula is not assembled, and the positive/negative simplex dichotomy is absent), 108.32, 108.33, 108.34.

### Stability and inference for geometric filtrations

[Mathematical scope](SYNOPSIS108.md#stability-and-inference-for-geometric-filtrations).

#### Mathlib

The Gromov–Hausdorff distance between nonempty compact metric spaces is defined. It is at most the Hausdorff distance of any isometric embeddings into a common space (`GromovHausdorff.ghDist`, `GromovHausdorff.ghDist_le_hausdorffDist`, `Topology/MetricSpace/GromovHausdorff.lean`); see [CKMA Structure 39](../lean-CKMA/STRUCTURE39.md). The characterization by distortion of correspondences is not stated. No Rips filtration, \(q\)-tameness, weak feature size, critical point of a distance function, or standard measure is defined.

#### TauCeti

No relevant declarations were found.

#### Statlib

No relevant declarations were found.

**Synopsis entries.** Not covered: 108.35, 108.36, 108.37, 108.38, 108.39.

<a id="structure-108b"></a>

## 108B. Optimal Transport and Kernel Discrepancies

[Mathematical scope](SYNOPSIS108.md#synopsis-108b).

The analytic optimal-transport theory of [CKMA Structure 39](../lean-CKMA/STRUCTURE39.md) is assumed. It covers couplings, existence, Kantorovich and Kantorovich–Rubinstein duality, Wasserstein spaces, Brenier's theorem, geodesics, and entropic transport, all in TauCeti. Mathlib and Statlib contain none of it. Its pinned links refer to an earlier TauCeti revision; the declarations cited below were checked at the present one. Statistical theorems are mostly absent. The exceptions are a substantial TauCeti theory of Wasserstein barycenters, Gaussian and one-dimensional explicit formulas, Gromov–Wasserstein distances, the Sinkhorn divergence, the comparison of Wasserstein and weak convergence, and kernel mean embeddings with universal kernels. Statlib contributes only integral forms of the total variation distance.

### Optimal transport and Wasserstein statistics

[Mathematical scope](SYNOPSIS108.md#optimal-transport-and-wasserstein-statistics).

#### Mathlib

No Wasserstein distance is defined. The Lévy–Prokhorov metric and Prokhorov's theorem are recorded in [CKMA Structure 39](../lean-CKMA/STRUCTURE39.md).

#### TauCeti

**Empirical measures.** For independent random points of a separable pseudometric space with law \(\mu\) of finite \(p\)-th moment, \(0<p<\infty\), the empirical measures converge to \(\mu\) in \(W_p\) almost surely (`TauCeti.tendsto_wassersteinEDist_empiricalMeasure_ae`, [empirical measures](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/MeasureTheory/OptimalTransport/Wasserstein/Empirical.lean)). No rate of convergence is proved, and the Fournier–Guillin bounds of item 40 are absent.

**Existence and uniqueness of barycenters.** On a proper metric space and for \(1\le p<\infty\), every finitely supported law \(\sum_jw_j\delta_{\mu_j}\) on \(\mathcal P_p(X)\), with weights summing to one, has a \(p\)-Fréchet barycenter in \(\mathcal P_p(X)\), a minimizer of \(\nu\mapsto\sum_jw_jW_p^p(\nu,\mu_j)\) (`TauCeti.WassersteinSpace.exists_isFrechetBarycenter_sum_smul_dirac`, [multi-marginal barycenters](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/MeasureTheory/OptimalTransport/MultiMarginal/Barycenter.lean)). More generally, every law of finite \(p\)-th moment on \(\mathcal P_p(X)\) has a barycenter (Le Gouic–Loubes; `TauCeti.WassersteinSpace.exists_isFrechetBarycenter`, [population barycenters](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/MeasureTheory/OptimalTransport/Wasserstein/PopulationBarycenter.lean)). On a finite-dimensional real inner product space, the quadratic barycenter of finitely many laws in \(\mathcal P_2\) is unique as soon as one law with positive weight is absolutely continuous with respect to an additive Haar measure (`TauCeti.WassersteinSpace.subsingleton_frechetBarycenters_two_sum_smul_dirac`, [Euclidean uniqueness](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/MeasureTheory/OptimalTransport/Wasserstein/Barycenter/Uniqueness/Euclidean.lean)). The same holds for population laws charging the absolutely continuous measures (`TauCeti.WassersteinSpace.subsingleton_frechetBarycenters_two`). Together with existence on the proper space \(\mathbb R^d\), this is item 41.

**Stability of transport maps (supporting).** Graph plans of maps converge weakly exactly when the maps converge in measure (`TauCeti.tendsto_map_prodMk_self_iff_tendstoInMeasure`, [graph-plan convergence](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/MeasureTheory/OptimalTransport/GraphPlan/Convergence.lean)). The primal transport problem is stable under varying marginals and costs, given explicit liminf and recovery hypotheses ([stability](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/MeasureTheory/OptimalTransport/Stability.lean)). These are the ingredients of item 42, but the \(L^2(\mu)\) convergence of Brenier maps is not stated.

**Gromov–Wasserstein distance.** For measured kernels \((X,\mu,\omega_X)\) with values in an extended metric space, the \(p\)-distortion of a coupling and the \(p\)-Gromov–Wasserstein distance are defined, without the factor \(\frac12\) (`TauCeti.gromovWassersteinDistortion`, `TauCeti.gromovWassersteinEDist`, [Gromov–Wasserstein](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/MeasureTheory/OptimalTransport/GromovWasserstein/Basic.lean)). It is an extended pseudodistance: symmetric, vanishing on a kernel and itself, and satisfying the triangle inequality for \(1\le p\) through a standard Borel middle carrier (`TauCeti.gromovWassersteinEDist_triangle`). For probability measures on standard Borel carriers and a.e. strongly measurable kernels, the distance vanishes exactly when the kernels are weakly isomorphic, that is, identified almost everywhere by some coupling (`TauCeti.gromovWassersteinEDist_eq_zero_iff`, `TauCeti.AreWeaklyIsomorphicKernels`, [zero distance](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/MeasureTheory/OptimalTransport/GromovWasserstein/Zero.lean)). Weak isomorphism leaves the distance to a third kernel unchanged (`TauCeti.AreWeaklyIsomorphicKernels.gromovWassersteinEDist_congr_left`). For \(1\le p\), the measured kernels of finite \(p\)-size on standard Borel probability carriers, modulo weak isomorphism, form a metric space, with the coupling formula as its extended distance (`TauCeti.GromovWassersteinSpace`, [Gromov–Wasserstein space](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/MeasureTheory/OptimalTransport/GromovWasserstein/Space.lean)); it is complete exactly when the value space is ([completeness](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/MeasureTheory/OptimalTransport/GromovWasserstein/Complete.lean), `TauCeti.GromovWassersteinSpace.completeSpace_iff`). For compact metric probability spaces, the upgrade from weak isomorphism to a measure-preserving isometry of the supports is not stated.

**Sinkhorn divergence.** For a cost \(c:X\times X\to[0,\infty]\) and \(\varepsilon\ge0\), the debiased divergence \(S_\varepsilon(\mu,\nu)=\mathop{\mathrm{OT}}_\varepsilon(\mu,\nu)-\frac12\mathop{\mathrm{OT}}_\varepsilon(\mu,\mu)-\frac12\mathop{\mathrm{OT}}_\varepsilon(\nu,\nu)\) is defined as a real number and vanishes on the diagonal (`TauCeti.sinkhornDivergence`, `TauCeti.sinkhornDivergence_self`, [Sinkhorn divergence](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/MeasureTheory/OptimalTransport/Entropic/SinkhornDivergence.lean)). Let \(X\) be compact, \(c\) measurable and bounded, \(\varepsilon>0\), and let the Gibbs kernel \(e^{-c/\varepsilon}\) be jointly continuous and positive definite in the kernel sense. Then \(S_\varepsilon(\mu,\nu)\ge0\) for probability measures (`TauCeti.sinkhornDivergence_nonneg`). If moreover \(X\) carries its Borel σ-algebra, closed sets are approximable from outside (for instance \(X\) compact metrizable), and the Gibbs kernel is universal, then \(S_\varepsilon(\mu,\nu)=0\) exactly when \(\mu=\nu\) (`TauCeti.sinkhornDivergence_eq_zero_iff`). The Gibbs kernel of a continuous bounded cost is continuous (`TauCeti.continuous_entropicGibbsKernel`, [entropic duality](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/MeasureTheory/OptimalTransport/Entropic/Duality.lean)). The proof runs through the symmetric Schrödinger potentials of the self-transport problems (`TauCeti.exists_entropicDualValue_self_eq`, [symmetric potentials](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/MeasureTheory/OptimalTransport/Entropic/Symmetric.lean)) and the injectivity of universal mean embeddings, recorded under the kernel headings below. Costs are nonnegative; a real-valued Lipschitz cost on a compact space becomes one after adding a constant, which leaves \(S_\varepsilon\) unchanged, but this reduction is not stated. The metrization of weak convergence by \(S_\varepsilon\) is not formalized.

#### Statlib

No relevant declarations were found.

**Synopsis entries.** Covered: 108.41 (TauCeti). Partly covered: 108.44 (nonnegativity and definiteness for bounded nonnegative measurable costs on compact spaces whose Gibbs kernel is continuous, positive definite, and universal, in TauCeti; real-valued costs and the metrization of weak convergence are absent). Not covered: 108.40, 108.42, 108.43 (ingredients only: Gromov–Wasserstein as an extended pseudodistance, vanishing exactly on weakly isomorphic measured kernels, and the metric space of weak-isomorphism classes, in TauCeti; isometry of supports for compact metric measure spaces is not derived).

### Explicit geometries and empirical inference

[Mathematical scope](SYNOPSIS108.md#explicit-geometries-and-empirical-inference).

#### Mathlib

As supporting material for item 48, two finite measures on a complete second-countable real inner product space with the same characteristic function are equal (`MeasureTheory.Measure.ext_of_charFun`, `MeasureTheory/Measure/CharacteristicFunction/Basic.lean`). The Cramér–Wold theorem reduces convergence in distribution in a finite-dimensional inner product space to its scalar projections (`tendstoInDistribution_iff_tendstoInDistribution_inner`, `Probability/CramerWold.lean`). No sliced Wasserstein distance, Brownian bridge limit of empirical quantile processes, or Gaussian transport formula is present.

#### TauCeti

**One-dimensional barycenters and the quantile isometry.** For probability laws \(\mu_i\) on \(\mathbb R\) and weights summing to one, the law whose quantile function is \(\sum_iw_iF_{\mu_i}^{-1}\) minimizes \(\nu\mapsto\sum_iw_iW_2^2(\nu,\mu_i)\), and it is the only minimizer when the minimum is finite (`TauCeti.quantile_quantileBarycenter_ae`, `TauCeti.sum_mul_wassersteinEDist_sq_le_iff_eq_quantileBarycenter`, [quantile barycenters](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/MeasureTheory/OptimalTransport/Wasserstein/Barycenter/Basic.lean)). In \(\mathcal P_2(\mathbb R)\) the Fréchet barycenter of finitely many laws exists, is unique, and has the averaged quantile function (`TauCeti.existsUnique_isFrechetBarycenter_two`). For every \(1\le p\le\infty\), the quantile map is an isometry of \(\mathcal P_p(\mathbb R)\) into \(L^p(0,1)\), and its image is the set of classes of nondecreasing functions (`TauCeti.WassersteinSpace.isometry_quantileLp`, `TauCeti.WassersteinSpace.range_quantileLp`, [quantile isometry](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/MeasureTheory/OptimalTransport/Wasserstein/Quantile/Isometry.lean)). Hence \(\mathcal P_2(\mathbb R)\) is CAT(0) (`TauCeti.WassersteinSpace.instIsCATZeroSpace`). Every law of finite second moment on \(\mathcal P_2(\mathbb R)\) then has exactly one quadratic barycenter, with no absolute continuity (`TauCeti.WassersteinSpace.existsUnique_isFrechetBarycenter_real`, [barycenters on the line](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/MeasureTheory/OptimalTransport/Wasserstein/Barycenter/Uniqueness/Real.lean)). The identification of that population barycenter's quantile function with \(\mathbb E F_\Lambda^{-1}\) is not stated.

**Gaussian transport.** On a Euclidean space, let the source covariance \(S_1\) be positive definite and the target covariance \(S_2\) positive semidefinite. The positive affine map between \(N(m_1,S_1)\) and \(N(m_2,S_2)\) is optimal for the quadratic cost, and \(W_2^2\) is given by the Bures formula of item 46 (`TauCeti.Probability.isKantorovichOptimalTransportMap_affineGeometricMean`, `TauCeti.wassersteinEDist_two_multivariateGaussian_rpow_two`, [Gaussian distance](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/MeasureTheory/OptimalTransport/Wasserstein/Gaussian/Basic.lean)). Along the optimal affine map, the interpolating laws are Gaussian and form a \(W_2\) geodesic. The law at time \(t\) is therefore a Fréchet barycenter of the two input laws with weights \(1-t,t\) (`TauCeti.Probability.exists_isGeodesicSegment_multivariateGaussian`, `TauCeti.Probability.isFrechetBarycenter_two_multivariateGaussian`, [Gaussian barycenters](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/MeasureTheory/OptimalTransport/Wasserstein/Gaussian/Barycenter.lean)). For finitely many Gaussian laws \(N(m_j,C_j)\) with positive semidefinite \(C_j\) and weights \(w_j\) summing to one, if a positive definite \(S\) solves \(S=\sum_jw_j(S^{1/2}C_jS^{1/2})^{1/2}\), then \(N(\sum_jw_jm_j,S)\) is a quadratic barycenter, and it is the only one when some \(C_j\) with positive weight is positive definite (`TauCeti.Probability.isFrechetBarycenter_sum_smul_dirac_multivariateGaussian`, `TauCeti.Probability.frechetBarycenters_sum_smul_dirac_multivariateGaussian`, [Gaussian fixed point](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/MeasureTheory/OptimalTransport/Wasserstein/Gaussian/FixedPoint.lean)). This rests on a Gaussian lower bound for the barycentric cost of arbitrary laws with finite second moments (`TauCeti.sum_mul_ofReal_gaussianWassersteinSq_le`). The existence and uniqueness of a positive definite solution of the fixed-point equation, the commuting case, and the formula with both covariances singular are not formalized.

**Consistency of empirical barycenters.** Let \(X\) be a proper Polish metric space, \(1\le p<\infty\), and let \(Y_0,Y_1,\dots\) be independent random laws in \(\mathcal P_p(X)\) with population law \(Q\) of finite \(p\)-th moment. Almost surely, every sequence of empirical Wasserstein barycenters has compact closure, and every subsequence of it has a further subsequence converging to a population barycenter. When the population barycenter is unique, every such sequence converges to it (`TauCeti.WassersteinSpace.isCompact_closure_range_of_isFrechetBarycenter_empiricalMeasure_ae`, `TauCeti.WassersteinSpace.tendsto_of_isFrechetBarycenter_empiricalMeasure_ae`, [empirical Wasserstein barycenters](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/MeasureTheory/OptimalTransport/Wasserstein/Barycenter/Empirical.lean)). Random measures supported in a common compact subset of \(\mathbb R^d\) satisfy these hypotheses, so this covers item 49 without measurability of the selected barycenters.

#### Statlib

No relevant declarations were found.

**Synopsis entries.** Covered: 108.49 (TauCeti). Partly covered: 108.45 (finite barycenters on the line with averaged quantile function, the quantile isometry onto nondecreasing classes, and existence and uniqueness of population barycenters, in TauCeti; the population quantile formula \(\mathbb E F_\Lambda^{-1}\) is not stated), 108.46 (Bures formula and optimal affine map with positive definite source, and the Gaussian barycenter of finitely many laws given a positive definite solution of the fixed-point equation, unique when one input with positive weight is nondegenerate, in TauCeti; doubly singular covariances, the existence and uniqueness of the fixed point, and the commuting case are absent). Not covered: 108.47, 108.48.

### Minimax limits, smoothness, and smoothing

[Mathematical scope](SYNOPSIS108.md#minimax-limits-smoothness-and-smoothing).

#### Mathlib

No relevant declarations were found.

#### TauCeti

The \(N\)-point quantization error of a law is defined as the infimum of the Wasserstein distances to laws carried by at most \(N\) points. It is reduced to an infimum over finite sets of \(\|\inf\mathrm{dist}(\cdot,s)\|_{L^p(\mu)}\), and on a proper space a best quantizer exists (`TauCeti.wassersteinQuantizationError`, `TauCeti.wassersteinQuantizationError_eq_iInf_eLpNorm_infEDist`, `TauCeti.exists_wassersteinEDist_eq_wassersteinQuantizationError`, [quantization](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/MeasureTheory/OptimalTransport/Wasserstein/Quantization.lean)). This is the right object for the first lower bound of item 50, but no rate of decay, and in particular no bound \(n^{-1/d}/(108d)\) for the uniform law, is proved. Convolution with a common probability law does not increase \(W_p\) (`TauCeti.wassersteinEDist_conv_right_le`, [convolution](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/MeasureTheory/OptimalTransport/Wasserstein/Convolution.lean)). This is the contraction underlying smoothed Wasserstein distances. The smoothed distance itself, its metric property, and its parametric rate are not formalized. No minimax lower bound, Sobolev class on the torus, or dual Lipschitz norm on signed measures appears.

#### Statlib

No relevant declarations were found.

**Synopsis entries.** Not covered: 108.50, 108.51.

### Estimation of transport maps

[Mathematical scope](SYNOPSIS108.md#estimation-of-transport-maps).

#### Mathlib

No relevant declarations were found.

#### TauCeti

As supporting material, Brenier's theorem gives, for the cost \(\|x-y\|^2/2\) on a finite-dimensional real inner product space, a source law absolutely continuous with respect to Haar measure, and finite optimal cost, an optimal plan that is the graph of \(\nabla u\) for a proper lower-semicontinuous convex \(u\) (`TauCeti.exists_isKantorovichOptimalTransportMap_gradient`, [Brenier](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/MeasureTheory/OptimalTransport/Brenier.lean)). Kantorovich duality and Rockafellar's theorem are recorded in [CKMA Structure 39](../lean-CKMA/STRUCTURE39.md). The semidual functional \(\int\phi\,d\mu+\int\phi^*\,d\nu\), its strong-convexity stability bounds, and all rates of transport-map estimation are absent.

#### Statlib

No relevant declarations were found.

The rate statement of item 53 uses ambient smoothness and Hessian bounds on the closed conjugacy ball, a source support separated from its boundary, and constants allowed to depend on that margin. None of the pinned libraries states these statistical rates.

**Synopsis entries.** Not covered: 108.52, 108.53.

### Entropic transport: duality and statistical rates

[Mathematical scope](SYNOPSIS108.md#entropic-transport-duality-and-statistical-rates).

#### Mathlib

No relevant declarations were found. Relative entropy is Mathlib's `InformationTheory.klDiv` (`InformationTheory/KullbackLeibler/Basic.lean`), on which TauCeti's entropic transport is built.

#### TauCeti

**Entropic duality.** The entropic dual value of potentials \(\varphi,\psi\) is \(\int\varphi\,d\mu+\int\psi\,d\nu-\varepsilon\int(e^{(\varphi(x)+\psi(y)-c(x,y))/\varepsilon}-1)\,d(\mu\otimes\nu)\) (`TauCeti.entropicDualValue`, [entropic duality](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/MeasureTheory/OptimalTransport/Entropic/Duality.lean)). Weak duality holds for every coupling (`TauCeti.ofReal_entropicDualValue_le_entropicTransportCost`). Complementary slackness is proved: a coupling of finite regularized cost and a pair of potentials have the same value exactly when the coupling has density \(e^{(\varphi\oplus\psi-c)/\varepsilon}\) against \(\mu\otimes\nu\) (`TauCeti.IsCoupling.entropicDualValue_eq_toReal_lintegral_add_mul_klDiv_iff`). This contains the converse in item 54. For a bounded measurable cost and probability measures, strong duality holds with attainment by bounded measurable potentials, unique up to an additive constant (`TauCeti.exists_entropicDualValue_eq_toReal_entropicTransportCost`, `TauCeti.isGreatest_entropicDualValue_integrable`, `TauCeti.exists_ae_eq_add_const_of_entropicDualValue_eq_toReal_entropicTransportCost`). The quadratic cost on compactly supported laws is bounded on the product of the supports, so this applies after restriction to the supports. The potentials are found as fixed points of the Sinkhorn sweep, whose half-steps are the exact partial maximizations \(\psi=-\varepsilon\log\int e^{(\varphi-c)/\varepsilon}\,d\mu\) (`TauCeti.exists_isCoupling_withDensity_exp_add`, [Schrödinger system](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/MeasureTheory/OptimalTransport/Entropic/SchroedingerSystem.lean)). The entropic map \(b_\varepsilon\), its gradient representation, and its identification as an \(L^2(\pi_\varepsilon)\) projection are not formalized.

**Entropic barycenters (supporting).** Entropic Wasserstein barycenter costs are defined, exist on compact spaces, and \(\Gamma\)-converge to the Wasserstein barycenter cost as \(\varepsilon\downarrow0\) (`TauCeti.entropicBarycenterCost`, `TauCeti.exists_isMinOn_entropicBarycenterCost`, [entropic barycenters](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/MeasureTheory/OptimalTransport/Entropic/Barycenter.lean)). No sample-complexity bound for entropic transport is proved.

**Discrete Sinkhorn iteration (supporting).** For a matrix with positive entries and positive marginals, any two Sinkhorn half-steps with the same kernel lie within its projective diameter of each other in Hilbert's projective metric, whatever their inputs. This gives explicit linear rates for the iteration in terms of that diameter (`Matrix.hilbertProjectiveDist_sinkhornUpdate_le_projectiveDiameter`, [Sinkhorn rates](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Data/Matrix/Sinkhorn/Rate.lean)).

#### Statlib

No relevant declarations were found.

**Synopsis entries.** Partly covered: 108.54 (dual formula, weak and strong duality with attainment for bounded costs, the Gibbs-density characterization of optimality, and Sinkhorn half-steps, in TauCeti; the entropic map and its gradient form are absent). Not covered: 108.55.

### Semidiscrete transport

[Mathematical scope](SYNOPSIS108.md#semidiscrete-transport).

#### Mathlib

No relevant declarations were found.

#### TauCeti

No Laguerre cell, power diagram, or semidiscrete dual function was found. The general \(c\)-transform and dual-attainment theory of [CKMA Structure 39](../lean-CKMA/STRUCTURE39.md) is the natural starting point.

#### Statlib

No relevant declarations were found.

**Synopsis entries.** Not covered: 108.56.

### Tangent space, linearization, and Fréchet means

[Mathematical scope](SYNOPSIS108.md#tangent-space-linearization-and-fréchet-means).

#### Mathlib

No relevant declarations were found.

#### TauCeti

**Tangent space.** On a finite-dimensional real inner product space, the tangent space at \(\mu\) is defined as the closure in \(L^2(\mu;E)\) of the gradients of smooth compactly supported functions (`TauCeti.wassersteinTangentSpace`, [tangent space](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/MeasureTheory/OptimalTransport/Wasserstein/TangentSpace.lean)). Its orthogonal complement is described as the divergence-free fields, and the projection onto it is the least-norm field of given divergence. The equality with the closure of the cone \(\{s(t_\gamma^\mu-\mathrm{id})\}\) is not proved.

**Linearization.** For maps \(f,g\) and a coupling \(\pi\), \(W_p(f_\#\mu,g_\#\nu)\le\|d(f(x),g(y))\|_{L^p(\pi)}\) (`TauCeti.wassersteinEDist_map_le_eLpNorm`, [pushforwards](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/MeasureTheory/OptimalTransport/Wasserstein/Pushforward.lean)). With the diagonal coupling of \(\gamma\) this gives \(W_2(\mu,\nu)\le\|t_\gamma^\mu-t_\gamma^\nu\|_{L^2(\gamma)}\). Brenier's theorem identifies \(W_2(\gamma,\mu)^2\) with \(\int\|t_\gamma^\mu-\mathrm{id}\|^2\,d\gamma\). On a separable Banach space, the laws of \((1-t)x+ty\) under an optimal coupling form a \(W_2\) geodesic (`TauCeti.WassersteinSpace.exists_isGeodesicSegment_map_smul_add_smul`, [geodesics](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/MeasureTheory/OptimalTransport/Wasserstein/Geodesic/Basic.lean)). The one-dimensional isometry recorded above is the compatible case on \(\mathbb R\). The log and exponential maps, compatible families, the isometric embedding on them, and the Gaussian compatibility criterion are not formalized.

**Subdifferential (supporting).** On \(\mathcal P_2\) of a separable Hilbert space, the Fréchet subdifferential of an energy is defined through all optimal couplings. It is a closed convex subset of \(L^2(\mu;E)\), with the global characterization for geodesically \(m\)-convex energies (`TauCeti.wassersteinSubdifferential`, [subdifferential](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/MeasureTheory/OptimalTransport/Wasserstein/Subdifferential.lean)). The gradient of the barycenter functional \(F\), the Karcher-mean equation, the Agueh–Carlier sufficiency criterion, and the fixed-point (Procrustes) iteration are not formalized.

#### Statlib

No relevant declarations were found.

**Synopsis entries.** Partly covered: 108.57 (the tangent space as a closure of gradients, the coupling bound \(W_2(\mu,\nu)\le\|t_\gamma^\mu-t_\gamma^\nu\|_{L^2(\gamma)}\) via pushforwards, displacement geodesics, and the one-dimensional isometry, in TauCeti; log and exponential maps, compatibility, and the isometric embedding are absent). Not covered: 108.58, 108.59.

### Kernel mean embeddings and integral probability metrics

[Mathematical scope](SYNOPSIS108.md#kernel-mean-embeddings-and-integral-probability-metrics).

#### Mathlib

**Reproducing-kernel Hilbert spaces.** Vector-valued reproducing-kernel Hilbert spaces are defined as a class, with evaluation operators and kernel functions (`RKHS`, `RKHS.kerFun`, `Analysis/InnerProductSpace/Reproducing.lean`). Kernel functions are dense, and the kernel is positive semidefinite. Joint continuity of the kernel, continuity of evaluation, and continuity of the kernel functions are equivalent (`RKHS.continuous_kernel_tfae`). The space constructed from a positive semidefinite kernel has that kernel (Moore's theorem, `RKHS.OfKernel`, `RKHS.kernel_ofKernel`). This is supporting material; no integral of the feature map against a measure is taken in Mathlib.

#### TauCeti

**Kernel mean embeddings.** For a real positive semidefinite kernel \(k\), the canonical feature map into its Kolmogorov space is built from Mathlib's `RKHS.OfKernel` (`Matrix.PosSemidef.kolmogorovFeature`, [Kolmogorov decomposition](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Analysis/PositiveDefinite/Kernel/Kolmogorov.lean)). The kernel mean embedding of a measure is the Bochner integral of the feature map (`Matrix.PosSemidef.kernelMeanEmbedding`, [mean embeddings](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Analysis/PositiveDefinite/Kernel/MeanEmbedding.lean)). When the feature map is integrable, \(\langle m_\mu,m_\nu\rangle=\iint k\,d\mu\,d\nu\), so \(\|m_\mu-m_\nu\|^2=\iint k\,d\mu\,d\mu-2\iint k\,d\mu\,d\nu+\iint k\,d\nu\,d\nu\) (`Matrix.PosSemidef.inner_kernelMeanEmbedding`, `Matrix.PosSemidef.norm_kernelMeanEmbedding_sub_sq`). This is the expectation formula for \(\mathrm{MMD}^2\) in item 60. On a compact space, the feature map of a jointly continuous kernel is integrable for every finite measure (`Matrix.PosSemidef.integrable_kolmogorovFeature`). The supremum formula over the unit ball is not stated.

**Positive-definite functions (supporting).** Bochner's theorem is proved on finite-dimensional real inner product spaces: a function is continuous and positive definite exactly when it is the Fourier transform of a unique finite Borel measure (`TauCeti.bochner`, `TauCeti.bochnerMeasure`, [Bochner](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Analysis/Bochner/BochnerTheorem.lean)). Versions on locally compact abelian groups are also proved. The Gaussian kernel \(e^{-c\|a-b\|^2}\) is positive definite for \(c\ge0\) (`TauCeti.posSemidef_cexp_neg_mul_sq_norm`, [Gaussian](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Analysis/Bochner/Gaussian/Basic.lean)). The characteristic property of the Gaussian and Laplace kernels and the full-support spectral criterion are not proved. Energy distance, distance covariance, and the Hilbert–Schmidt independence criterion are not defined.

#### Statlib

No relevant declarations were found.

**Synopsis entries.** Partly covered: 108.60 (kernel mean embedding and the double-integral formula for \(\mathrm{MMD}^2\), in TauCeti; the unit-ball supremum formula, characteristic Gaussian and Laplace kernels, and the spectral criterion are absent). Not covered: 108.61, 108.62, 108.63.

### Kernel estimation, witnesses, and test calibration

[Mathematical scope](SYNOPSIS108.md#kernel-estimation-witnesses-and-test-calibration).

#### Mathlib

As supporting material, Hoeffding's inequality for sums of independent sub-Gaussian real random variables and Hoeffding's lemma for bounded centred variables are proved (`ProbabilityTheory.measure_sum_ge_le_of_iIndepFun`, `ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`, `Probability/Moments/SubGaussian.lean`). No Hilbert-space-valued concentration inequality is stated. No \(U\)-statistic, degenerate \(U\)-statistic limit, or Gram-matrix statistic is defined.

#### TauCeti

McDiarmid's bounded-differences inequality is proved in sub-Gaussian moment-generating-function form (`TauCeti.Probability.hasSubgaussianMGF_of_bounded_differences`, [McDiarmid](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/McDiarmid.lean)). It would give the high-probability part of item 64 from the norm \(\|\Phi(\mu_n)-\Phi(\mu)\|\), but that application is not made. Independent identically distributed sequences are exchangeable (`TauCeti.Probability.Exchangeable.of_iIndepFun_identDistrib`, [i.i.d. sequences](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/Exchangeability/IID.lean)). This is the symmetry input of permutation tests, but no permutation test and no level guarantee is formalized.

#### Statlib

No relevant declarations were found.

**Synopsis entries.** Not covered: 108.64, 108.65, 108.66, 108.67.

### Characteristic kernels and comparison of metrics

[Mathematical scope](SYNOPSIS108.md#characteristic-kernels-and-comparison-of-metrics).

#### Mathlib

The Lévy–Prokhorov metric induces the weak topology on probability measures on a separable pseudometric Borel space (`MeasureTheory.LevyProkhorov.probabilityMeasureHomeomorph`, `MeasureTheory/Measure/LevyProkhorovMetric.lean`). Prokhorov's theorem gives compactness of the closure of a tight set of probability measures (`isCompact_closure_of_isTightMeasureSet`, `MeasureTheory/Measure/Prokhorov.lean`); see [CKMA Structure 06](../lean-CKMA/STRUCTURE06.md). These are the inputs of the tightness half of item 70. No maximum mean discrepancy is defined.

#### TauCeti

**Universal kernels are characteristic.** A kernel is universal when its continuous sections span a dense subspace of \(C(X)\) (`TauCeti.IsUniversalKernel`, [universal kernels](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Analysis/PositiveDefinite/Kernel/Universal.lean)). On a compact metrizable space, finite Borel measures with the same integrals of the sections of a universal kernel are equal (`TauCeti.IsUniversalKernel.ext_of_forall_integral_eq`). For a jointly continuous universal positive semidefinite kernel, the mean embedding is injective on finite Borel measures (`Matrix.PosSemidef.kernelMeanEmbedding_inj`, [mean embeddings](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Analysis/PositiveDefinite/Kernel/MeanEmbedding.lean)). This is part (b) of item 68. Integral strict positive definiteness, the translation-invariant spectral criterion, and the polynomial-kernel example are not formalized.

**Comparison of metrics (supporting).** Kantorovich–Rubinstein duality for \(W_1\) and a bounded-Lipschitz variant with attainment are proved (`TauCeti.wassersteinEDist_one_eq_iSup`, `TauCeti.isGreatest_ofReal_integral_sub_integral_boundedLipschitz`, [Kantorovich–Rubinstein](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/MeasureTheory/OptimalTransport/Wasserstein/KantorovichRubinstein.lean)). The bounded-Lipschitz variant uses separate bounds \(\sup|f|\le R\) and \(\mathop{\mathrm{Lip}}f\le1\), the maximum-norm convention, not the sum norm \(\|f\|_{\mathrm{BL}}\) of the Dudley metric. For \(1\le p\le\infty\), a \(W_p\) distance below \(\varepsilon^2\) bounds the Lévy–Prokhorov distance by \(\varepsilon\). On a second-countable standard Borel pseudometric space, convergence in \(W_p\), in particular in \(W_1\), therefore implies weak convergence, both on the finite-moment Wasserstein space and on every component of laws at finite distance from a fixed one (`TauCeti.levyProkhorovEDist_le_of_wassersteinEDist_lt_mul_self`, `TauCeti.WassersteinSpace.continuous_toProbabilityMeasure`, `TauCeti.WassersteinComponent.continuous_toProbabilityMeasure`, [weak convergence](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/MeasureTheory/OptimalTransport/Wasserstein/WeakConvergence.lean)). Weak convergence is equivalent to convergence of the transport cost for the truncated distance \(\min(d,2R)\), \(R>0\), and on a Polish space to uniform convergence of integrals over the \(1\)-Lipschitz functions bounded by \(R\) (`TauCeti.tendsto_probabilityMeasure_iff_transportCost_truncated_dist`, `TauCeti.tendsto_probabilityMeasure_iff_iSup_abs_integral_sub_integral_boundedLipschitz`, [bounded-Lipschitz transport](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/MeasureTheory/OptimalTransport/Wasserstein/BoundedLipschitz.lean)); this is again the maximum-norm class, not the Dudley metric. The inequalities between MMD, \(W_1\), \(d_{\mathrm{TV}}\), and the Dudley metric, the metrization of weak convergence by the Dudley metric and by MMD, and the counterexamples of item 69 are not stated.

#### Statlib

For finite measures and measurable \(f\) with \(|f|\le1\), \(\int f\,d\mu-\int f\,d\nu\le\) `tvDist μ ν`, and `tvDist μ ν` is the supremum of these differences ([integral forms of total variation](https://github.com/stat-lib/statlib/blob/eeaac0283690efaa60c31115400cf561836baeb9/Statlib/Divergence/TotalVariation/Integral.lean), `ProbabilityTheory.integral_sub_integral_le_tvDist`, `ProbabilityTheory.tvDist_eq_iSup_integral_sub`). For probability laws `tvDist` is \(2d_{\mathrm{TV}}\), and every \(f\) with \(\|f\|_{\mathrm{BL}}\le1\) satisfies \(|f|\le1\), so taking the supremum gives \(\beta\le2d_{\mathrm{TV}}\) of item 69; that inequality is not stated.

**Synopsis entries.** Partly covered: 108.68 (part (b), universal kernels on compact metrizable spaces are characteristic, in TauCeti; parts (a), (c), (d) and the general criterion are absent), 108.69 (convergence in \(W_1\), and in every \(W_p\) with \(p\ge1\), implies weak convergence on second-countable standard Borel spaces, in TauCeti; the MMD, Dudley, and total-variation inequalities, the metrization by the Dudley metric, and the examples are not stated). Not covered: 108.70.

### Kernel Stein discrepancies

[Mathematical scope](SYNOPSIS108.md#kernel-stein-discrepancies).

#### Mathlib

No relevant declarations were found.

#### TauCeti

No Stein operator, Stein kernel, or kernel Stein discrepancy was found.

#### Statlib

No relevant declarations were found.

**Synopsis entries.** Not covered: 108.71, 108.72.

### Conditional embeddings and random features

[Mathematical scope](SYNOPSIS108.md#conditional-embeddings-and-random-features).

#### Mathlib

Covariance bilinear forms of measures on Banach spaces are defined (`ProbabilityTheory.covarianceBilin`, `Probability/Moments/CovarianceBilin.lean`). Cross-covariance operators between reproducing-kernel Hilbert spaces are not. Hoeffding's inequality, the pointwise tool of item 74, is recorded under the previous heading.

#### TauCeti

Bochner's theorem, recorded above, makes the spectral measure of a normalized continuous positive-definite function a probability measure (`TauCeti.bochner_probabilityMeasure`, [Bochner](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Analysis/Bochner/BochnerTheorem.lean)). This is the starting point of random Fourier features. The unbiasedness identity \(\mathbb E\,z(x)^\top z(y)=k(x,y)\), the uniform approximation bound, conditional mean embeddings, and the regularized estimator are not formalized. As supporting material for the uniform bound, a subset of a closed ball of radius \(r\) in an \(n\)-dimensional real normed space has an \(\varepsilon\)-net of at most \((1+2r/\varepsilon)^n\) of its points (`TauCeti.exists_finset_isCover_of_subset_closedBall`, `TauCeti.coveringNumber_le_of_subset_closedBall`, [covering numbers](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Analysis/Normed/Module/CoveringNumber.lean)).

#### Statlib

No relevant declarations were found.

**Synopsis entries.** Not covered: 108.73, 108.74.

## Missing from all three libraries

The principal results of Section 108 that none of the three libraries provides are grouped below. Statlib's divergence and testing theory bears on them only through the total variation distance. In each case the nearest infrastructure and the distance from the statement are noted.

**Spectral graph theory and manifold learning (108.1–108.4, 108.8–108.12).** Weighted graphs and normalized Laplacians are missing. Mathlib's unweighted `SimpleGraph.lapMatrix` and the Rayleigh, Courant–Fischer, and Ky Fan principles in Mathlib and TauCeti are the starting point. Item 11 for weighted graphs is a modest generalization of the existing file. Items 2, 9, and 12 are then a few steps beyond Ky Fan's trace inequality, which needs to be restricted to an invariant subspace. The Cheeger inequality (item 1) needs a sweep-cut argument that is absent. Diffusion distances (item 3) need reversible Markov matrices with an \(L^2(\pi)\) spectral expansion. Classical multidimensional scaling (item 8) is two steps from `Matrix.posSemidef_gram` and the spectral theorem: double centring and the converse Gram factorization, plus the Frobenius form of Eckart–Young. Isomap consistency (item 4) needs submanifolds of positive reach and graph geodesics, none of which exist.

**Geometric statistics on manifolds and shape (108.5–108.7, 108.10, 108.13, 108.15–108.17).** TauCeti's Fréchet barycenter theory is general and metric. Its Riemannian geometry (exponential map, Hopf–Rinow, sectional curvature) is substantial. The two are not connected. The Karcher–Kendall–Afsari uniqueness theorem (item 13) needs comparison geometry under an upper curvature bound and convexity of \(d^2\) in small balls. The barycentric equation (item 15) needs differentiability of \(d^2\) off the cut locus, which needs the cut locus. Central limit theorems for intrinsic and extrinsic means (items 5, 10) need a multivariate delta method and \(M\)-estimation in a chart. Mathlib's central limit theorem is real-valued, so they are far. Kendall's shape space and Procrustes analysis (items 6, 16, 17) need the quotient of the preshape sphere by \(SO(m)\). TauCeti's Ky Fan principle gives the optimal rotation over \(O(m)\), so item 16 is one step away (the \(SO(m)\) sign correction) once configurations are set up. Hausdorff estimation of a submanifold (item 7) needs covering numbers of manifolds and a minimax framework.

**Persistent homology (108.18–108.39, except 108.31).** No persistence module, filtration of complexes, barcode, or diagram distance exists, so the whole stability and inference theory is missing. Interval decomposition (item 18) over a finite index set is the type \(A_n\) case of TauCeti's Gabriel theorem plus identification of the indecomposables, which is moderate. Over \(\mathbb R\) it needs Crawley-Boevey's theorem, which is far. The isometry theorem (item 20) and bottleneck stability (item 19) require diagrams, matchings, and interleavings from scratch. The nerve theorem for convex sets (item 21) could start from TauCeti's Čech–singular quasi-isomorphism for open covers, but needs the nerve as a simplicial complex and closed covers. Homology inference from samples (items 22, 37, 38) needs reach, weak feature size, and the deformation retraction of offsets. The matrix-reduction algorithm (item 32) is self-contained linear algebra over a field, close to TauCeti's ordered simplicial chain complex and reachable with moderate work. Item 33 needs minimum spanning trees, which none of the three libraries has. Item 31 is one assembly step from existing TauCeti theorems for the Euler–Poincaré formula and its invariance; the positive/negative dichotomy remains. Items 27 and 29 are short consequences of Mathlib's Hausdorff-distance lemmas once diagrams and landscapes are defined.

**Statistical optimal transport (108.40, 108.42, 108.44, 108.47, 108.48, 108.50–108.53, 108.55, 108.56, 108.58, 108.59).** TauCeti's analytic transport theory is broad, but no rate is proved. Empirical Wasserstein rates (item 40) need dyadic partition or chaining bounds on top of the almost-sure convergence theorem. They are far, as are the minimax lower bounds (item 50) and smoothing rates (item 51). Stability of Brenier maps (item 42) is a few steps from the existing transport-stability theorem, Brenier uniqueness, and the equivalence of graph-plan convergence with convergence in measure. The one-dimensional limit theorem (item 47) needs the Brownian-bridge limit of quantile processes, which is absent. The sliced distance (item 48) is close: one-dimensional transport and Mathlib's characteristic-function injectivity are present, and only measurability in \(\theta\) and the triangle inequality under integration remain. For the debiased Sinkhorn divergence (item 44), TauCeti proves nonnegativity and definiteness for nonnegative costs; real-valued costs reduce to that case by a constant shift, and the metrization of weak convergence is missing. Semidual and semidiscrete theory (items 52, 53, 56) need Legendre conjugates of convex potentials on \(\mathbb R^d\) and polyhedral Laguerre cells, which are absent. The Karcher-mean calculus (items 58, 59) needs differentiability of \(W_2^2\) at absolutely continuous laws, which is not proved. TauCeti's Wasserstein subdifferential and tangent space are the natural setting.

**Kernel methods (108.60–108.74, except the parts of 108.60, 108.68, and 108.69 noted).** TauCeti has mean embeddings, universal kernels, and Bochner's theorem, but no MMD statistics. The unit-ball formula and the witness function (items 60, 65) are one step from the Kolmogorov space construction. The characteristic property of translation-invariant kernels (item 68(c)) is a few steps from Bochner's theorem plus Fourier uniqueness of finite measures. The expectation identity for empirical kernel means (item 64) is a short Hilbert-space computation, and its high-probability bound would follow from McDiarmid's inequality. Degenerate \(U\)-statistic limits (items 61, 63, 67) need \(U\)-statistics, Mercer expansions, and Hilbert-space central limit theorems, all absent, so they are far. Energy distance and distance covariance (item 62) need the conditionally negative definite kernel \(\|x-y\|\). Permutation tests (item 66) need only finite exchangeability and randomized quantiles, so they are close given TauCeti's exchangeability layer. The comparison inequalities of item 69 are short consequences of the mean embedding, Kantorovich–Rubinstein duality, and Statlib's variational form of total variation once MMD is defined. Metrization (items 69, 70) needs MMD defined on probability measures together with Mathlib's Prokhorov theorem. Kernel Stein discrepancies (items 71, 72) need vector-valued RKHS of differentiable kernels and Stein's identity, and they are far. Conditional mean embeddings (item 73) need cross-covariance operators between RKHSs. Random Fourier features (item 74) are close: Bochner's probability form and Mathlib's Hoeffding inequality give the pointwise bound directly, and the uniform bound needs a Lipschitz and union-bound argument over TauCeti's volumetric nets.
