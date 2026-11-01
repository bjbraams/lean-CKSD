# Structure 107: Statistical learning and machine learning

Part of the [Mathlib and TauCeti coverage series](STRUCTURE.md).
[Mathematical inventory](SYNOPSIS107.md); [bibliographical scope](CKSD-bib.md#cks-107).

This file follows the thematic order and lettered subdivisions of the mathematical inventory. It records definitions, structures, and proved results, with supporting material identified separately. A topic heading locates the recorded statements; the **Synopsis entries** line at the end of each section states which numbered results are covered.

**Source baseline.** Mathlib `911003dd6dea5df215dff57f2717be762e11a6ca` and TauCeti `a049b4264d2cf4dbf4720796f844a3a3764914a5`, both of 2026-10-18, checked against local checkouts on 2026-11-01. See the [revision and source conventions](STRUCTURE.md#source-baseline-and-conventions).

**Mathlib source areas.** `Mathlib.Combinatorics.SetFamily.Shatter`, `Mathlib.Probability.Moments.SubGaussian`, `Mathlib.Probability.Moments.Variance`, `Mathlib.Probability.Moments.MGFAnalytic`, `Mathlib.Probability.Independence.Conditional`, `Mathlib.Probability.ConditionalProbability`, `Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs`, `Mathlib.Probability.Kernel.IonescuTulcea.Traj`, `Mathlib.InformationTheory.KullbackLeibler`, `Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym`, `Mathlib.Analysis.InnerProductSpace.Reproducing`, `Mathlib.Analysis.InnerProductSpace.Projection.Minimal`, `Mathlib.Analysis.SpecialFunctions.Log.NegMulLog`, `Mathlib.Analysis.SpecialFunctions.BinaryEntropy`, `Mathlib.Analysis.Fourier.ZMod`, `Mathlib.LinearAlgebra.Matrix.Circulant`, `Mathlib.Topology.MetricSpace.Contracting`, `Mathlib.Analysis.Normed.Ring.Units`.

**Namespaces.** Probability results are in `ProbabilityTheory`, including the sub-Gaussian predicate `HasSubgaussianMGF` and conditional independence `CondIndepFun`. The Kullback–Leibler divergence `klDiv` is in `InformationTheory`. Reproducing-kernel Hilbert spaces are the class `RKHS`. The binomial random graph is `SimpleGraph.binomialRandom`. The Banach fixed-point theorem is in `ContractingWith`. Circulant matrices are `Matrix.circulant`. TauCeti declarations are in `TauCeti`, `TauCeti.Probability`, `TauCeti.DenseGraphLimits` (graphons and exchangeable random graphs), and `Matrix.PosSemidef` (Kolmogorov feature maps and kernel mean embeddings).

Neither library has a notion of a learning rule, of a hypothesis class with its risk, of a sequential policy, of a Markov decision process, or of a differentially private mechanism. Almost all of this section is therefore not covered. What is recorded below is the probabilistic, information-theoretic, and linear-algebraic infrastructure on which the statements would be built, together with the few results, chiefly on exchangeable random graphs and Gaussian conditioning, that reach a numbered entry.

<a id="structure-107a"></a>

## 107A. Learning Theory, Probabilistic Models, Deep Learning, and Networks

This subdivision covers generalization bounds, classification targets, kernel and nearest-neighbour methods, ensembles and graphical models, neural-network approximation and training, and network data. The libraries supply concentration inequalities, the VC dimension of finite set families, reproducing-kernel Hilbert spaces, the Kullback–Leibler divergence, Gaussian conditioning, and a substantial theory of graphons and exchangeable random graphs. No learning-theoretic statement as such is formalized.

### Statistical learning theory

[Mathematical scope](SYNOPSIS107.md#statistical-learning-theory).

#### Mathlib

**VC dimension.** Shattering and the VC dimension of a finite family of finite sets are defined (`Finset.shatterer`, `Finset.vcDim`, `Combinatorics/SetFamily/Shatter.lean`), and the Sauer–Shelah bound is proved (`Finset.card_shatterer_le_sum_vcDim`); see [CKMA Structure 07](../lean-CKMA/STRUCTURE07.md). This is the combinatorial input to item 1, but there is no notion of a classification rule, of PAC learnability, or of sample complexity. The uniform deviation bound for VC classes, CKMA SYNOPSIS07 item 37, is not formalized.

**Hoeffding inequalities.** Hoeffding's lemma (`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc`) and the tail bound for sums of independent sub-Gaussian variables (`ProbabilityTheory.measure_sum_ge_le_of_iIndepFun`, `Probability/Moments/SubGaussian.lean`) give the deviation bound for a single bounded loss. These are supporting material for items 1, 2, and 15.

**Convex projection.** In a real inner product space the nearest point of a nonempty complete convex set exists and is characterized by the variational inequality \(\langle u-v,w-v\rangle\le0\) (`exists_norm_eq_iInf_of_complete_convex`, `norm_eq_iInf_iff_real_inner_le_zero`, `Analysis/InnerProductSpace/Projection/Minimal.lean`). This is the nonexpansive projection step of online gradient descent, item 4; the regret bound is not stated.

**Reproducing kernels.** Vector-valued reproducing-kernel Hilbert spaces are the class `RKHS` (`Analysis/InnerProductSpace/Reproducing.lean`). The kernel of such a space is positive semidefinite (`RKHS.posSemidef_kernel`), and every positive semidefinite kernel is the kernel of the space `RKHS.OfKernel` (`RKHS.kernel_ofKernel`, Moore's theorem). This is supporting material for item 3; the Rademacher complexity is not defined.

#### TauCeti

The Rademacher law on \(\mathbb R\), with its moments and transforms, is defined ([Rademacher](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Probability/Distributions/Rademacher.lean), `TauCeti.Probability.rademacherMeasure`). McDiarmid's bounded-differences theorem is proved for finite products of a probability space ([McDiarmid](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Probability/McDiarmid.lean), `TauCeti.Probability.hasSubgaussianMGF_of_bounded_differences`). It is the concentration step in the high-probability parts of item 2; symmetrization and the expected-supremum bound are not stated. Empirical measures of finite samples are defined ([empirical measures](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Probability/Process/EmpiricalMeasure.lean), `TauCeti.Probability.empiricalMeasure`), without uniform deviation bounds.

For a scalar positive-definite kernel, the Kolmogorov feature map \(\Phi\) with \(\langle\Phi(a),\Phi(b)\rangle=K(a,b)\) is constructed through Mathlib's `RKHS.OfKernel` ([Kolmogorov decomposition](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Analysis/PositiveDefinite/Kernel/Kolmogorov.lean), `Matrix.PosSemidef.kolmogorovFeature`, `Matrix.PosSemidef.inner_kolmogorovFeature`). With the Cauchy–Schwarz inequality this feature map is the starting point for item 3.

Exchangeability of a sequence of random variables is defined ([exchangeability](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Probability/Exchangeability/Basic.lean), `TauCeti.Probability.Exchangeable`), with de Finetti's theorem; see [CKMA Structure 06](../lean-CKMA/STRUCTURE06.md). The rank argument behind split conformal prediction, item 6, is not stated.

**Synopsis entries.** Not covered: 107.1–107.7.

### Statistical targets in classification

[Mathematical scope](SYNOPSIS107.md#statistical-targets-in-classification).

#### Mathlib

Conditional expectation, and hence the regression function \(\eta(x)=P(Y=1\mid X=x)\) as an almost-everywhere-defined function, is available ([CKMA Structure 06](../lean-CKMA/STRUCTURE06.md)). Neither the Bayes classifier nor the excess-risk identity is stated.

#### TauCeti

No relevant declarations were found.

**Synopsis entries.** Not covered: 107.8, 107.9.

### Margins, surrogate losses, and stability

[Mathematical scope](SYNOPSIS107.md#margins-surrogate-losses-and-stability).

#### Mathlib

No margin bound, surrogate-risk comparison, or stability notion is stated. The concentration ingredients are those listed under statistical learning theory.

#### TauCeti

McDiarmid's inequality, recorded above, is the concentration step in the proof of item 12; uniform stability is not defined.

**Synopsis entries.** Not covered: 107.10–107.12.

### Kernel regression, nearest neighbours, and data splitting

[Mathematical scope](SYNOPSIS107.md#kernel-regression-nearest-neighbours-and-data-splitting).

#### Mathlib

For hold-out selection, item 15, Hoeffding's inequality for independent bounded summands (`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc`, `ProbabilityTheory.measure_sum_ge_le_of_iIndepFun`) applies to the hold-out error frequency of each fixed candidate, and the finite union bound is `measure_iUnion_fintype_le` (`MeasureTheory/OuterMeasure/Basic.lean`). The selection inequality obtained by combining them is not stated, and neither is the conditioning on the training part. Kernel ridge regression, its critical-radius rate, and nearest-neighbour rules are absent.

#### TauCeti

No relevant declarations were found.

**Synopsis entries.** Not covered: 107.13, 107.14, 107.15 (ingredients only: Hoeffding's bound for each fixed candidate and the union bound; the selection inequality is not stated).

### Foundations, probabilistic modelling, and ensembles

[Mathematical scope](SYNOPSIS107.md#foundations-probabilistic-modelling-and-ensembles).

#### Mathlib

The Hausdorff distance between subsets of a metric space is `Metric.hausdorffDist` (`Topology/MetricSpace/HausdorffDistance.lean`). This is the metric of item 16; the \(k\)-means criterion and its consistency are absent. Trees in simple graphs are `SimpleGraph.IsTree` (`Combinatorics/SimpleGraph/Acyclic.lean`), but binary decision trees, pruning, boosting, belief propagation, and forests are not formalized.

#### TauCeti

The identification of the Gaussian-process posterior mean with kernel ridge regression and simple kriging, in the preamble, rests on the Gaussian conditioning formula recorded under item 34 below.

**Synopsis entries.** Not covered: 107.16–107.20.

### Prediction losses and ensemble structure

[Mathematical scope](SYNOPSIS107.md#prediction-losses-and-ensemble-structure).

#### Mathlib

**Divergence and logarithmic loss.** The Kullback–Leibler divergence of finite measures is `InformationTheory.klDiv`, valued in \([0,\infty]\), and it vanishes exactly when the two finite measures are equal (`InformationTheory.klDiv_eq_zero_iff`, `InformationTheory/KullbackLeibler/Basic.lean`). This is Gibbs' inequality, so a reported distribution \(q\) minimizes \(D(p\|q)\) only at \(q=p\). The decomposition of the expected logarithmic loss into entropy plus divergence, and the Brier-score identity, are not stated; Mathlib has no Shannon entropy of a finite distribution beyond the binary and \(q\)-ary entropy functions (`Analysis/SpecialFunctions/BinaryEntropy.lean`).

**Variance of a sum.** For square-integrable real random variables on a finite measure space, the variance of a finite sum is the double sum of covariances (`ProbabilityTheory.variance_sum`, `Probability/Moments/Variance.lean`), and covariance is bilinear (`ProbabilityTheory.covariance_sum_left`, `ProbabilityTheory.covariance_sum_sum`, `Probability/Moments/Covariance.lean`). With equal variances \(\sigma^2\) and equal pairwise correlations \(\rho\), the double sum is \(B\sigma^2+B(B-1)\rho\sigma^2\). Item 22 is this computation divided by \(B^2\), which is not stated.

#### TauCeti

For finite measures on a finite space, the divergence is written as a finite sum, \(\sum_x\mu\{x\}\log(\mu\{x\}/\nu\{x\})\) up to the mass correction ([finite divergence](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/InformationTheory/KullbackLeibler/Finite.lean), `TauCeti.klDiv_eq_ofReal_sum_log_singleton`). This is the form needed in item 21.

Exact belief propagation on trees, item 23, is not formalized in either library.

**Synopsis entries.** Not covered: 107.21 (ingredients only: Gibbs' inequality, and the finite-sum form of the divergence in TauCeti; the cross-entropy decomposition and the Brier identity are not stated), 107.22 (ingredients only: the variance of a sum as a double sum of covariances; the equicorrelated specialization is not stated), 107.23.

### Boosting and tree splitting

[Mathematical scope](SYNOPSIS107.md#boosting-and-tree-splitting).

#### Mathlib

Strict concavity of \(x\mapsto-x\log x\) on \([0,\infty)\) (`Real.strictConcaveOn_negMulLog`, `Analysis/SpecialFunctions/Log/NegMulLog.lean`) and of the binary entropy on \([0,1]\) (`Real.strictConcave_binEntropy`, `Analysis/SpecialFunctions/BinaryEntropy.lean`) are proved. Since the parent proportions are \(p(\cdot\mid t)=p_Lp(\cdot\mid t_L)+p_Rp(\cdot\mid t_R)\), the first assertion of item 25 is the defining inequality of `StrictConcaveOn` applied to this two-point combination. The impurity-function axioms and Breiman's ordering theorem for categorical splits are not formalized. AdaBoost is absent.

#### TauCeti

No relevant declarations were found.

**Synopsis entries.** Not covered: 107.24, 107.25 (ingredients only: the nonnegativity and equality case are the definition of strict concavity, with strict concavity of the entropy summands proved; the ordering theorem for categorical predictors is not stated).

### Variational and exact inference

[Mathematical scope](SYNOPSIS107.md#variational-and-exact-inference).

#### Mathlib

For a real random variable, the derivative of the cumulant-generating function at an interior point of the exponential-integrability set is the mean under the exponentially tilted law, and its second derivative is the tilted variance (`ProbabilityTheory.deriv_cgf`, `ProbabilityTheory.iteratedDeriv_two_cgf`, `Probability/Moments/MGFAnalytic.lean`). This is the one-parameter case of the gradient map \(\nabla A\) in item 26. Multiparameter exponential families, the mean-parameter set, and the conjugate-duality representation are not formalized, and chordal graphs and junction trees are absent.

#### TauCeti

No relevant declarations were found. The Legendre-type duality in TauCeti's optimal-transport files (\(c\)-transforms) is a different construction.

**Synopsis entries.** Not covered: 107.26, 107.27.

### Deep learning: architectures, approximation, and training

[Mathematical scope](SYNOPSIS107.md#deep-learning-architectures-approximation-and-training).

#### Mathlib

The Fourier transform of functions on a finite-dimensional real inner product space is the instance `Real.instFourierTransform`, with integral formula `Real.fourier_eq` (`Analysis/Fourier/FourierTransform.lean`), the analytic input to Barron's spectral norm in item 28. Neural networks, Hölder compositional classes, the neural tangent kernel, and the Jensen–Shannon divergence are not defined. The density of one-hidden-layer networks, CKMA SYNOPSIS47 item 76, is recorded as not covered in [CKMA Structure 47](../lean-CKMA/STRUCTURE47.md).

#### TauCeti

**Inverse-Wishart mean.** For a positive-definite scale \(S\) of size \(p\) and degree \(n>p+1\), the inverse-Wishart law has mean \((n-p-1)^{-1}S\); in positive dimension the identity is not integrable for \(p-1<n\le p+1\) ([inverse-Wishart moments](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Probability/Distributions/Wishart/Inverse/Moments.lean), `TauCeti.Probability.integral_id_inverseWishartMeasure`, `TauCeti.Probability.not_integrable_id_inverseWishartMeasure`). The inverse-Wishart law is defined as the image of the nonsingular Wishart law with inverted scale under matrix inversion. The Gram matrix of independent centred Gaussian rows has the Wishart law ([Wishart agreement](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Probability/Distributions/Wishart/Agreement.lean), `TauCeti.Probability.hasLaw_wishartGram_gaussian_nonsingularWishartMeasure`). Together these give \(\mathbb E(X^\top X)^{-1}=I/(n-p-1)\) for an isotropic Gaussian design, which is the moment behind the underparameterized formula \(\sigma^2p/(n-p-1)\) in item 31. The risk formula itself, the overparameterized case, and the limits are not stated.

**Synopsis entries.** Not covered: 107.28–107.30, 107.31 (ingredients only: the inverse-Wishart mean and the Wishart law of a Gaussian Gram matrix, which give the key moment of the case \(n>p+1\); the risk identities are not stated), 107.32.

### Probabilistic output layers and kernel prediction

[Mathematical scope](SYNOPSIS107.md#probabilistic-output-layers-and-kernel-prediction).

#### Mathlib

The multivariate Gaussian law with mean \(m\) and positive semidefinite covariance \(S\) is `ProbabilityTheory.multivariateGaussian` (`Probability/Distributions/Gaussian/Multivariate.lean`). Softmax, the log-sum-exp function, and its Hessian are not defined. The scalar cumulant derivatives recorded under item 26 are the one-dimensional analogue of the gradient identity in item 33.

#### TauCeti

**Gaussian conditioning.** Let \(X\) be a Gaussian vector indexed by \(\iota\sqcup\kappa\) with mean \(m\) and positive semidefinite covariance \(S\), whose observed block \(S_{22}\) is positive definite. Then the regular conditional law of the first block given the second is, almost everywhere, Gaussian with mean \(m_1+S_{12}S_{22}^{-1}(x_2-m_2)\) and covariance given by the Schur complement \(S_{11}-S_{12}S_{22}^{-1}S_{21}\) ([conditional Gaussian](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Probability/Distributions/Gaussian/Conditional.lean), `TauCeti.Probability.condDistrib_multivariateGaussian`, `EuclideanSpace.gaussianCondMean`, `Matrix.gaussianCondCov`). For the joint law of \((f(x),f(x'),y_1,\ldots,y_n)\) the observed block is \(K+\sigma^2I\), positive definite when \(\sigma^2>0\), so this formula gives the posterior mean and covariance of item 34 at finitely many test points. A Gaussian process indexed by an arbitrary set, the predictive variance of a new response, and the identification with kernel ridge regression are not stated.

The kernel mean embedding of a measure into the Kolmogorov space of a positive-definite kernel is defined, with \(\|m_\mu-m_\nu\|^2\) equal to the kernel energy of \(\mu-\nu\) ([mean embeddings](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Analysis/PositiveDefinite/Kernel/MeanEmbedding.lean), `Matrix.PosSemidef.kernelMeanEmbedding`, `Matrix.PosSemidef.norm_kernelMeanEmbedding_sub_sq`); this is supporting material.

**Synopsis entries.** Partly covered: 107.34 (block Gaussian conditioning with a positive definite observed block, in TauCeti; the Gaussian-process formulation and the kernel ridge identification are not stated). Not covered: 107.33.

### Capacity, depth, and symmetry

[Mathematical scope](SYNOPSIS107.md#capacity-depth-and-symmetry).

#### Mathlib

**Circulant matrices.** The circulant matrix of a vector \(v\) indexed by an additive group has entries \(v(i-j)\) (`Matrix.circulant`, `LinearAlgebra/Matrix/Circulant.lean`). Products of circulant matrices are circulant (`Matrix.circulant_mul`), and over a commutative ring any two circulant matrices commute (`Matrix.circulant_mul_comm`). Since the cyclic shift is the circulant matrix of a unit vector (`Matrix.circulant_single`), every circulant matrix commutes with the shift. The converse, that a matrix commuting with the shift is circulant, is not stated. The discrete Fourier transform on \(\mathbb Z/N\mathbb Z\) is defined, with its inversion formula (`ZMod.dft`, `ZMod.dft_dft`, `Analysis/Fourier/ZMod.lean`), but the diagonalization of circulant matrices by it is not stated.

The characterization of permutation-equivariant linear maps, the equivariance of self-attention, VC bounds for network classes, and approximation rates for ReLU networks are absent.

#### TauCeti

No relevant declarations were found.

**Synopsis entries.** Partly covered: 107.38 (circulant matrices commute with each other, hence with the shift; the converse, Fourier diagonalization, the permutation-equivariant layers, and self-attention are not stated). Not covered: 107.35–107.37.

### Random initialization and implicit bias

[Mathematical scope](SYNOPSIS107.md#random-initialization-and-implicit-bias).

#### Mathlib

No relevant declarations were found. Mathlib has no Moore–Penrose pseudoinverse of a real matrix and no convergence theorem for gradient descent.

#### TauCeti

No relevant declarations were found.

**Synopsis entries.** Not covered: 107.39, 107.40.

### Networks and graph representation learning

[Mathematical scope](SYNOPSIS107.md#networks-and-graph-representation-learning).

#### Mathlib

The binomial random graph \(G(V,p)\) on a vertex type \(V\), with independent edges of probability \(p\in[0,1]\), is `SimpleGraph.binomialRandom`. On a finite vertex type a graph \(G\) has probability \(p^{|E(G)|}(1-p)^{\binom{|V|}2-|E(G)|}\) (`SimpleGraph.binomialRandom_singleton`, `Probability/Combinatorics/BinomialRandomGraph/Defs.lean`). Stochastic block models, recovery thresholds, contiguity, and Weisfeiler–Leman refinement are not formalized.

#### TauCeti

**Graphons and exchangeable random graphs.** A graphon on a probability space \((\Omega,\mu)\) is a symmetric measurable kernel with values in \([0,1]\) (`TauCeti.DenseGraphLimits.Graphon`). Graphons on the unit interval modulo cut distance zero form the compact metric space `TauCeti.DenseGraphLimits.GraphonSpaceI` ([graphons](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Combinatorics/DenseGraphLimits/Graphon/Basic.lean), [compactness](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Combinatorics/DenseGraphLimits/GraphonSpace/Compact.lean)). An exchangeable random graph on \(\mathbb N\) is a probability law on `SimpleGraph ℕ` invariant under relabelling by every permutation of \(\mathbb N\) (`TauCeti.DenseGraphLimits.InfiniteExchangeableGraphLaw`, [infinite exchangeable laws](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Combinatorics/DenseGraphLimits/ExchangeableGraphLaw/Infinite/Basic.lean)).

The graphon form of the Aldous–Hoover theorem, in the version of Diaconis and Janson, is proved. Every exchangeable law on infinite graphs is the integral, against exactly one probability measure on `GraphonSpaceI`, of the laws of the graphon model: draw independent uniform latent variables and include each edge independently with probability \(W(U_i,U_j)\) ([mixture representation](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Combinatorics/DenseGraphLimits/ExchangeableGraphLaw/Infinite/Mixture.lean), `TauCeti.DenseGraphLimits.InfiniteExchangeableGraphLaw.existsUnique_bind_infiniteSampleLawOnSpace`, `TauCeti.DenseGraphLimits.graphonMixtureLawEquiv_law`). Two graphons, on arbitrary probability spaces, at cut distance zero have the same finite sampling laws (`TauCeti.DenseGraphLimits.sampleGraph_eq_of_cutDist_eq_zero`). Conversely, equal sampling laws give equal homomorphism densities, and equal homomorphism densities force cut distance zero ([separation](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Combinatorics/DenseGraphLimits/Separation/Inverse.lean), `TauCeti.DenseGraphLimits.cutDist_eq_zero_iff_forall_homDensity_eq_cross`). On standard Borel carriers the cut distance equals the infimum, over pairs of measure-preserving maps from the unit interval, of the cut norm of the difference of the pullbacks ([map form of the cut distance](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Combinatorics/DenseGraphLimits/CutMetric/Pullback/Basic.lean), `TauCeti.DenseGraphLimits.cutDist_eq_cutDistPullback`).

The two formal statements differ from the synopsis in two places. Exchangeability is assumed under all permutations of \(\mathbb N\), not only finite ones; the two hypotheses are equivalent because a law on `SimpleGraph ℕ` is determined by its finite windows, but this equivalence is not stated. The uniqueness is up to cut distance zero, expressed as an infimum over pullbacks. The characterization of weak isomorphism by pullbacks that agree almost everywhere, with the infimum attained, is not stated. TauCeti also proves a decomposition of exchangeable array laws into dissociated components, a step towards the general Aldous–Hoover representation ([array decomposition](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Probability/Exchangeability/Arrays/AldousHoover/Decomposition.lean)).

**Synopsis entries.** Partly covered: 107.43 (the mixture representation and the uniqueness of the mixing measure up to cut distance zero, in TauCeti; invariance is assumed under all permutations, and weak isomorphism by almost-everywhere equal pullbacks is not stated). Not covered: 107.41, 107.42, 107.44.

### Symmetry and graph signal

[Mathematical scope](SYNOPSIS107.md#symmetry-and-graph-signal).

#### Mathlib

The adjacency matrix of a simple graph is `SimpleGraph.adjMatrix` (`Combinatorics/SimpleGraph/AdjMatrix.lean`), and Hermitian matrices have the spectral theorem (`Matrix.IsHermitian.eigenvalues`; see [CKMA Structure 13](../lean-CKMA/STRUCTURE13.md)). The eigenstructure of the block-model expectation and the permutation equivariance of message passing are not stated.

#### TauCeti

No relevant declarations were found.

**Synopsis entries.** Not covered: 107.45, 107.46.

### Random graphs and spectral recovery

[Mathematical scope](SYNOPSIS107.md#random-graphs-and-spectral-recovery).

#### Mathlib

The binomial random graph is defined, as recorded above. The phase transition, the giant component, and the connectivity threshold are absent. The Galton–Watson survival probability, CKMA SYNOPSIS06 item 65, is recorded as not covered in [CKMA Structure 06](../lean-CKMA/STRUCTURE06.md).

#### TauCeti

The Davis–Kahan \(\sin\Theta\) theorem is proved in a dimension-free operator-norm form. If \(U\) is invariant under \(A\), \(W\) is invariant under a symmetric \(B\), the quadratic form of \(A\) on \(U\) is at least \(c+g\), and that of \(B\) on \(W\) is at most \(c\), then \(g\|P_WP_U\|\le\|B-A\|\) ([sin Θ](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Analysis/InnerProductSpace/Projection/SinTheta.lean), `Submodule.mul_norm_starProjection_comp_starProjection_le_norm_sub`). Versions in unitarily invariant seminorms are in [CKMA Structure 13](../lean-CKMA/STRUCTURE13.md). This is the deterministic perturbation step of item 48. The counting of misclassified vertices and the operator-norm bound for the noise matrix are not stated.

**Synopsis entries.** Not covered: 107.47, 107.48.

<a id="structure-107b"></a>

## 107B. Bandits, Reinforcement Learning, Privacy, Fairness, and Distribution Shift

Neither library defines bandit policies, Markov decision processes, value functions, or differential privacy. The relevant infrastructure is the Ionescu–Tulcea construction of laws of processes driven by kernels, the Banach fixed-point theorem, Neumann series, the Kullback–Leibler divergence with its chain rule and Pinsker's inequality, sub-Gaussian concentration, conditional independence, Radon–Nikodym change of measure, and the Laplace and Gaussian laws.

### Bandits and reinforcement learning

[Mathematical scope](SYNOPSIS107.md#bandits-and-reinforcement-learning).

#### Mathlib

**Laws of interaction.** The Ionescu–Tulcea theorem constructs the law of a trajectory from a sequence of kernels, each depending on the history so far (`ProbabilityTheory.Kernel.traj`, `Probability/Kernel/IonescuTulcea/Traj.lean`). This is the construction that turns a policy and an environment into a law on histories, but no bandit or decision-process structure is built on it.

**Divergence.** The chain rule for the Kullback–Leibler divergence of composition products, \(D(\mu\otimes\kappa\|\nu\otimes\eta)=D(\mu\|\nu)+D(\mu\otimes\kappa\|\mu\otimes\eta)\), and the data-processing inequality are proved (`InformationTheory.klDiv_compProd_eq_add`, `InformationTheory/KullbackLeibler/ChainRule.lean`; `InformationTheory.klDiv_map_le`, `InformationTheory/KullbackLeibler/DataProcessing.lean`). These are the divergence-decomposition and change-of-measure steps of the Lai–Robbins lower bound, item 49.

**Contractions.** The Banach fixed-point theorem gives, for a contraction with constant \(K<1\) on a complete metric space, a unique fixed point and the a priori geometric bound for the iterates (`ContractingWith.fixedPoint_isFixedPt`, `ContractingWith.fixedPoint_unique`, `ContractingWith.apriori_dist_iterate_fixedPoint_le`, `Topology/MetricSpace/Contracting.lean`). This is the abstract half of item 53; the Bellman operator and the optimality of greedy policies are not stated. The almost-sure convergence of \(L^1\)-bounded submartingales (`MeasureTheory.Submartingale.ae_tendsto_limitProcess`, `Probability/Martingale/Convergence.lean`) is the starting point for the stochastic-approximation argument of item 54, which is not formalized.

#### TauCeti

The path law of a homogeneous Markov chain is constructed from Mathlib's Ionescu–Tulcea measure, with its finite-dimensional product formula ([Markov chains](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Probability/Process/MarkovChain.lean), `TauCeti.Probability.markovChainLaw`). It supports the Markov bandit of item 51; Gittins indices are absent. The divergence of product measures is the sum of the divergences of the factors ([chain rule](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/InformationTheory/KullbackLeibler/ChainRule.lean), `TauCeti.klDiv_prod_prod`).

**Synopsis entries.** Not covered: 107.49–107.54.

### Policy evaluation and policy-dependent distributions

[Mathematical scope](SYNOPSIS107.md#policy-evaluation-and-policy-dependent-distributions).

#### Mathlib

In a complete normed ring, if \(\|t\|<1\) then \(1-t\) is invertible with inverse \(\sum_{i\ge0}t^i\) (`NormedRing.inverse_one_sub`, `Analysis/Normed/Ring/Units.lean`). Applied to \(t=\gamma P_\pi\) in the supremum norm, this is the Neumann-series identity of item 55. The policy value, policy improvement, the performance-difference identity, and the policy-gradient theorem are not stated.

#### TauCeti

No relevant declarations were found.

**Synopsis entries.** Not covered: 107.55–107.57.

### Optimal policies, planning, and sample complexity

[Mathematical scope](SYNOPSIS107.md#optimal-policies-planning-and-sample-complexity).

#### Mathlib

No relevant declarations were found beyond the contraction and Neumann-series results above. Linear-programming duality for occupancy measures, sample-complexity bounds for the generative model, temporal-difference learning, and natural policy gradient are absent.

#### TauCeti

No relevant declarations were found.

**Synopsis entries.** Not covered: 107.58–107.61.

### Minimax and linear bandits

[Mathematical scope](SYNOPSIS107.md#minimax-and-linear-bandits).

#### Mathlib

The Azuma–Hoeffding estimate for adapted sums with conditionally sub-Gaussian increments is proved (`ProbabilityTheory.measure_sum_ge_le_of_hasCondSubgaussianMGF`, `Probability/Moments/SubGaussian.lean`; see [CKMA Structure 07](../lean-CKMA/STRUCTURE07.md)). This is scalar and has a fixed horizon. The self-normalized vector bound of item 63, which needs the method of mixtures and a maximal inequality uniform in time, is not stated.

#### TauCeti

No relevant declarations were found.

**Synopsis entries.** Not covered: 107.62, 107.63.

### Privacy, fairness, and distribution shift

[Mathematical scope](SYNOPSIS107.md#privacy-fairness-and-distribution-shift).

#### Mathlib

**Change of measure.** If \(\mu\ll\nu\), then \(\int(d\mu/d\nu)\,f\,d\nu=\int f\,d\mu\) (`MeasureTheory.integral_rnDeriv_smul`, `MeasureTheory/Measure/Decomposition/RadonNikodym.lean`). Under covariate shift the target joint law has density \(w(x)=dP_T^X/dP_S^X\) with respect to the source joint law. With this density the identity is the importance-weighting formula \(R_T(f)=\mathbb E_S[w(X)L(Y,f(X))]\) of item 68, but the passage from the marginal density ratio to the joint density is not stated. The \(\mathcal H\Delta\mathcal H\) bound is absent.

**Conditional independence.** Conditional independence of random variables given a σ-algebra is `ProbabilityTheory.CondIndepFun` (`Probability/Independence/Conditional.lean`). The fairness criteria of items 67 and 76 can be expressed with it, but no incompatibility theorem is stated.

#### TauCeti

The Laplace law with location \(\mu\) and scale \(b>0\), with density \((2b)^{-1}e^{-|x-\mu|/b}\), is defined and identified as a density law. Its distribution function, moments, and transforms are computed, and translation shifts the location ([Laplace law](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/Probability/Distributions/Laplace/Basic.lean), `TauCeti.Probability.laplaceMeasure`, `TauCeti.Probability.laplaceMeasure_map_add_const`). This is the noise law of item 64. The density-ratio bound \(e^{|a-a'|/b}\) between two translates, which is the core of the Laplace mechanism, is not stated.

**Synopsis entries.** Not covered: 107.64–107.67, 107.68 (ingredients only: the change-of-measure identity behind importance weighting; the joint density under covariate shift and the \(\mathcal H\Delta\mathcal H\) bound are not stated).

### Privacy mechanisms and weighted inference

[Mathematical scope](SYNOPSIS107.md#privacy-mechanisms-and-weighted-inference).

#### Mathlib

The Gaussian law on \(\mathbb R\) and multivariate Gaussian laws are available ([CKMA Structure 06](../lean-CKMA/STRUCTURE06.md)), as is the Bernoulli law. None of the privacy mechanisms is stated. No Bernstein inequality is stated, so the bound of item 73 is unavailable; Hoeffding's inequality gives only the weaker bound \(B\sqrt{\log(2/\delta)/(2n)}\).

#### TauCeti

No relevant declarations were found.

**Synopsis entries.** Not covered: 107.69–107.73.

### Threshold queries and local contraction

[Mathematical scope](SYNOPSIS107.md#threshold-queries-and-local-contraction).

#### Mathlib

The chain rule and data-processing inequality for the divergence, recorded above, give the tensorization step of item 75 once the single-release bound is known.

#### TauCeti

Pinsker's inequality is proved for probability measures, in the form \(|\mu-\nu|(\Omega)^2\le2D(\mu\|\nu)\) for the total variation of the signed difference, with no absolute-continuity hypothesis ([Pinsker](https://github.com/TauCetiProject/TauCeti/blob/a049b4264d2cf4dbf4720796f844a3a3764914a5/TauCeti/InformationTheory/KullbackLeibler/Pinsker.lean), `TauCeti.totalVariation_sq_le_two_mul_klDiv`). It bounds total variation by divergence, whereas item 75 bounds divergence by total variation under a likelihood-ratio constraint; the latter is not stated.

**Synopsis entries.** Not covered: 107.74, 107.75.

### Fairness criteria and label shift

[Mathematical scope](SYNOPSIS107.md#fairness-criteria-and-label-shift).

#### Mathlib

Bayes' theorem for conditional probability measures, \(\mu[t\mid s]=\mu(s)^{-1}\mu[s\mid t]\,\mu(t)\), is `ProbabilityTheory.cond_eq_inv_mul_cond_mul` (`Probability/ConditionalProbability.lean`). It is the elementary identity behind the label-shift correction of item 77, which is not stated. The fairness criteria are expressible with `ProbabilityTheory.CondIndepFun`, as noted above.

#### TauCeti

No relevant declarations were found.

**Synopsis entries.** Not covered: 107.76, 107.77.

## Missing from both libraries

**Learning-theoretic framework.** There is no definition of a hypothesis class with population and empirical risk, of a learning rule, or of PAC learnability, so items 1, 7, 9, 10, and 35 have no formal home. Item 9 is a two-line inequality once risks are defined. The fundamental theorem, item 1, needs the uniform deviation bound for VC classes, CKMA SYNOPSIS07 item 37, which is itself missing; Sauer–Shelah is present. Rademacher complexity, item 2, is one definition away, given TauCeti's Rademacher law and McDiarmid's inequality. Symmetrization is the missing step. Once symmetrization is available, the kernel-ball bound, item 3, follows from Mathlib's RKHS and the Cauchy–Schwarz inequality. Uniform stability, item 12, is close to McDiarmid's inequality once algorithms on samples are defined.

**Online learning and bandits.** Regret, online gradient descent, Hedge, Exp3, UCB, Thompson sampling, Gittins indices, the Lai–Robbins bound, and linear bandits, items 4, 5, 49–52, 62, and 63, are absent. Items 4 and 5 are deterministic potential-function arguments; they need only convex projection, which Mathlib has, and elementary inequalities for the exponential. The Lai–Robbins bound, item 49, would combine Mathlib's KL chain rule and data-processing inequality with an Ionescu–Tulcea law of the interaction; the bandit model is the missing layer. The self-normalized bound, item 63, needs a time-uniform maximal inequality for supermartingales (Ville's inequality), which neither library states.

**Markov decision processes.** No finite MDP, value function, or Bellman operator is defined. Items 53, 55, and 58 are short once the model is defined: they follow from `ContractingWith`, the Neumann series, and finite-dimensional linear algebra. Item 58 also needs linear-programming duality. Items 54 and 60 need a stochastic-approximation theorem of Robbins–Siegmund type, not present although Mathlib's martingale convergence theorem is. Items 56, 57, 59, and 61 are algebraic identities and concentration bounds on top of the same model.

**Classification theory.** The Bayes classifier and excess-risk identity, item 8, Zhang's comparison inequality, item 11, the kernel ridge rate, item 13, nearest-neighbour asymptotics, item 14, and Stone-type consistency of forests, item 20, are absent. Item 8 is one step from conditional expectation. Items 13, 14, and 20 need empirical-process and covering arguments that are missing; see [CKMA Structure 07](../lean-CKMA/STRUCTURE07.md).

**Ensembles, trees, and graphical models.** The \(k\)-means consistency, cost-complexity pruning, gradient-boosting descent, AdaBoost, and Breiman's ordering theorem, items 16–18, 24, and the second half of 25, are absent. Item 18 is a Hilbert-space computation and item 22 a covariance computation, both one step from existing API. Belief propagation, the Bethe free energy, junction trees, and the variational representation of exponential families, items 19, 23, 26, and 27, need multiparameter exponential families, chordal graphs, and convex conjugates, none of which is present.

**Neural networks.** No neural-network architecture is defined, so items 28–30, 32, 33, and 35–40 are absent. The cheapest entries are item 33, the gradient and Hessian of log-sum-exp, and item 32, the pointwise optimal discriminator, which also needs the Jensen–Shannon divergence. Item 38 needs the converse commutant statement and the Fourier diagonalization of circulants, from Mathlib's `Matrix.circulant` and `ZMod.dft`. Item 40 needs a Moore–Penrose pseudoinverse. Item 31 is closest: the inverse-Wishart mean in TauCeti gives the case \(n>p+1\) after a short computation; the case \(p>n+1\) needs the corresponding moment for the projection onto the row space. The Gaussian-process limit, item 39, needs a multivariate central limit theorem for exchangeable arrays of width tending to infinity, and Barron's and Yarotsky's rates need Fourier-analytic and Sobolev approximation theory beyond what is formalized.

**Network models.** The binomial random graph is only defined. Its phase transition and connectivity threshold, item 47, need branching-process comparison and the Poisson approximation, both absent. The stochastic block model, items 41, 42, 45, and 48, is not defined; item 45 is a rank-two eigenvalue computation, and item 48 is a combination of TauCeti's Davis–Kahan theorem with a matrix concentration bound that is missing (CKMA SYNOPSIS07 item 44). Contiguity, needed for item 42, is not defined. Weisfeiler–Leman refinement and message-passing networks, items 44 and 46, are combinatorial and absent. Item 46 is a direct verification once message passing is defined. For item 43 the remaining gap is the attained form of weak isomorphism, from cut distance zero to almost-everywhere equal pullbacks (the Borgs–Chayes–Lovász theorem), together with the reduction from finite to all permutations.

**Differential privacy.** No mechanism or privacy definition exists, so items 64–66, 69–72, 74, and 75 are absent. The Laplace and Gaussian mechanisms, items 64 and 70, are close to TauCeti's Laplace law and Mathlib's Gaussian law: they need a pointwise density-ratio bound and, for item 70, a Gaussian tail estimate. Composition, post-processing, and the exponential mechanism, items 65, 69, and 71, are measure-theoretic statements about kernels; the advanced composition bound also needs Azuma's inequality, which Mathlib has in conditional sub-Gaussian form. The local-privacy contraction, item 75, and the minimax rates, item 66, need a reverse-Pinsker inequality under bounded likelihood ratio and the two-point and Fano methods of SYNOPSIS103, which are absent.

**Fairness and distribution shift.** The fairness incompatibility results, items 67 and 76, are elementary consequences of conditional independence that are not stated; `CondIndepFun` supplies the language. The \(\mathcal H\Delta\mathcal H\) bound, item 68, needs the hypothesis-class framework. Item 73 needs a Bernstein inequality, which neither library states. Item 77 is Bayes' theorem plus a finite linear system and is one step from `cond_eq_inv_mul_cond_mul`.
