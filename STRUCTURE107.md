# Structure 107: Statistical learning and machine learning

Part of the [Mathlib, TauCeti, and Statlib coverage series](STRUCTURE.md).
[Mathematical inventory](SYNOPSIS107.md); [bibliographical scope](CKSD-bib.md#cks-107).

This file follows the thematic order and lettered subdivisions of the mathematical inventory. It records definitions, structures, and proved results, with supporting material identified separately. A topic heading locates the recorded statements; the **Synopsis entries** line at the end of each section states which numbered results are covered.

**Source baseline.** Mathlib `6135ffb78e8bcd3fcc8ec02f3f82ea0b0737358b` of 2026-11-05, TauCeti `afa08a3ed16fb167e35de371afb1eb03fbc5913a` of 2026-11-06, and Statlib `eeaac0283690efaa60c31115400cf561836baeb9` of 2026-11-05, checked against local checkouts on 2026-11-06. See the [revision and source conventions](STRUCTURE.md#source-baseline-and-conventions).

**Mathlib source areas.** `Mathlib.Combinatorics.SetFamily.Shatter`, `Mathlib.Probability.Moments.SubGaussian`, `Mathlib.Probability.Moments.Variance`, `Mathlib.Probability.Moments.MGFAnalytic`, `Mathlib.Probability.Independence.Conditional`, `Mathlib.Probability.ConditionalProbability`, `Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs`, `Mathlib.Probability.Kernel.IonescuTulcea.Traj`, `Mathlib.InformationTheory.KullbackLeibler`, `Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym`, `Mathlib.Analysis.InnerProductSpace.Reproducing`, `Mathlib.Analysis.InnerProductSpace.Projection.Minimal`, `Mathlib.Analysis.SpecialFunctions.Log.NegMulLog`, `Mathlib.Analysis.SpecialFunctions.BinaryEntropy`, `Mathlib.Analysis.Fourier.ZMod`, `Mathlib.LinearAlgebra.Matrix.Circulant`, `Mathlib.Topology.MetricSpace.Contracting`, `Mathlib.Analysis.Normed.Ring.Units`.

**Namespaces.** Probability results are in `ProbabilityTheory`, including the sub-Gaussian predicate `HasSubgaussianMGF` and conditional independence `CondIndepFun`. The Kullback–Leibler divergence `klDiv` is in `InformationTheory`. Reproducing-kernel Hilbert spaces are the class `RKHS`. The binomial random graph is `SimpleGraph.binomialRandom`. The Banach fixed-point theorem is in `ContractingWith`. Circulant matrices are `Matrix.circulant`. TauCeti declarations are in `TauCeti`, `TauCeti.Probability`, `TauCeti.DenseGraphLimits` (graphons and exchangeable random graphs), and `Matrix.PosSemidef` (Kolmogorov feature maps and kernel mean embeddings), with network specifications in `TauCeti.Neuromanifold`, the Moore–Penrose inverse in `LinearMap`, and Bernstein's inequality in `ProbabilityTheory.iIndepFun`. Statlib declarations cited here are in `ProbabilityTheory` (the binary Bayes test, the Jensen–Shannon divergence, mutual information, integral forms of the total variation distance, the Bretagnolle–Huber inequality, and divergence identities at stopping times); its contiguity predicates `Contiguous1`–`Contiguous5` are in the root namespace.

None of the three libraries has a notion of a learning rule, of a hypothesis class with its risk, of a sequential policy, of a Markov decision process, or of a differentially private mechanism. Almost all of this section is therefore not covered. What is recorded below is the probabilistic, information-theoretic, and linear-algebraic infrastructure on which the statements would be built, together with the few results, chiefly on exchangeable random graphs, Gaussian conditioning, and the binary Bayes test, that reach a numbered entry.

<a id="structure-107a"></a>

## 107A. Learning Theory, Probabilistic Models, Deep Learning, and Networks

This subdivision covers generalization bounds, classification targets, kernel and nearest-neighbour methods, ensembles and graphical models, neural-network approximation and training, and network data. The libraries supply concentration inequalities, the VC dimension of finite set families, reproducing-kernel Hilbert spaces, the Kullback–Leibler and Jensen–Shannon divergences, the Bayes test between two laws, Gaussian conditioning, specifications of multilayer perceptrons, contiguity, and a substantial theory of graphons and exchangeable random graphs. Apart from the Bayes rule of item 8, no learning-theoretic statement as such is formalized.

### Statistical learning theory

[Mathematical scope](SYNOPSIS107.md#statistical-learning-theory).

#### Mathlib

**VC dimension.** Shattering and the VC dimension of a finite family of finite sets are defined (`Finset.shatterer`, `Finset.vcDim`, `Combinatorics/SetFamily/Shatter.lean`), and the Sauer–Shelah bound is proved (`Finset.card_shatterer_le_sum_vcDim`); see [CKMA Structure 07](../lean-CKMA/STRUCTURE07.md). This is the combinatorial input to item 1, but there is no notion of a classification rule, of PAC learnability, or of sample complexity. The uniform deviation bound for VC classes, CKMA SYNOPSIS07 item 37, is not formalized.

**Hoeffding inequalities.** Hoeffding's lemma (`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc`) and the tail bound for sums of independent sub-Gaussian variables (`ProbabilityTheory.measure_sum_ge_le_of_iIndepFun`, `Probability/Moments/SubGaussian.lean`) give the deviation bound for a single bounded loss. These are supporting material for items 1, 2, and 15.

**Convex projection.** In a real inner product space the nearest point of a nonempty complete convex set exists and is characterized by the variational inequality \(\langle u-v,w-v\rangle\le0\) (`exists_norm_eq_iInf_of_complete_convex`, `norm_eq_iInf_iff_real_inner_le_zero`, `Analysis/InnerProductSpace/Projection/Minimal.lean`). This is the nonexpansive projection step of online gradient descent, item 4; the regret bound is not stated.

**Reproducing kernels.** Vector-valued reproducing-kernel Hilbert spaces are the class `RKHS` (`Analysis/InnerProductSpace/Reproducing.lean`). The kernel of such a space is positive semidefinite (`RKHS.posSemidef_kernel`), and every positive semidefinite kernel is the kernel of the space `RKHS.OfKernel` (`RKHS.kernel_ofKernel`, Moore's theorem). This is supporting material for item 3; the Rademacher complexity is not defined.

#### TauCeti

The Rademacher law on \(\mathbb R\), with its moments and transforms, is defined ([Rademacher](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/Distributions/Rademacher/Basic.lean), `TauCeti.Probability.rademacherMeasure`). McDiarmid's bounded-differences theorem is proved for finite products of a probability space ([McDiarmid](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/McDiarmid.lean), `TauCeti.Probability.hasSubgaussianMGF_of_bounded_differences`). It is the concentration step in the high-probability parts of item 2; symmetrization and the expected-supremum bound are not stated. Empirical measures of finite samples are defined ([empirical measures](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/Process/EmpiricalMeasure.lean), `TauCeti.Probability.empiricalMeasure`), without uniform deviation bounds.

For a scalar positive-definite kernel, the Kolmogorov feature map \(\Phi\) with \(\langle\Phi(a),\Phi(b)\rangle=K(a,b)\) is constructed through Mathlib's `RKHS.OfKernel` ([Kolmogorov decomposition](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Analysis/PositiveDefinite/Kernel/Kolmogorov.lean), `Matrix.PosSemidef.kolmogorovFeature`, `Matrix.PosSemidef.inner_kolmogorovFeature`). With the Cauchy–Schwarz inequality this feature map is the starting point for item 3.

Exchangeability of a sequence of random variables is defined ([exchangeability](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/Exchangeability/Basic.lean), `TauCeti.Probability.Exchangeable`), with de Finetti's theorem; see [CKMA Structure 06](../lean-CKMA/STRUCTURE06.md). The rank argument behind split conformal prediction, item 6, is not stated.

#### Statlib

No relevant declarations were found.

**Synopsis entries.** Not covered: 107.1–107.7.

### Statistical targets in classification

[Mathematical scope](SYNOPSIS107.md#statistical-targets-in-classification).

#### Mathlib

Conditional expectation, and hence the regression function \(\eta(x)=P(Y=1\mid X=x)\) as an almost-everywhere-defined function, is available ([CKMA Structure 06](../lean-CKMA/STRUCTURE06.md)). For a two-point prior \(\pi\) on \(\{0,1\}\) and laws \(\mu,\nu\), the posterior weight of \(1\) is \(\pi\{1\}\,d\nu/dP\) almost everywhere, where \(P\) is the marginal law of the observation (`ProbabilityTheory.posterior_boolKernel_apply_true`, `Probability/Kernel/Posterior.lean`), and argmin estimators are Bayes estimators (`ProbabilityTheory.IsArgminEstimator.isBayesEstimator`, `Probability/Decision/BayesEstimator.lean`). Neither the Bayes classifier nor the excess-risk identity is stated.

#### TauCeti

No relevant declarations were found.

#### Statlib

**Bayes test between two laws.** For finite measures \(\mu,\nu\) and a finite prior \(\pi\) on \(\{0,1\}\), the test `ProbabilityTheory.binaryArgminEstimator μ ν π` chooses \(\nu\) exactly where \(\pi\{0\}\,d\mu/dP\le\pi\{1\}\,d\nu/dP\), and it is an argmin, hence Bayes, estimator for the \(0\)–\(1\) loss (`ProbabilityTheory.isArgminEstimator_binaryArgminEstimator`, [binary tests](https://github.com/stat-lib/statlib/blob/eeaac0283690efaa60c31115400cf561836baeb9/Statlib/Testing/Binary.lean)). With \(\mu,\nu\) the conditional laws of \(X\) given \(Y=0\) and \(Y=1\) and \(\pi\) the law of \(Y\), the two sides are \(1-\eta\) and \(\eta\), so this is the rule \(1_{\{\eta\ge1/2\}}\) in likelihood-ratio form. Its Bayes risk is \(\int\min(\pi\{0\}\,d\mu/dP,\pi\{1\}\,d\nu/dP)\,dP=\mathbb E\min(\eta(X),1-\eta(X))\) (`ProbabilityTheory.bayesBinaryRisk_eq_lintegral_min`, `ProbabilityTheory.toReal_bayesBinaryRisk_eq_integral_abs`). The excess-risk identity for an arbitrary classifier, the plug-in bound, and the margin bound are not stated.

**Synopsis entries.** Partly covered: 107.8 (the Bayes rule \(1_{\{\eta\ge1/2\}}\) in likelihood-ratio form, with Bayes risk \(\mathbb E\min(\eta,1-\eta)\), in Statlib; the excess-risk identity, the plug-in bound, and the margin bound are not stated). Not covered: 107.9.

### Margins, surrogate losses, and stability

[Mathematical scope](SYNOPSIS107.md#margins-surrogate-losses-and-stability).

#### Mathlib

No margin bound, surrogate-risk comparison, or stability notion is stated. The concentration ingredients are those listed under statistical learning theory.

#### TauCeti

McDiarmid's inequality, recorded above, is the concentration step in the proof of item 12; uniform stability is not defined.

#### Statlib

No relevant declarations were found.

**Synopsis entries.** Not covered: 107.10–107.12.

### Kernel regression, nearest neighbours, and data splitting

[Mathematical scope](SYNOPSIS107.md#kernel-regression-nearest-neighbours-and-data-splitting).

#### Mathlib

For hold-out selection, item 15, Hoeffding's inequality for independent bounded summands (`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc`, `ProbabilityTheory.measure_sum_ge_le_of_iIndepFun`) applies to the hold-out error frequency of each fixed candidate, and the finite union bound is `measure_iUnion_fintype_le` (`MeasureTheory/OuterMeasure/Basic.lean`). The selection inequality obtained by combining them is not stated, and neither is the conditioning on the training part. Kernel ridge regression, its critical-radius rate, and nearest-neighbour rules are absent.

#### TauCeti

No relevant declarations were found.

#### Statlib

No relevant declarations were found.

**Synopsis entries.** Not covered: 107.13, 107.14, 107.15 (ingredients only: Hoeffding's bound for each fixed candidate and the union bound; the selection inequality is not stated).

### Foundations, probabilistic modelling, and ensembles

[Mathematical scope](SYNOPSIS107.md#foundations-probabilistic-modelling-and-ensembles).

#### Mathlib

The Hausdorff distance between subsets of a metric space is `Metric.hausdorffDist` (`Topology/MetricSpace/HausdorffDistance.lean`). This is the metric of item 16; the \(k\)-means criterion and its consistency are absent. Trees in simple graphs are `SimpleGraph.IsTree` (`Combinatorics/SimpleGraph/Acyclic.lean`), but binary decision trees, pruning, boosting, belief propagation, and forests are not formalized.

#### TauCeti

The identification of the Gaussian-process posterior mean with kernel ridge regression and simple kriging, in the preamble, rests on the Gaussian conditioning formula recorded under item 34 below.

#### Statlib

No relevant declarations were found.

**Synopsis entries.** Not covered: 107.16–107.20.

### Prediction losses and ensemble structure

[Mathematical scope](SYNOPSIS107.md#prediction-losses-and-ensemble-structure).

#### Mathlib

**Divergence and logarithmic loss.** The Kullback–Leibler divergence of finite measures is `InformationTheory.klDiv`, valued in \([0,\infty]\), and it vanishes exactly when the two finite measures are equal (`InformationTheory.klDiv_eq_zero_iff`, `InformationTheory/KullbackLeibler/Basic.lean`). This is Gibbs' inequality, so a reported distribution \(q\) minimizes \(D(p\|q)\) only at \(q=p\). The decomposition of the expected logarithmic loss into entropy plus divergence, and the Brier-score identity, are not stated; Mathlib has no Shannon entropy of a finite distribution beyond the binary and \(q\)-ary entropy functions (`Analysis/SpecialFunctions/BinaryEntropy.lean`).

**Variance of a sum.** For square-integrable real random variables on a finite measure space, the variance of a finite sum is the double sum of covariances (`ProbabilityTheory.variance_sum`, `Probability/Moments/Variance.lean`), and covariance is bilinear (`ProbabilityTheory.covariance_sum_left`, `ProbabilityTheory.covariance_sum_sum`, `Probability/Moments/Covariance.lean`). With equal variances \(\sigma^2\) and equal pairwise correlations \(\rho\), the double sum is \(B\sigma^2+B(B-1)\rho\sigma^2\). Item 22 is this computation divided by \(B^2\), which is not stated.

#### TauCeti

For finite measures on a finite space, the divergence is written as a finite sum, \(\sum_x\mu\{x\}\log(\mu\{x\}/\nu\{x\})\) up to the mass correction ([finite divergence](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/InformationTheory/KullbackLeibler/Finite.lean), `TauCeti.klDiv_eq_ofReal_sum_log_singleton`). This is the form needed in item 21.

#### Statlib

No relevant declarations were found; Statlib has no Shannon entropy of a finite distribution. Exact belief propagation on trees, item 23, is not formalized in any of the three libraries.

**Synopsis entries.** Not covered: 107.21 (ingredients only: Gibbs' inequality, and the finite-sum form of the divergence in TauCeti; the cross-entropy decomposition and the Brier identity are not stated), 107.22 (ingredients only: the variance of a sum as a double sum of covariances; the equicorrelated specialization is not stated), 107.23.

### Boosting and tree splitting

[Mathematical scope](SYNOPSIS107.md#boosting-and-tree-splitting).

#### Mathlib

Strict concavity of \(x\mapsto-x\log x\) on \([0,\infty)\) (`Real.strictConcaveOn_negMulLog`, `Analysis/SpecialFunctions/Log/NegMulLog.lean`) and of the binary entropy on \([0,1]\) (`Real.strictConcave_binEntropy`, `Analysis/SpecialFunctions/BinaryEntropy.lean`) are proved. Since the parent proportions are \(p(\cdot\mid t)=p_Lp(\cdot\mid t_L)+p_Rp(\cdot\mid t_R)\), the first assertion of item 25 is the defining inequality of `StrictConcaveOn` applied to this two-point combination. The impurity-function axioms and Breiman's ordering theorem for categorical splits are not formalized. AdaBoost is absent.

#### TauCeti

No relevant declarations were found.

#### Statlib

No relevant declarations were found.

**Synopsis entries.** Not covered: 107.24, 107.25 (ingredients only: the nonnegativity and equality case are the definition of strict concavity, with strict concavity of the entropy summands proved; the ordering theorem for categorical predictors is not stated).

### Variational and exact inference

[Mathematical scope](SYNOPSIS107.md#variational-and-exact-inference).

#### Mathlib

For a real random variable, the derivative of the cumulant-generating function at an interior point of the exponential-integrability set is the mean under the exponentially tilted law, and its second derivative is the tilted variance (`ProbabilityTheory.deriv_cgf`, `ProbabilityTheory.iteratedDeriv_two_cgf`, `Probability/Moments/MGFAnalytic.lean`). This is the one-parameter case of the gradient map \(\nabla A\) in item 26. Multiparameter exponential families, the mean-parameter set, and the conjugate-duality representation are not formalized. Chordal graphs, junction trees, and the construction of the unique Markov extension from normalized compatible clique and separator tables are absent.

#### TauCeti

No relevant declarations were found. The Legendre-type duality in TauCeti's optimal-transport files (\(c\)-transforms) is a different construction.

#### Statlib

No relevant declarations were found.

**Synopsis entries.** Not covered: 107.26, 107.27.

### Deep learning: architectures, approximation, and training

[Mathematical scope](SYNOPSIS107.md#deep-learning-architectures-approximation-and-training).

#### Mathlib

The Fourier transform of functions on a finite-dimensional real inner product space is the instance `Real.instFourierTransform`, with integral formula `Real.fourier_eq` (`Analysis/Fourier/FourierTransform.lean`), the analytic input to Barron's spectral norm in item 28. The approximation target is the continuous representative determined by Fourier inversion, also for sampling laws singular with respect to Lebesgue measure. Neural networks, Hölder compositional classes, the neural tangent kernel, and the Jensen–Shannon divergence are not defined. The density of one-hidden-layer networks, CKMA SYNOPSIS47 item 76, is recorded as not covered in [CKMA Structure 47](../lean-CKMA/STRUCTURE47.md).

#### TauCeti

**Inverse-Wishart mean.** For a positive-definite scale \(S\) of size \(p\) and degree \(n>p+1\), the inverse-Wishart law has mean \((n-p-1)^{-1}S\); in positive dimension the identity is not integrable for \(p-1<n\le p+1\) ([inverse-Wishart moments](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/Distributions/Wishart/Inverse/Moments.lean), `TauCeti.Probability.integral_id_inverseWishartMeasure`, `TauCeti.Probability.not_integrable_id_inverseWishartMeasure`). The inverse-Wishart law is defined as the image of the nonsingular Wishart law with inverted scale under matrix inversion. The Gram matrix of independent centred Gaussian rows has the Wishart law ([Wishart agreement](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/Distributions/Wishart/Agreement.lean), `TauCeti.Probability.hasLaw_wishartGram_gaussian_nonsingularWishartMeasure`). Together these give \(\mathbb E(X^\top X)^{-1}=I/(n-p-1)\) for an isotropic Gaussian design, which is the moment behind the underparameterized formula \(\sigma^2p/(n-p-1)\) in item 31. A Wishart matrix of degree \(\nu\) with positive semidefinite scale \(S\) has rank \(\min(\nu,\mathop{\mathrm{rank}}S)\) almost surely ([Wishart rank](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/Distributions/Wishart/Rank.lean), `TauCeti.Probability.ae_rank_eq_wishartGramMeasure`), so a Gaussian design has full rank almost surely. The risk formula itself, the overparameterized case, and the limits are not stated.

**Network specifications (supporting).** A multilayer perceptron specification records widths \(d_0,\ldots,d_L\) and one scalar activation for each hidden layer. Its realization alternates affine maps with coordinatewise activations, and the output layer is affine (`TauCeti.Neuromanifold.MLPSpec`, `TauCeti.Neuromanifold.MLPSpec.realize`, [MLP specifications](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Geometry/Neuromanifold/MLP/Basic.lean)). This is the feedforward network of the synopsis. The set of functions realized by a parametric model is `TauCeti.Neuromanifold.realizedFunctions` ([realized functions](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Geometry/Neuromanifold/Basic.lean)), and dense and one-dimensional convolutional layers are set up in the same framework. No approximation, capacity, or training theorem is stated for these networks.

#### Statlib

The Jensen–Shannon divergence of weight \(\alpha\), \(\alpha D(\mu\|\alpha\mu+(1-\alpha)\nu)+(1-\alpha)D(\nu\|\alpha\mu+(1-\alpha)\nu)\) with natural logarithms, is defined as an \(f\)-divergence (`ProbabilityTheory.jensenShannon`, [Jensen–Shannon](https://github.com/stat-lib/statlib/blob/eeaac0283690efaa60c31115400cf561836baeb9/Statlib/Divergence/JensenShannon/Basic.lean)); for \(\alpha=1/2\) it is the \(\mathop{\mathrm{JSD}}\) of item 32. For \(0<\alpha<1\) it vanishes on two finite measures exactly when they are equal (`ProbabilityTheory.jensenShannon_eq_zero_iff`). For probability measures it is the infimum over probability measures \(\xi\) of \(\alpha D(\mu\|\xi)+(1-\alpha)D(\nu\|\xi)\) (`ProbabilityTheory.jensenShannon_eq_iInf_klDiv`, [variational form](https://github.com/stat-lib/statlib/blob/eeaac0283690efaa60c31115400cf561836baeb9/Statlib/Divergence/JensenShannon/Variational.lean)). These give the equality case of item 32 once the value identity is known; the optimal discriminator and the identity \(-\log4+2\mathop{\mathrm{JSD}}(p,p_g)\) are not stated.

The minimax lower bound in item 29 uses a nonnegative extended-real risk for arbitrary measurable estimators, including those with infinite risk. No such compositional-class bound is stated.

**Synopsis entries.** Not covered: 107.28–107.30, 107.31 (ingredients only: the inverse-Wishart mean and the Wishart law of a Gaussian Gram matrix, in TauCeti, which give the key moment of the case \(n>p+1\); the risk identities are not stated), 107.32 (ingredients only: the Jensen–Shannon divergence with its vanishing criterion, in Statlib; the optimal discriminator and the value identity are not stated).

### Probabilistic output layers and kernel prediction

[Mathematical scope](SYNOPSIS107.md#probabilistic-output-layers-and-kernel-prediction).

#### Mathlib

The multivariate Gaussian law with mean \(m\) and positive semidefinite covariance \(S\) is `ProbabilityTheory.multivariateGaussian` (`Probability/Distributions/Gaussian/Multivariate.lean`). Softmax, the log-sum-exp function, and its Hessian are not defined. The scalar cumulant derivatives recorded under item 26 are the one-dimensional analogue of the gradient identity in item 33.

#### TauCeti

**Gaussian conditioning.** Let \(X\) be a Gaussian vector indexed by \(\iota\sqcup\kappa\) with mean \(m\) and positive semidefinite covariance \(S\), whose observed block \(S_{22}\) is positive definite. Then the regular conditional law of the first block given the second is, almost everywhere, Gaussian with mean \(m_1+S_{12}S_{22}^{-1}(x_2-m_2)\) and covariance given by the Schur complement \(S_{11}-S_{12}S_{22}^{-1}S_{21}\) ([conditional Gaussian](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/Distributions/Gaussian/Conditional/Basic.lean), `TauCeti.Probability.condDistrib_multivariateGaussian`, `EuclideanSpace.gaussianCondMean`, `Matrix.gaussianCondCov`). For the joint law of \((f(x),f(x'),y_1,\ldots,y_n)\) the observed block is \(K+\sigma^2I\), positive definite when \(\sigma^2>0\), so this formula gives the posterior mean and covariance of item 34 at finitely many test points. A Gaussian process indexed by an arbitrary set, the predictive variance of a new response, and the identification with kernel ridge regression are not stated.

The kernel mean embedding of a measure into the Kolmogorov space of a positive-definite kernel is defined, with \(\|m_\mu-m_\nu\|^2\) equal to the kernel energy of \(\mu-\nu\) ([mean embeddings](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Analysis/PositiveDefinite/Kernel/MeanEmbedding.lean), `Matrix.PosSemidef.kernelMeanEmbedding`, `Matrix.PosSemidef.norm_kernelMeanEmbedding_sub_sq`); this is supporting material.

**Softmax derivative.** In the logistic-normal files, the softmax chart \(z\mapsto\bigl(e^{z_j}/(1+\sum_ke^{z_k})\bigr)_j\), with the logit of the reference category fixed at zero, has derivative \(\mathop{\mathrm{diag}}(p)-pp^\top\) at a point with value \(p\) ([logistic-normal chart](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/Distributions/LogisticNormal/PDF.lean), `TauCeti.Probability.hasFDerivAt_logisticNormalChart_coords`). This is the Hessian of item 33 in reduced coordinates, obtained as the derivative of softmax. The shift identity \(\log\sum_ie^{f_i}=c+\log\sum_ie^{f_i-c}\) is also proved ([log-sum-exp](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Analysis/SpecialFunctions/Log/SumExp.lean), `Finset.log_sum_exp_eq_add_log_sum_exp_sub`). The gradient \(q-y\) of the logarithmic loss and the Hessian of log-sum-exp in all \(K\) coordinates are not stated.

#### Statlib

No relevant declarations were found.

**Synopsis entries.** Partly covered: 107.34 (block Gaussian conditioning with a positive definite observed block, in TauCeti; the Gaussian-process formulation and the kernel ridge identification are not stated). Not covered: 107.33 (ingredients only: the derivative \(\mathop{\mathrm{diag}}(p)-pp^\top\) of the softmax chart in reduced coordinates, in TauCeti; the gradient of the logarithmic loss and the Hessian of log-sum-exp are not stated).

### Capacity, depth, and symmetry

[Mathematical scope](SYNOPSIS107.md#capacity-depth-and-symmetry).

#### Mathlib

**Circulant matrices.** The circulant matrix of a vector \(v\) indexed by an additive group has entries \(v(i-j)\) (`Matrix.circulant`, `LinearAlgebra/Matrix/Circulant.lean`). Products of circulant matrices are circulant (`Matrix.circulant_mul`), and over a commutative ring any two circulant matrices commute (`Matrix.circulant_mul_comm`). Since the cyclic shift is the circulant matrix of a unit vector (`Matrix.circulant_single`), every circulant matrix commutes with the shift. The converse, that a matrix commuting with the shift is circulant, is not stated. The discrete Fourier transform on \(\mathbb Z/N\mathbb Z\) is defined, with its inversion formula (`ZMod.dft`, `ZMod.dft_dft`, `Analysis/Fourier/ZMod.lean`), but the diagonalization of circulant matrices by it is not stated.

The characterization of permutation-equivariant linear maps, the equivariance of self-attention, VC bounds for network classes, and approximation rates for ReLU networks are absent.

#### TauCeti

Hidden-neuron symmetries of multilayer perceptrons are defined on bias-free weights. Relabelling the neurons of a hidden layer by a permutation preserves the realization for every activation, and rescaling them by units preserves it when the activation of that layer is \(t\mapsto t^e\) (`TauCeti.Neuromanifold.MLPSpec.permuteHidden`, `TauCeti.Neuromanifold.MLPSpec.realizeWeights_permuteHidden`, `TauCeti.Neuromanifold.MLPSpec.scaleHidden`, `TauCeti.Neuromanifold.MLPSpec.hiddenSymmetrySetoid`, [MLP symmetries](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Geometry/Neuromanifold/MLP/Symmetry.lean)). These are symmetries of the parameter space, not equivariance of the realized map under permutations of the input rows. The VC and Rademacher bounds of item 35, approximation rates, and depth separation are not stated.

#### Statlib

No relevant declarations were found.

**Synopsis entries.** Partly covered: 107.38 (circulant matrices commute with each other, hence with the shift, in Mathlib; the converse, Fourier diagonalization, the permutation-equivariant layers, and self-attention are not stated). Not covered: 107.35–107.37.

### Random initialization and implicit bias

[Mathematical scope](SYNOPSIS107.md#random-initialization-and-implicit-bias).

#### Mathlib

No relevant declarations were found. Mathlib has no Moore–Penrose pseudoinverse of a real matrix and no convergence theorem for gradient descent.

#### TauCeti

The Moore–Penrose inverse of a linear map between finite-dimensional inner product spaces is constructed from its singular system, and it is the unique map satisfying the four Penrose equations (`LinearMap.moorePenroseInverse`, `LinearMap.IsMoorePenroseInverse`, `LinearMap.isMoorePenroseInverse_iff_eq_moorePenroseInverse`, [Moore–Penrose inverse](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Analysis/InnerProductSpace/MoorePenrose.lean)). Matrices satisfying the Penrose equations give the same relation for the associated Euclidean maps (`Matrix.isMoorePenroseInverse_toEuclideanLin_of_penrose`). This is the limit object \(X^+y+(I-X^+X)\theta_0\) of item 40; the convergence of gradient descent and the implicit bias for the logistic loss are not stated. No Gaussian-process limit of wide networks appears.

#### Statlib

No relevant declarations were found.

**Synopsis entries.** Not covered: 107.39, 107.40 (ingredients only: the Moore–Penrose inverse, in TauCeti; the convergence of gradient descent and the logistic implicit bias are not stated).

### Networks and graph representation learning

[Mathematical scope](SYNOPSIS107.md#networks-and-graph-representation-learning).

#### Mathlib

The binomial random graph \(G(V,p)\) on a vertex type \(V\), with independent edges of probability \(p\in[0,1]\), is `SimpleGraph.binomialRandom`. On a finite vertex type a graph \(G\) has probability \(p^{|E(G)|}(1-p)^{\binom{|V|}2-|E(G)|}\) (`SimpleGraph.binomialRandom_singleton`, `Probability/Combinatorics/BinomialRandomGraph/Defs.lean`). Stochastic block models, recovery thresholds, contiguity, and Weisfeiler–Leman refinement are not formalized.

#### TauCeti

**Graphons and exchangeable random graphs.** A graphon on a probability space \((\Omega,\mu)\) is a symmetric measurable kernel with values in \([0,1]\) (`TauCeti.DenseGraphLimits.Graphon`). Graphons on the unit interval modulo cut distance zero form the compact metric space `TauCeti.DenseGraphLimits.GraphonSpaceI` ([graphons](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Combinatorics/DenseGraphLimits/Graphon/Basic.lean), [compactness](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Combinatorics/DenseGraphLimits/GraphonSpace/Compact.lean)). An exchangeable random graph on \(\mathbb N\) is a probability law on `SimpleGraph ℕ` invariant under relabelling by every permutation of \(\mathbb N\) (`TauCeti.DenseGraphLimits.InfiniteExchangeableGraphLaw`, [infinite exchangeable laws](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Combinatorics/DenseGraphLimits/ExchangeableGraphLaw/Infinite/Basic.lean)).

The graphon form of the Aldous–Hoover theorem, in the version of Diaconis and Janson, is proved. Every exchangeable law on infinite graphs is the integral, against exactly one probability measure on `GraphonSpaceI`, of the laws of the graphon model: draw independent uniform latent variables and include each edge independently with probability \(W(U_i,U_j)\) ([mixture representation](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Combinatorics/DenseGraphLimits/ExchangeableGraphLaw/Infinite/Mixture.lean), `TauCeti.DenseGraphLimits.InfiniteExchangeableGraphLaw.existsUnique_bind_infiniteSampleLawOnSpace`, `TauCeti.DenseGraphLimits.graphonMixtureLawEquiv_law`). Two graphons, on arbitrary probability spaces, at cut distance zero have the same finite sampling laws (`TauCeti.DenseGraphLimits.sampleGraph_eq_of_cutDist_eq_zero`). Conversely, equal sampling laws give equal homomorphism densities, and equal homomorphism densities force cut distance zero ([separation](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Combinatorics/DenseGraphLimits/Separation/Inverse.lean), `TauCeti.DenseGraphLimits.cutDist_eq_zero_iff_forall_homDensity_eq_cross`). On standard Borel carriers the cut distance equals the infimum, over pairs of measure-preserving maps from the unit interval, of the cut norm of the difference of the pullbacks ([map form of the cut distance](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Combinatorics/DenseGraphLimits/CutMetric/Pullback/Basic.lean), `TauCeti.DenseGraphLimits.cutDist_eq_cutDistPullback`).

The two formal statements differ from the synopsis in two places. Exchangeability is assumed under all permutations of \(\mathbb N\), not only finite ones; the two hypotheses are equivalent because a law on `SimpleGraph ℕ` is determined by its finite windows, but this equivalence is not stated. The uniqueness is up to cut distance zero, expressed as an infimum over pullbacks. The characterization of weak isomorphism by pullbacks that agree almost everywhere, with the infimum attained, is not stated. TauCeti also proves a decomposition of exchangeable array laws into dissociated components, a step towards the general Aldous–Hoover representation ([array decomposition](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/Exchangeability/Arrays/AldousHoover/Decomposition.lean)). An exchangeable law on infinite graphs is dissociated exactly when the action of finitary permutations on its relational law is ergodic ([ergodic laws](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Combinatorics/DenseGraphLimits/ExchangeableGraphLaw/Relational/Ergodic.lean), `TauCeti.DenseGraphLimits.isDissociated_iff_ergodicSMul_toRelationalLaw`); this is supporting material.

#### Statlib

**Contiguity.** For families of probability measures indexed along a filter, contiguity of \(Q\) with respect to \(P\) is defined in five forms ([contiguity](https://github.com/stat-lib/statlib/blob/eeaac0283690efaa60c31115400cf561836baeb9/Statlib/Contiguity/Def.lean)). The form `Contiguous5` is the sequential one of the synopsis: \(P(A_n)\to0\) implies \(Q(A_n)\to0\) for measurable events. `Contiguous1` requires the same along every finer filter, `Contiguous4` transfers convergence in probability to zero from \(P\) to \(Q\), and `Contiguous2` and `Contiguous3` are stated through weak limits of likelihood-ratio laws. Only `contiguous1_iff_contiguous4` and `Contiguous1.contiguous5` are proved; the remaining equivalences, including Le Cam's first lemma, are recorded as open in the source. Mutual contiguity in item 42 is the conjunction of the two directions. No statement about graph laws is made.

**Synopsis entries.** Partly covered: 107.43 (the mixture representation and the uniqueness of the mixing measure up to cut distance zero, in TauCeti; invariance is assumed under all permutations, and weak isomorphism by almost-everywhere equal pullbacks is not stated). Not covered: 107.41, 107.42 (ingredients only: the definition of contiguity, in Statlib; the Kesten–Stigum threshold and the contiguity of the block model with the Erdős–Rényi graph are not stated), 107.44.

### Symmetry and graph signal

[Mathematical scope](SYNOPSIS107.md#symmetry-and-graph-signal).

#### Mathlib

The adjacency matrix of a simple graph is `SimpleGraph.adjMatrix` (`Combinatorics/SimpleGraph/AdjMatrix.lean`), and Hermitian matrices have the spectral theorem (`Matrix.IsHermitian.eigenvalues`; see [CKMA Structure 13](../lean-CKMA/STRUCTURE13.md)). The eigenstructure of the block-model expectation and the permutation equivariance of message passing are not stated.

#### TauCeti

No relevant declarations were found.

#### Statlib

No relevant declarations were found.

**Synopsis entries.** Not covered: 107.45, 107.46.

### Random graphs and spectral recovery

[Mathematical scope](SYNOPSIS107.md#random-graphs-and-spectral-recovery).

#### Mathlib

The binomial random graph is defined, as recorded above. The phase transition, the giant component, and the connectivity threshold are absent. The Galton–Watson survival probability, CKMA SYNOPSIS06 item 65, is recorded as not covered in [CKMA Structure 06](../lean-CKMA/STRUCTURE06.md).

#### TauCeti

The Davis–Kahan \(\sin\Theta\) theorem is proved in a dimension-free operator-norm form. If \(U\) is invariant under \(A\), \(W\) is invariant under a symmetric \(B\), the quadratic form of \(A\) on \(U\) is at least \(c+g\), and that of \(B\) on \(W\) is at most \(c\), then \(g\|P_WP_U\|\le\|B-A\|\) ([sin Θ](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Analysis/InnerProductSpace/Projection/SinTheta.lean), `Submodule.mul_norm_starProjection_comp_starProjection_le_norm_sub`). Versions in unitarily invariant seminorms are in [CKMA Structure 13](../lean-CKMA/STRUCTURE13.md). This is the deterministic perturbation step of item 48. If the entries of a real \(m\times n\) random matrix are independent and sub-Gaussian with variance proxy \(K^2\), its operator norm exceeds \(8K(\sqrt m+\sqrt n+t)\) with probability at most \(2e^{-t^2}\) ([sub-Gaussian matrices](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/Moments/SubGaussianMatrix.lean), `ProbabilityTheory.iIndepFun.measureReal_matrix_l2_opNorm_gt_le`). The noise matrix \(R\) of item 48 is symmetric, so its entries are independent only on and above the diagonal, and the bound does not apply to it directly. The counting of misclassified vertices, the bound for the symmetric noise matrix, and the matrix Bernstein inequality are not stated.

#### Statlib

No relevant declarations were found.

**Synopsis entries.** Not covered: 107.47, 107.48 (ingredients only: the Davis–Kahan theorem and an operator-norm tail bound for rectangular matrices with independent sub-Gaussian entries, in TauCeti; the misclassification count and the bound for the symmetric noise matrix are not stated).

<a id="structure-107b"></a>

## 107B. Bandits, Reinforcement Learning, Privacy, Fairness, and Distribution Shift

None of the three libraries defines bandit policies, Markov decision processes, value functions, or differential privacy. The relevant infrastructure is the Ionescu–Tulcea construction of laws of processes driven by kernels, the Banach fixed-point theorem, Neumann series, the Kullback–Leibler divergence with its chain rule, tensorization, value at stopping times, and the Pinsker and Bretagnolle–Huber inequalities, Wald's identity, sub-Gaussian and Bernstein concentration, conditional independence, Radon–Nikodym change of measure, the variational form of total variation, and the Laplace and Gaussian laws.

### Bandits and reinforcement learning

[Mathematical scope](SYNOPSIS107.md#bandits-and-reinforcement-learning).

#### Mathlib

**Laws of interaction.** The Ionescu–Tulcea theorem constructs the law of a trajectory from a sequence of kernels, each depending on the history so far (`ProbabilityTheory.Kernel.traj`, `Probability/Kernel/IonescuTulcea/Traj.lean`). This is the construction that turns a policy and an environment into a law on histories, but no bandit or decision-process structure is built on it.

**Divergence.** The chain rule for the Kullback–Leibler divergence of composition products, \(D(\mu\otimes\kappa\|\nu\otimes\eta)=D(\mu\|\nu)+D(\mu\otimes\kappa\|\mu\otimes\eta)\), and the data-processing inequality are proved (`InformationTheory.klDiv_compProd_eq_add`, `InformationTheory/KullbackLeibler/ChainRule.lean`; `InformationTheory.klDiv_map_le`, `InformationTheory/KullbackLeibler/DataProcessing.lean`). These are the divergence-decomposition and change-of-measure steps of the Lai–Robbins lower bound, item 49.

**Contractions.** The Banach fixed-point theorem gives, for a contraction with constant \(K<1\) on a complete metric space, a unique fixed point and the a priori geometric bound for the iterates (`ContractingWith.fixedPoint_isFixedPt`, `ContractingWith.fixedPoint_unique`, `ContractingWith.apriori_dist_iterate_fixedPoint_le`, `Topology/MetricSpace/Contracting.lean`). This is the abstract half of item 53; the Bellman operator and the optimality of greedy policies are not stated. The almost-sure convergence of \(L^1\)-bounded submartingales (`MeasureTheory.Submartingale.ae_tendsto_limitProcess`, `Probability/Martingale/Convergence.lean`) is the starting point for the stochastic-approximation argument of item 54, which is not formalized.

#### TauCeti

The path law of a homogeneous Markov chain is constructed from Mathlib's Ionescu–Tulcea measure, with its finite-dimensional product formula ([Markov chains](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/Process/MarkovChain.lean), `TauCeti.Probability.markovChainLaw`). It supports the Markov bandit of item 51; Gittins indices are absent. The divergence of product measures is the sum of the divergences of the factors ([chain rule](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/InformationTheory/KullbackLeibler/ChainRule.lean), `TauCeti.klDiv_prod_prod`).

#### Statlib

**Sequential sampling.** For an i.i.d. sequence with law \(\mu\) or \(\nu\) and an \(\mathbb N\)-valued stopping time \(\tau\) of its natural filtration, the laws \(\mu_\tau,\nu_\tau\) of the observations up to \(\tau\) satisfy \(D(\mu_\tau\|\nu_\tau)=\mathbb E_\mu[\tau+1]\,D(\mu\|\nu)\) ([divergence at stopping times](https://github.com/stat-lib/statlib/blob/eeaac0283690efaa60c31115400cf561836baeb9/Statlib/Testing/Sequential/KLDiv.lean), `ProbabilityTheory.klDiv_trim_stoppingTime`). Wald's identity holds for an integrable stopping time ([Wald](https://github.com/stat-lib/statlib/blob/eeaac0283690efaa60c31115400cf561836baeb9/Statlib/Testing/Sequential/Wald.lean), `ProbabilityTheory.integral_sum_comp_stoppingTime`). These are the single-arm forms of the divergence decomposition \(\sum_k\mathbb E[N_k]\,\mathop{\mathrm{kl}}(\nu_k,\nu_k')\) behind item 49; the multi-armed decomposition under a policy is not stated. The divergence of a finite product of probability measures is the sum of the divergences of the factors ([tensorization](https://github.com/stat-lib/statlib/blob/eeaac0283690efaa60c31115400cf561836baeb9/Statlib/Divergence/KullbackLeibler/CondKL.lean), `ProbabilityTheory.klDiv_pi`, `ProbabilityTheory.klDiv_pi_const`), which TauCeti proves for two factors.

**Synopsis entries.** Not covered: 107.49 (ingredients only: the chain rule and data-processing inequality for the divergence, in Mathlib, and the divergence of i.i.d. observations up to a stopping time, in Statlib; the bandit model and the lower bound are not stated), 107.50–107.54.

### Policy evaluation and policy-dependent distributions

[Mathematical scope](SYNOPSIS107.md#policy-evaluation-and-policy-dependent-distributions).

#### Mathlib

In a complete normed ring, if \(\|t\|<1\) then \(1-t\) is invertible with inverse \(\sum_{i\ge0}t^i\) (`NormedRing.inverse_one_sub`, `Analysis/Normed/Ring/Units.lean`). Applied to \(t=\gamma P_\pi\) in the supremum norm, this is the Neumann-series identity of item 55. The policy value, policy improvement, the performance-difference identity, and the policy-gradient theorem are not stated.

#### TauCeti

No relevant declarations were found.

#### Statlib

No relevant declarations were found.

**Synopsis entries.** Not covered: 107.55–107.57.

### Optimal policies, planning, and sample complexity

[Mathematical scope](SYNOPSIS107.md#optimal-policies-planning-and-sample-complexity).

#### Mathlib

No relevant declarations were found beyond the contraction and Neumann-series results above. Linear-programming duality for occupancy measures, sample-complexity bounds for the generative model, temporal-difference learning, and natural policy gradient are absent.

#### TauCeti

No relevant declarations were found.

#### Statlib

No relevant declarations were found.

**Synopsis entries.** Not covered: 107.58–107.61.

### Minimax and linear bandits

[Mathematical scope](SYNOPSIS107.md#minimax-and-linear-bandits).

#### Mathlib

The Azuma–Hoeffding estimate for adapted sums with conditionally sub-Gaussian increments is proved (`ProbabilityTheory.measure_sum_ge_le_of_hasCondSubgaussianMGF`, `Probability/Moments/SubGaussian.lean`; see [CKMA Structure 07](../lean-CKMA/STRUCTURE07.md)). This is scalar and has a fixed horizon. The self-normalized vector bound of item 63, which needs the method of mixtures and a maximal inequality uniform in time, is not stated.

#### TauCeti

The Azuma–Hoeffding inequality for bounded martingale differences is derived from a conditional form of Hoeffding's lemma ([Azuma](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/Moments/Azuma.lean), `TauCeti.Probability.hasCondSubgaussianMGF_of_mem_Icc_of_condExp_eq_zero`, `TauCeti.Probability.measureReal_sum_range_ge_le_of_bounded_martingale_differences`). Doob's maximal inequality is extended to finite sets of times and to right-continuous submartingales in continuous time, up to a fixed horizon ([maximal inequality](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/Martingale/MaximalInequality.lean), `MeasureTheory.Submartingale.mul_measure_exists_le_lt_le`). Neither is time-uniform over an infinite horizon, as item 63 requires.

#### Statlib

The Bretagnolle–Huber inequality is proved for probability measures. Statlib's `tvDist` of probability laws is twice \(\|P-Q\|_{\mathrm{TV}}\), so the statements read \(-\log(1-\|P-Q\|_{\mathrm{TV}}^2)\le D(P\|Q)\) and, when the divergence is finite, \(e^{-D(P\|Q)}\le2-2\|P-Q\|_{\mathrm{TV}}\) ([Bretagnolle–Huber](https://github.com/stat-lib/statlib/blob/eeaac0283690efaa60c31115400cf561836baeb9/Statlib/Divergence/BretagnolleHuber.lean), `ProbabilityTheory.neg_log_one_sub_tvDist_div_two_sq_le_klDiv`, `ProbabilityTheory.exp_neg_klDiv_le_two_sub_tvDist`). Hence the two error probabilities of any test sum to at least \(\frac12e^{-D(P\|Q)}\). With the tensorization recorded above this is the two-point step of the lower bound in item 62; the bandit instances and the divergence decomposition under a policy are not stated.

Item 63 allows arbitrary positive noise scale and uses the effective regret scale \(\max\{\sigma,BW\}\), which controls initial exploration. The corresponding confidence and regret statements remain absent.

**Synopsis entries.** Not covered: 107.62 (ingredients only: the Bretagnolle–Huber inequality and tensorization of the divergence, in Statlib; the bandit lower-bound construction and the UCB1 bound are not stated), 107.63 (ingredients only: the Azuma–Hoeffding inequality, in Mathlib and TauCeti; the self-normalized bound and the LinUCB regret bounds are not stated).

### Privacy, fairness, and distribution shift

[Mathematical scope](SYNOPSIS107.md#privacy-fairness-and-distribution-shift).

#### Mathlib

**Change of measure.** If \(\mu\ll\nu\), then \(\int(d\mu/d\nu)\,f\,d\nu=\int f\,d\mu\) (`MeasureTheory.integral_rnDeriv_smul`, `MeasureTheory/Measure/Decomposition/RadonNikodym.lean`). Under covariate shift the target joint law has density \(w(x)=dP_T^X/dP_S^X\) with respect to the source joint law. With this density the identity is the importance-weighting formula \(R_T(f)=\mathbb E_S[w(X)L(Y,f(X))]\) of item 68, but the passage from the marginal density ratio to the joint density is not stated. The \(\mathcal H\Delta\mathcal H\) bound is absent.

**Conditional independence.** Conditional independence of random variables given a σ-algebra is `ProbabilityTheory.CondIndepFun` (`Probability/Independence/Conditional.lean`). The fairness criteria of items 67 and 76 can be expressed with it, but no incompatibility theorem is stated.

#### TauCeti

The Laplace law with location \(\mu\) and scale \(b>0\), with density \((2b)^{-1}e^{-|x-\mu|/b}\), is defined and identified as a density law. Its distribution function, moments, and transforms are computed, and translation shifts the location ([Laplace law](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/Distributions/Laplace/Basic.lean), `TauCeti.Probability.laplaceMeasure`, `TauCeti.Probability.laplaceMeasure_map_add_const`). This is the noise law of item 64. The density-ratio bound \(e^{|a-a'|/b}\) between two translates, which is the core of the Laplace mechanism, is not stated.

#### Statlib

For finite measures, \(\int f\,d\mu-\int f\,d\nu\le\) `tvDist μ ν` whenever \(|f|\le1\), and `tvDist μ ν` is the supremum of these differences over measurable \(f\) with \(|f|\le1\) ([integral forms of total variation](https://github.com/stat-lib/statlib/blob/eeaac0283690efaa60c31115400cf561836baeb9/Statlib/Divergence/TotalVariation/Integral.lean), `ProbabilityTheory.integral_sub_integral_le_tvDist`, `ProbabilityTheory.tvDist_eq_iSup_integral_sub`). Applied to \(2\cdot1_{\{h\ne h'\}}-1\) this bounds \(d_{\mathcal H\Delta\mathcal H}(P,Q)\) by `tvDist P Q`, twice \(\|P-Q\|_{\mathrm{TV}}\) for probability laws, which is supporting material for item 68; the domain-adaptation inequality is not stated.

**Synopsis entries.** Not covered: 107.64–107.67, 107.68 (ingredients only: the change-of-measure identity behind importance weighting; the joint density under covariate shift and the \(\mathcal H\Delta\mathcal H\) bound are not stated).

### Privacy mechanisms and weighted inference

[Mathematical scope](SYNOPSIS107.md#privacy-mechanisms-and-weighted-inference).

#### Mathlib

The Gaussian law on \(\mathbb R\) and multivariate Gaussian laws are available ([CKMA Structure 06](../lean-CKMA/STRUCTURE06.md)), as is the Bernoulli law. None of the privacy mechanisms is stated. Mathlib states no Bernstein inequality; its Hoeffding inequality gives only the weaker bound \(B\sqrt{\log(2/\delta)/(2n)}\) for item 73.

#### TauCeti

**Bernstein's inequality.** Let \(X_i\), \(i\in s\), be independent with mean zero, finite second moments, and \(X_i\le b\) almost surely, and let \(v=\sum_i\mathbb EX_i^2\). Then \(P(\sum_iX_i\ge\varepsilon)\le\exp(-\varepsilon^2/(2(v+b\varepsilon/3)))\) for \(\varepsilon\ge0\), and the two-sided bound with a factor \(2\) holds when \(|X_i|\le b\) ([Bernstein](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/Probability/Moments/Bernstein.lean), `ProbabilityTheory.iIndepFun.measureReal_sum_ge_le_of_ae_le`, `ProbabilityTheory.iIndepFun.measureReal_abs_sum_ge_le_of_abs_le`). Applied to the centred weighted losses divided by \(n\), with \(b=B/n\) and \(v\le B/n\), and solved for \(\varepsilon\), it gives the deviation bound of item 73. The unbiasedness and variance bound under covariate shift and that inversion are not stated.

#### Statlib

No relevant declarations were found.

**Synopsis entries.** Not covered: 107.69–107.72, 107.73 (ingredients only: Bernstein's inequality for independent bounded summands, in TauCeti; the unbiasedness and variance under covariate shift and the explicit bound are not stated).

### Threshold queries and local contraction

[Mathematical scope](SYNOPSIS107.md#threshold-queries-and-local-contraction).

#### Mathlib

The chain rule and data-processing inequality for the divergence, recorded above, give the tensorization step of item 75 once the single-release bound is known.

#### TauCeti

Pinsker's inequality is proved for probability measures, in the form \(|\mu-\nu|(\Omega)^2\le2D(\mu\|\nu)\) for the total variation of the signed difference, with no absolute-continuity hypothesis ([Pinsker](https://github.com/TauCetiProject/TauCeti/blob/afa08a3ed16fb167e35de371afb1eb03fbc5913a/TauCeti/InformationTheory/KullbackLeibler/Pinsker.lean), `TauCeti.etvDist_sq_le_two_mul_klDiv`). It bounds total variation by divergence, whereas item 75 bounds divergence by total variation under a likelihood-ratio constraint; the latter is not stated.

#### Statlib

The data-processing inequalities for the total variation distance under a Markov kernel and for mutual information under kernels acting on each component are proved ([total variation](https://github.com/stat-lib/statlib/blob/eeaac0283690efaa60c31115400cf561836baeb9/Statlib/Divergence/TotalVariation.lean), `ProbabilityTheory.tvDist_comp_le`; [mutual information](https://github.com/stat-lib/statlib/blob/eeaac0283690efaa60c31115400cf561836baeb9/Statlib/Divergence/MutualInformation/Basic.lean), `ProbabilityTheory.mutualInfo_parallelComp_comp_le`). These are supporting material for item 75, whose bound under local privacy is not stated.

**Synopsis entries.** Not covered: 107.74, 107.75.

### Fairness criteria and label shift

[Mathematical scope](SYNOPSIS107.md#fairness-criteria-and-label-shift).

#### Mathlib

Bayes' theorem for conditional probability measures, \(\mu[t\mid s]=\mu(s)^{-1}\mu[s\mid t]\,\mu(t)\), is `ProbabilityTheory.cond_eq_inv_mul_cond_mul` (`Probability/ConditionalProbability.lean`). It is the elementary identity behind the label-shift correction of item 77, which is not stated. The fairness criteria are expressible with `ProbabilityTheory.CondIndepFun`, as noted above.

#### TauCeti

No relevant declarations were found.

#### Statlib

No relevant declarations were found.

**Synopsis entries.** Not covered: 107.76, 107.77.

## Missing from all three libraries

**Learning-theoretic framework.** There is no definition of a hypothesis class with population and empirical risk, of a learning rule, or of PAC learnability, so items 1, 7, 9, 10, and 35 have no formal home. Item 9 is a two-line inequality once risks are defined. The fundamental theorem, item 1, needs the uniform deviation bound for VC classes, CKMA SYNOPSIS07 item 37, which is itself missing; Sauer–Shelah is present. Rademacher complexity, item 2, is one definition away, given TauCeti's Rademacher law and McDiarmid's inequality. Symmetrization is the missing step. Once symmetrization is available, the kernel-ball bound, item 3, follows from Mathlib's RKHS and the Cauchy–Schwarz inequality. Uniform stability, item 12, is close to McDiarmid's inequality once algorithms on samples are defined.

**Online learning and bandits.** Regret, online gradient descent, Hedge, Exp3, UCB, Thompson sampling, Gittins indices, the Lai–Robbins bound, and linear bandits, items 4, 5, 49–52, 62, and 63, are absent. Items 4 and 5 are deterministic potential-function arguments; they need only convex projection, which Mathlib has, and elementary inequalities for the exponential. The Lai–Robbins bound, item 49, would combine Mathlib's KL chain rule and data-processing inequality with an Ionescu–Tulcea law of the interaction; Statlib's divergence identity at stopping times is its single-arm case, and the bandit model is the missing layer. The minimax lower bound of item 62 would add Statlib's Bretagnolle–Huber inequality to the same divergence decomposition. The self-normalized bound, item 63, needs a time-uniform maximal inequality for supermartingales (Ville's inequality), which none of the three libraries states.

**Markov decision processes.** No finite MDP, value function, or Bellman operator is defined. Items 53, 55, and 58 are short once the model is defined: they follow from `ContractingWith`, the Neumann series, and finite-dimensional linear algebra. Item 58 also needs linear-programming duality. Items 54 and 60 need a stochastic-approximation theorem of Robbins–Siegmund type, not present although Mathlib's martingale convergence theorem is. Items 56, 57, 59, and 61 are algebraic identities and concentration bounds on top of the same model.

**Classification theory.** The excess-risk identity and the plug-in and margin bounds of item 8, Zhang's comparison inequality, item 11, the kernel ridge rate, item 13, nearest-neighbour asymptotics, item 14, and Stone-type consistency of forests, item 20, are absent. The remaining claims of item 8 are short computations from Statlib's binary Bayes test once the risk of a classifier is written as the risk of a test. Items 13, 14, and 20 need empirical-process and covering arguments that are missing; see [CKMA Structure 07](../lean-CKMA/STRUCTURE07.md).

**Ensembles, trees, and graphical models.** The \(k\)-means consistency, cost-complexity pruning, gradient-boosting descent, AdaBoost, and Breiman's ordering theorem, items 16–18, 24, and the second half of 25, are absent. Item 18 is a Hilbert-space computation and item 22 a covariance computation, both one step from existing API. Belief propagation, the Bethe free energy, junction trees, and the variational representation of exponential families, items 19, 23, 26, and 27, need multiparameter exponential families, chordal graphs, and convex conjugates, none of which is present.

**Neural networks.** TauCeti's multilayer perceptron specifications and their hidden-neuron symmetries are the only network layer, and no approximation, capacity, initialization, or training theorem is built on them, so items 28–30, 32, 33, 35–37, 39, and 40 are absent. The cheapest entries are item 33, the gradient and Hessian of log-sum-exp, for which TauCeti's softmax derivative in reduced coordinates is the main step, and item 32, the pointwise optimal discriminator, for which Statlib supplies the Jensen–Shannon divergence and its vanishing criterion. Item 38 needs the converse commutant statement and the Fourier diagonalization of circulants, from Mathlib's `Matrix.circulant` and `ZMod.dft`. For item 40, TauCeti's Moore–Penrose inverse supplies the limit; the least-squares iteration is a spectral computation, and the logistic implicit bias is far. Item 31 is closest: the inverse-Wishart mean in TauCeti gives the case \(n>p+1\) after a short computation; the case \(p>n+1\) needs the corresponding moment for the projection onto the row space. The Gaussian-process limit, item 39, needs a multivariate central limit theorem for exchangeable arrays of width tending to infinity, and Barron's and Yarotsky's rates need Fourier-analytic and Sobolev approximation theory beyond what is formalized.

**Network models.** The binomial random graph is only defined. Its phase transition and connectivity threshold, item 47, need branching-process comparison and the Poisson approximation, both absent. The stochastic block model, items 41, 42, 45, and 48, is not defined; item 45 is a rank-two eigenvalue computation, and item 48 combines TauCeti's Davis–Kahan theorem with an operator-norm bound for the symmetric noise matrix. That bound follows from TauCeti's sub-Gaussian matrix bound applied to the upper triangle; the matrix Bernstein inequality of the sparse regime (CKMA SYNOPSIS07 item 44) is missing. Contiguity, needed for item 42, is defined in Statlib, but neither Le Cam's first lemma nor any contiguity of graph laws is proved. Weisfeiler–Leman refinement and message-passing networks, items 44 and 46, are combinatorial and absent. Item 46 is a direct verification once message passing is defined. For item 43 the remaining gap is the attained form of weak isomorphism, from cut distance zero to almost-everywhere equal pullbacks (the Borgs–Chayes–Lovász theorem), together with the reduction from finite to all permutations.

**Differential privacy.** No mechanism or privacy definition exists, so items 64–66, 69–72, 74, and 75 are absent. The Laplace and Gaussian mechanisms, items 64 and 70, are close to TauCeti's Laplace law and Mathlib's Gaussian law: they need a pointwise density-ratio bound and, for item 70, a Gaussian tail estimate. Composition, post-processing, and the exponential mechanism, items 65, 69, and 71, are measure-theoretic statements about kernels; the advanced composition bound also needs Azuma's inequality, which Mathlib has in conditional sub-Gaussian form and TauCeti for bounded martingale differences. The local-privacy contraction, item 75, and the minimax rates, item 66, need a reverse-Pinsker inequality under bounded likelihood ratio, which is absent, and the two-point and Fano methods of SYNOPSIS103, for which Statlib's Bretagnolle–Huber inequality, mutual information, and binary Fano inequality are the starting point.

**Fairness and distribution shift.** The fairness incompatibility results, items 67 and 76, are elementary consequences of conditional independence that are not stated; `CondIndepFun` supplies the language. The \(\mathcal H\Delta\mathcal H\) bound, item 68, needs the hypothesis-class framework. Item 73 is a direct application of TauCeti's Bernstein inequality once the weighted estimator and its variance bound are set up. Item 77 is Bayes' theorem plus a finite linear system and is one step from `cond_eq_inv_mul_cond_mul`.
