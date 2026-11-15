module -- shake: keep-all

public import CKSD.Asymptotics.AsymptoticTheory
public import CKSD.Asymptotics.Basic
public import CKSD.Asymptotics.Bootstrap
public import CKSD.Asymptotics.ConvexArgmin.Basic
public import CKSD.Asymptotics.ConvexRegression.Basic
public import CKSD.Asymptotics.CrossFitting
public import CKSD.Asymptotics.CrossFitting.FoldBounds
public import CKSD.Asymptotics.Expansions
public import CKSD.Asymptotics.FunctionalDeltaMethod
public import CKSD.Asymptotics.InformationGeometry
public import CKSD.Asymptotics.LAN.Approximation
public import CKSD.Asymptotics.LAN.Basic
public import CKSD.Asymptotics.LAN.ConvolutionKernel
public import CKSD.Asymptotics.LAN.GaussianAnderson
public import CKSD.Asymptotics.LAN.GaussianKernelTranslation
public import CKSD.Asymptotics.LAN.GaussianShiftComplete
public import CKSD.Asymptotics.LAN.GaussianShiftTilt
public import CKSD.Asymptotics.LAN.JointLimit
public import CKSD.Asymptotics.LAN.KernelConvolution
public import CKSD.Asymptotics.LAN.KernelTranslation
public import CKSD.Asymptotics.LAN.LeCam
public import CKSD.Asymptotics.LAN.LikelihoodLimit
public import CKSD.Asymptotics.LAN.LikelihoodSingular
public import CKSD.Asymptotics.LAN.LikelihoodTransfer
public import CKSD.Asymptotics.LAN.Representation
public import CKSD.Asymptotics.LikelihoodSupport
public import CKSD.Asymptotics.LikelihoodTests
public import CKSD.Asymptotics.Lindeberg.Basic
public import CKSD.Asymptotics.MartingaleCLT.Basic
public import CKSD.Asymptotics.MEstimation.Consistency
public import CKSD.Asymptotics.MEstimation.LipschitzChaining
public import CKSD.Asymptotics.MEstimation.LipschitzExpansion
public import CKSD.Asymptotics.MEstimation.MaximumLikelihood
public import CKSD.Asymptotics.MEstimation.Normality
public import CKSD.Asymptotics.MEstimation.Regression
public import CKSD.Asymptotics.MEstimation.ZEstimators
public import CKSD.Asymptotics.MultivariateCLT
public import CKSD.Asymptotics.QMDReference
public import CKSD.Asymptotics.Quantiles
public import CKSD.Asymptotics.RatesOfConvergence
public import CKSD.Asymptotics.Robustness
public import CKSD.Asymptotics.Semiparametric
public import CKSD.Asymptotics.Statistics
public import CKSD.Asymptotics.UStatistics.Limits
public import CKSD.Asymptotics.UStatistics.Projection

/-!
# Section 102: Asymptotic statistics

Entry module for the CKSD formalization of Section 102.

* `CKSD.Asymptotics.Basic`, `CKSD.Asymptotics.Statistics`: empirical statistics, contiguity,
  stochastic orders, and statistical functionals.
* `CKSD.Asymptotics.Basic`, `CKSD.Asymptotics.MultivariateCLT`,
  `CKSD.Asymptotics.Lindeberg.Basic`, `CKSD.Asymptotics.MartingaleCLT.Basic`: weak convergence,
  stochastic algebra, laws of large numbers, and central limit theorems, including the
  Lindeberg–Feller theorem for triangular arrays and the martingale central limit theorem under
  bounded conditional variances.
* `CKSD.Asymptotics.FunctionalDeltaMethod`: Hadamard differentiability and the functional delta
  method.
* `CKSD.Asymptotics.MEstimation` (`Consistency`, `MaximumLikelihood`, `ZEstimators`,
  `Normality`, `Regression`, with the chaining bounds of `LipschitzChaining` and
  `LipschitzExpansion`), `CKSD.Asymptotics.Quantiles`, `CKSD.Asymptotics.LikelihoodSupport`,
  `CKSD.Asymptotics.UStatistics` (`Projection`, `Limits`), `CKSD.Asymptotics.RatesOfConvergence`,
  `CKSD.Asymptotics.AsymptoticTheory`, `CKSD.Asymptotics.ConvexArgmin.Basic`,
  `CKSD.Asymptotics.ConvexRegression.Basic`: consistency, rates, and asymptotic normality of
  estimators.
* `CKSD.Asymptotics.LAN`: local experiments and local asymptotic normality (`Basic`), contiguity
  and Le Cam's lemmas (`LeCam`), and the asymptotic representation, convolution and local
  asymptotic minimax theorems (`Representation`) with their Gaussian-shift and kernel
  ingredients. `CKSD.Asymptotics.LikelihoodTests`: the likelihood-ratio, Wald, and score tests.
* `CKSD.Asymptotics.Semiparametric`, `CKSD.Asymptotics.QMDReference`,
  `CKSD.Asymptotics.CrossFitting`: semiparametric efficiency, cross-fitting, and adaptation.
* `CKSD.Asymptotics.Robustness`, `CKSD.Asymptotics.Expansions`, `CKSD.Asymptotics.Bootstrap`:
  robustness, Edgeworth and saddlepoint expansions, and the bootstrap.
* `CKSD.Asymptotics.InformationGeometry`: the Fisher–Rao metric and congruent embeddings.
-/
