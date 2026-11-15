module -- shake: keep-all

public import CKSD.LinearModels.FTest
public import CKSD.LinearModels.RegressionLimits
public import CKSD.LinearModels.GLM.Asymptotics
public import CKSD.LinearModels.Multivariate
public import CKSD.LinearModels.FactorAnalysis
public import CKSD.LinearModels.Mixtures
public import CKSD.LinearModels.Graphical.DecomposableGaussian
public import CKSD.LinearModels.Design
public import CKSD.LinearModels.SurveySampling
public import CKSD.LinearModels.Causal
public import CKSD.LinearModels.DirectedGraphical

/-!
# Section 105: linear models, multivariate analysis, design, and causal inference

Entry module for the CKSD formalization of Section 105. It imports:

* Gaussian linear models: Gauss–Markov, residual laws, the F test and its optimality
  (`Regression`, `FTest`), quantile regression (`RegressionLimits`), generalized linear models
  (`GLM.Basic`, `GLM.ConvexLikelihood`, `GLM.Asymptotics`);
* multivariate analysis: Wishart and Hotelling statistics, likelihood-ratio tests, canonical
  correlations and covariance eigenvalues (`Multivariate` and the modules `Multivariate.*`),
  factor analysis and mixtures (`FactorAnalysis`, `Mixtures`, `GaussianMixtureIdentifiability`),
  Gaussian graphical and decomposable models (`Graphical.Gaussian`, `Graphical.Decomposable`,
  `Graphical.DecomposableGaussian`);
* experimental design and survey sampling (`Design`, `SurveySampling`);
* causal inference (`Causal` and the modules `Causal.*`): potential outcomes, propensity
  scores, efficient influence functions, the g-formula, instrumental variables and structural
  equation models; causal graphs and d-separation (`DirectedGraphical.Basic.CausalGraph`,
  `DirectedGraphical.Basic.ActiveTrails`), directed Markov properties and the do-calculus
  (`DirectedGraphical`).
-/
