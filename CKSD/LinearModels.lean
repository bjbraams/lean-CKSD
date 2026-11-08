module

public import CKSD.LinearModels.Causal
public import CKSD.LinearModels.CausalEfficiency
public import CKSD.LinearModels.GaussianGraphical
public import CKSD.LinearModels.Regression
public import CKSD.LinearModels.Mixtures
public import CKSD.LinearModels.Multivariate
public import CKSD.LinearModels.MultivariateTests
public import CKSD.LinearModels.FactorAnalysis
public import CKSD.LinearModels.RegressionLimits
public import CKSD.LinearModels.Design
public import CKSD.LinearModels.CausalAndSurvey
public import CKSD.LinearModels.SurveySampling
public import CKSD.LinearModels.CanonicalCorrelation
public import CKSD.LinearModels.Decomposable
public import CKSD.LinearModels.ActiveTrails
public import CKSD.LinearModels.DirectedGraphical
public import CKSD.LinearModels.FTest
public import CKSD.LinearModels.GFormula
public import CKSD.LinearModels.GLMAsymptotics
public import CKSD.LinearModels.StructuralEquations

/-!
# Section 105: linear models, multivariate analysis, design, and causal inference

Entry module for the CKSD formalization of Section 105. It imports:

* Gaussian linear models: Gauss–Markov, residual laws, the F test and its optimality
  (`Regression`, `FTest`), quantile regression and instrumental variables
  (`RegressionLimits`), generalized linear models (`GLMAsymptotics`);
* multivariate analysis: Wishart and Hotelling statistics, canonical correlations, factor
  analysis, mixtures (`Multivariate`, `MultivariateTests`, `CanonicalCorrelation`,
  `FactorAnalysis`, `Mixtures`), Gaussian graphical and decomposable models
  (`GaussianGraphical`, `Decomposable`);
* experimental design and survey sampling (`Design`, `SurveySampling`);
* causal inference: potential outcomes, propensity scores, and efficient influence functions
  (`CausalEfficiency`, `CausalAndSurvey`, `GFormula`), causal graphs and d-separation (`Causal`, `ActiveTrails`),
  directed Markov properties and the do-calculus (`DirectedGraphical`), and structural equation
  models (`StructuralEquations`).
-/
