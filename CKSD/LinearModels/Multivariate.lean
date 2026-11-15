module -- shake: keep-all

public import CKSD.LinearModels.Multivariate.Tests

/-!
# Multivariate normal analysis

Entry module for the multivariate-normal chain of Section 105. It imports, through
`CKSD.LinearModels.Multivariate.Tests`:

* `CKSD.LinearModels.Multivariate.SampleLaws`, `CKSD.LinearModels.Multivariate.NormalSample`:
  the Helmert decomposition, Wishart and Hotelling laws for normal samples, the Gaussian
  covariance likelihood, and the law of the sample correlation;
* `CKSD.LinearModels.Multivariate.CanonicalCorrelation`: canonical correlations;
* `CKSD.LinearModels.Multivariate.EigenvaluePerturbation`,
  `CKSD.LinearModels.Multivariate.CovarianceEigenvalues`: eigenvalue perturbation and the
  asymptotic normality of sample covariance eigenvalues;
* the modules `CKSD.LinearModels.Multivariate.LikelihoodRatio.*`: Wishart moment identities,
  the exact and limiting laws of the sphericity and block-independence likelihood ratios, and
  the gamma and beta asymptotics they use;
* `CKSD.LinearModels.Multivariate.Tests`: Wilks's `Λ` and the other classical test statistics,
  their laws, and their expression through the generalized roots.
-/
