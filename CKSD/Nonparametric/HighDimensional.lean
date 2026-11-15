module -- shake: keep-all

public import CKSD.Nonparametric.HighDimensional.HilbertCLT
public import CKSD.Nonparametric.HighDimensional.PrincipalComponents
public import CKSD.Nonparametric.HighDimensional.EigenvectorPerturbation
public import CKSD.Nonparametric.HighDimensional.Lasso
public import CKSD.Nonparametric.HighDimensional.SparseMinimax
public import CKSD.Nonparametric.HighDimensional.FalseDiscoveryRate
public import CKSD.Nonparametric.HighDimensional.CovarianceThresholding
public import CKSD.Nonparametric.HighDimensional.GraphicalModels

/-!
# High-dimensional estimation and testing

Entry module for the high-dimensional part of Section 103: the central limit theorem in a
separable Hilbert space (`CKSD.Nonparametric.HighDimensional.HilbertCLT`), principal components
and leading-eigenvector perturbation (`CKSD.Nonparametric.HighDimensional.PrincipalComponents`,
`CKSD.Nonparametric.HighDimensional.EigenvectorPerturbation`), the lasso and the sparse minimax
rate (`CKSD.Nonparametric.HighDimensional.Lasso`,
`CKSD.Nonparametric.HighDimensional.SparseMinimax`), false discovery rate control
(`CKSD.Nonparametric.HighDimensional.FalseDiscoveryRate`), covariance thresholding
(`CKSD.Nonparametric.HighDimensional.CovarianceThresholding`), and Gaussian graphical model
selection (`CKSD.Nonparametric.HighDimensional.GraphicalModels`).
-/
