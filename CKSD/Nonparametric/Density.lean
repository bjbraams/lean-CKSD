module -- shake: keep-all

public import CKSD.Nonparametric.Density.KernelL1
public import CKSD.Nonparametric.Density.HolderMinimax
public import CKSD.Nonparametric.Density.Grenander
public import CKSD.Nonparametric.Density.LogConcave

/-!
# Density estimation

Entry module for density estimation: the universal `L¹` consistency of the kernel density
estimator (`CKSD.Nonparametric.Density.KernelL1`), the pointwise minimax rate over Hölder
classes (`CKSD.Nonparametric.Density.HolderMinimax`), and the shape-constrained Grenander
(`CKSD.Nonparametric.Density.Grenander`) and log-concave
(`CKSD.Nonparametric.Density.LogConcave`) maximum likelihood estimators.
-/
