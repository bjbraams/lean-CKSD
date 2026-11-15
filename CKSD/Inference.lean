module -- shake: keep-all

public import CKSD.Inference.ExponentialFamily
public import CKSD.Inference.LogPartition
public import CKSD.Inference.Density
public import CKSD.Inference.Factorization
public import CKSD.Inference.LaplaceDeterminacy
public import CKSD.Inference.Sufficiency
public import CKSD.Inference.Model
public import CKSD.Inference.Families
public import CKSD.Inference.SymmetricCompleteness
public import CKSD.Inference.Estimation
public import CKSD.Inference.NeymanPearson
public import CKSD.Inference.Testing
public import CKSD.Inference.IntervalTestConstruction
public import CKSD.Inference.Decision
public import CKSD.Inference.InvariantTesting
public import CKSD.Inference.Gaussian
public import CKSD.Inference.ExponentialFamilyMLE
public import CKSD.Inference.MeanParametrization
public import CKSD.Inference.ConditionalExponentialFamily

/-!
# Section 101: Statistical inference

Entry module for the CKSD formalization of Section 101 (core statistical inference).

* `CKSD.Inference.Basic`, `CKSD.Inference.Model`, `CKSD.Inference.Density`: models, convergence
  interfaces, tests, estimators, decision rules, the classical optimality criteria, and integrals
  against laws with a real density.
* `CKSD.Inference.LaplaceDeterminacy`: Laplace determinacy of finite measures, used for
  completeness in exponential families.
* `CKSD.Inference.Factorization`, `CKSD.Inference.Sufficiency`, `CKSD.Inference.ExponentialFamily`,
  `CKSD.Inference.ConditionalExponentialFamily`, `CKSD.Inference.LogPartition`: sufficiency,
  completeness, and exponential families (GAPS 101.1–101.6, 101.43, 101.46).
* `CKSD.Inference.Estimation`, `CKSD.Inference.Families`, `CKSD.Inference.SymmetricCompleteness`:
  unbiased estimation, order statistics, and equivariant estimation (GAPS 101.7–101.13, 101.21,
  101.40).
* `CKSD.Inference.NeymanPearson`, `CKSD.Inference.Testing`, `CKSD.Inference.InvariantTesting`,
  `CKSD.Inference.IntervalTestConstruction`: optimal tests (GAPS 101.14–101.17, 101.45–101.56).
* `CKSD.Inference.Decision`, `CKSD.Inference.Gaussian`, `CKSD.Inference.ExponentialFamilyMLE`,
  `CKSD.Inference.MeanParametrization`: decision theory, comparison of experiments, Gaussian models,
  and maximum likelihood in natural exponential families (GAPS 101.32–101.42, 101.57–101.69).
* `CKSD.Inference.FiniteDecision`, `CKSD.Inference.ConvexGames`,
  `CKSD.Inference.KernelDisintegration`, `CKSD.Inference.Blackwell.Finite`,
  `CKSD.Inference.Blackwell.Approximation`, `CKSD.Inference.Blackwell.Coupling`,
  `CKSD.Inference.Blackwell.Joint`, `CKSD.Inference.Blackwell.Posterior`: compact risk sets and
  saddle points for finite decision problems, common randomization kernels, and the finite,
  approximation, coupling and posterior steps of Blackwell's comparison of experiments, imported
  through `CKSD.Inference.Decision`.
-/
