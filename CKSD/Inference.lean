module

public import CKSD.Inference.ExponentialFamily
public import CKSD.Inference.Moments
public import CKSD.Inference.Density
public import CKSD.Inference.Factorization
public import CKSD.Inference.LaplaceDeterminacy
public import CKSD.Inference.Sufficiency
public import CKSD.Inference.Model
public import CKSD.Inference.Families
public import CKSD.Inference.Estimation
public import CKSD.Inference.NeymanPearson
public import CKSD.Inference.Testing
public import CKSD.Inference.Decision
public import CKSD.Inference.InvariantTesting
public import CKSD.Inference.Gaussian
public import CKSD.Inference.ConditionalExponentialFamily

/-!
# Section 101: Statistical inference

Entry module for the CKSD formalization of Section 101 (core statistical inference).

* `CKSD.Inference.Basic`, `CKSD.Inference.Model`: models, convergence interfaces, tests,
  estimators, decision rules, and the classical optimality criteria.
* `CKSD.Inference.Factorization`, `CKSD.Inference.Sufficiency`, `CKSD.Inference.ExponentialFamily`,
  `CKSD.Inference.ConditionalExponentialFamily`: sufficiency, completeness, and exponential
  families (GAPS 101.1–101.6, 101.43, 101.46).
* `CKSD.Inference.Estimation`, `CKSD.Inference.Families`: unbiased estimation, order statistics,
  and equivariant estimation (GAPS 101.7–101.13, 101.21, 101.40).
* `CKSD.Inference.NeymanPearson`, `CKSD.Inference.Testing`, `CKSD.Inference.InvariantTesting`:
  optimal tests (GAPS 101.14–101.17, 101.45–101.56).
* `CKSD.Inference.Decision`, `CKSD.Inference.Gaussian`: decision theory, comparison of
  experiments, and Gaussian models (GAPS 101.32–101.42, 101.57–101.69).
-/
