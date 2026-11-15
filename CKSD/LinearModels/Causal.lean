module -- shake: keep-all

public import CKSD.LinearModels.Causal.Identification
public import CKSD.LinearModels.Causal.GFormula
public import CKSD.LinearModels.Causal.InstrumentalVariables
public import CKSD.LinearModels.Causal.StructuralEquations

/-!
# Causal inference

Entry module for the causal-inference modules of Section 105:

* `CKSD.LinearModels.Causal.Efficiency`: propensity scores and the efficient influence
  function of the average treatment effect (imported through `Identification`);
* `CKSD.LinearModels.Causal.Identification`: adjustment, inverse propensity weighting, double
  robustness, and the Wald ratio for compliers;
* `CKSD.LinearModels.Causal.GFormula`: the longitudinal g-formula;
* `CKSD.LinearModels.Causal.InstrumentalVariables`: two-stage least squares;
* `CKSD.LinearModels.Causal.StructuralEquations`: structural equation models on causal graphs.

Causal graphs, d-separation, the directed Markov properties and the do-calculus are in
`CKSD.LinearModels.DirectedGraphical`.
-/
