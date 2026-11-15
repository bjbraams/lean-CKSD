module -- shake: keep-all

public import CKSD.Bayes.MeanField.PropagationOfChaos
public import CKSD.Bayes.MeanField.Training.Limit
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# McKean–Vlasov systems and mean-field limits

Interacting diffusions with additive noise `dXₜ = b(Xₜ, μₜ) dt + dWₜ` are stated pathwise, as the
integral equation `Xₜ = X₀ + ∫₀ᵗ b(Xₛ, μₛ) ds + Wₜ` driven by continuous Brownian paths. The
mean-field gradient flow of two-layer network training is a system of ordinary differential
equations, and its limit is a solution of TauCeti's continuity equation. This module imports the
whole development.

## Main results

* `CKSD.exists_unique_mcKeanVlasov_and_particleSystem`, `CKSD.tendsto_particle_paths`,
  `CKSD.exists_lintegral_sup_particle_sub_le` (in `CKSD.Bayes.MeanField.PropagationOfChaos`):
  well-posedness, propagation of chaos, and quantitative propagation of chaos.
* `CKSD.meanFieldRisk_eq`, `CKSD.hasGradientAt_meanFieldPotential_empiricalMeasure`,
  `CKSD.exists_meanField_limit` (in `CKSD.Bayes.MeanField.Training.Limit`): the quadratic
  expansion of the risk, the gradient-flow form of the particle equation, and the mean-field limit
  of network training.

The definitions of the McKean–Vlasov equation and its particle systems are in
`CKSD.Bayes.MeanField.Basic`.

Sources: GAPS 104.51, 104.53, and 104.56.
-/
