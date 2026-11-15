module -- shake: keep-all

public import CKSD.Bayes.Particle.Limits

/-!
# Particle filters

Bootstrap particle approximations of Feynman–Kac flows: the bootstrap particle filter,
unbiasedness of its likelihood estimate and fixed-time consistency
(`CKSD.Bayes.Particle.Filter`), fluctuation and central limit theorems
(`CKSD.Bayes.Particle.Fluctuations`, `CKSD.Bayes.Particle.CentralLimit`,
`CKSD.Bayes.Particle.LimitCore`), and uniform-in-time moment bounds under mixing
(`CKSD.Bayes.Particle.Limits`). This module imports the whole development.
-/
