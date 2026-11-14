module

public import CKSD.Processes.Kalman.Filter


namespace CKSD

/-!
# The Kalman filter

A time-varying linear Gaussian state-space model `x_{t+1} = F_t x_t + w_t`,
`y_t = H_t x_t + v_t` with state and observation coordinates indexed by finite types, and time
indexed from `0`: the initial state is `x_0`, so `x_{0|-1}` and `P_{0|-1}` are its mean and
covariance. The covariance recursion does
not depend on the data; the mean recursion is a function of the observation sequence, of which
only the first `t + 1` terms enter the filtered mean at time `t`.

Gaussian densities are TauCeti's `multivariateGaussianPDF`.

## Main results

* `CKSD.KalmanModel.kalman_filter` (GAPS 106.7): conditionally on `y_0, …, y_t`, the state
  `x_t` is Gaussian with mean `x_{t|t}` and covariance `P_{t|t}`, and `x_{t+1}` with mean
  `x_{t+1|t}` and covariance `P_{t+1|t}`; the innovations are independent with laws
  `N(0, Σ_t)`; and the density of `(y_0, …, y_{n-1})` is the product of the one-step predictive
  densities.

## Proof outline

The proof follows the innovations argument and works with the prediction errors
`ε_t = x_t - x_{t|t-1}`, the filtering errors `φ_t = x_t - x_{t|t}`, and the innovations
`e_t = y_t - H_t x_{t|t-1}` (`KalmanModel.predErr`, `KalmanModel.filtErr`,
`KalmanModel.innovation`). By induction on `t`, `ε_t` has law `N(0, P_{t|t-1})` and is
independent of `(y_0, …, y_{t-1})` (`KalmanModel.GaussianInputs.pred_err_has_law_indep_fun`).

* Measurement update (`KalmanModel.GaussianInputs.measurement_update`): `e_t = H_t ε_t + v_t`
  and `φ_t = (I - K_t H_t) ε_t - K_t v_t` are linear combinations of the independent centered
  Gaussian vectors `ε_t` and `v_t`; they are independent because their cross-covariance
  vanishes, and the Joseph form gives the covariance `P_{t|t}` of `φ_t`.
* Time update (`KalmanModel.GaussianInputs.time_update`): `ε_{t+1} = F_t φ_t + w_t`.
* Independence bookkeeping uses that `v_t` and `w_t` are independent of the inputs that
  determine the earlier errors and observations (`indep_fun_apply_prefix_of_indep_fun`).

The conditional laws then follow from `x_t = x_{t|t}(y_0, …, y_t) + φ_t` with `φ_t`
independent of the record (`cond_distrib_add_eq_multivariate_gaussian`); the innovations are
mutually independent because each is independent of the earlier record
(`i_indep_fun_of_indep_fun_fin_prefix`); and the density factorization follows by appending one
observation at a time (`KalmanModel.GaussianInputs.map_obs_prefix_eq_with_density`).

Reused results: from TauCeti, the affine images, convolutions, independence criterion, and
densities of multivariate Gaussian laws (`TauCeti.Probability.map_affine_multivariateGaussian`,
`TauCeti.Probability.multivariateGaussian_conv_multivariateGaussian`,
`TauCeti.Probability.indepFun_matrix_of_hasLaw_multivariateGaussian_iff`,
`TauCeti.Probability.multivariateGaussian_eq_withDensity`) and the transport of densities
`MeasurableEquiv.map_withDensity`; from Mathlib, the
conditional-distribution characterization `condDistrib_ae_eq_of_measure_eq_compProd`,
`Measure.withDensity_compProd_withDensity`, and `measurePreserving_piFinSuccAbove`.

Source: GAPS 106.7.
-/


end CKSD