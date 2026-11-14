module

public import CKSD.Nonparametric.LowerBounds.Testing
public import CKSD.Nonparametric.LowerBounds.Gaussian
public import CKSD.Nonparametric.SparseRecovery.Robust
public import CKSD.Nonparametric.CovarianceThresholding

/-!
# Testing lower bounds and sparse recovery

Entry module for the minimax lower-bound tools (Le Cam's two-point bound, Fano's inequality,
Assouad's lemma and Hamming packings), Kullback–Leibler and total variation bounds between
Gaussian product laws, restricted-isometry recovery theory, and deterministic
covariance thresholding.
Sources: GAPS 103.39–103.40, 103.45–103.46, 103.48–103.49, 103.52.

## References

* A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer, 2009, Chapter 2.
* M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge University
  Press, 2019, Chapter 15.
* S. Foucart and H. Rauhut, *A Mathematical Introduction to Compressive Sensing*, Birkhäuser, 2013.
-/
