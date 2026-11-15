module -- shake: keep-all

public import CKSD.Nonparametric.LowerBounds.Testing
public import CKSD.Nonparametric.LowerBounds.Gaussian

/-!
# Minimax lower bounds

Entry module for the minimax lower-bound tools: Le Cam's two-point bound, Fano's inequality
(also in averaged form), Assouad's lemma and Hamming packings
(`CKSD.Nonparametric.LowerBounds.Testing`), and Kullback–Leibler and total variation bounds
between Gaussian product laws (`CKSD.Nonparametric.LowerBounds.Gaussian`).
Sources: GAPS 103.39–103.40 and 103.45–103.46.

## References

* A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer, 2009, Chapter 2.
* M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge University
  Press, 2019, Chapter 15.
-/
