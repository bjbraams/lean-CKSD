<!-- Sections 101-114 of the core-knowledge bibliography.
     Sections 101-109 are mathematical statistics; Sections 110-114 are
     data science. They follow the conventions of CKMA-bib.md (../lean-CKMA).
     Numbers start at 101 to avoid collision with Sections 1-55 there;
     "Section N" with N <= 55 refers to CKMA-bib.md. -->

---

# Part XI. Mathematical Statistics

---

<a id="cks-101"></a>

## 101. Statistical Inference: General Texts, References, and History

Graduate texts in mathematical statistics cover probability at the level
needed for inference, sufficiency, estimation, testing, and a first look at
asymptotics. Subdivision 101A collects these general courses; 101B collects
the large references, distribution handbooks, and histories that statisticians
consult rather than read. Classical decision theory, estimation, and testing
are developed further in Section 102, asymptotic theory in Section 103, and
measure-theoretic probability in Section 6.

<a id="cks-101a"></a>

### 101A. General Graduate Texts

Probability for inference, point estimation, hypothesis testing, likelihood,
and the first asymptotic evaluations provide the general framework.

#### Foundational works

* **Harald Cramér, *Mathematical Methods of Statistics*** (1946,
  [Princeton University Press](https://doi.org/10.1515/9781400883868)).
  Measure and integration, distribution theory, and the classical theory
  of estimation and testing, including the information inequality. The
  book that set mathematical statistics on a rigorous footing, and still
  a clear reference for the classical results.
* **George Casella and Roger L. Berger, *Statistical Inference*** (2nd
  ed., 2002, Duxbury; [Chapman and
  Hall/CRC](https://doi.org/10.1201/9781003456285) reissue, 2024; first
  ed. 1990). The standard first graduate text in many statistics
  programs: probability, estimation, hypothesis testing, and the first
  asymptotic evaluations, with the measure theory kept light.
* **Peter J. Bickel and Kjell A. Doksum, *Mathematical Statistics: Basic
  Ideas and Selected Topics***. Volume I, second edition (Prentice Hall,
  2001; [CRC Press reissue](https://doi.org/10.1201/b18312), 2015),
  revises the single-volume first edition of 1977. Volume II ([CRC
  Press](https://doi.org/10.1201/b19822), 2015) is a further book, on
  nonparametric and semiparametric models, function estimation, and
  prediction. The pair asks for more mathematical maturity than
  Casella–Berger. Also listed in Section 104.
* **Jun Shao, *Mathematical Statistics*** (2nd ed., 2003,
  [Springer](https://doi.org/10.1007/b97553); first ed. 1999). A
  measure-theoretic graduate text, often used for a PhD core course.
  *Mathematical Statistics: Exercises and Solutions* is the companion
  volume of worked exercises.
* **Mark J. Schervish, *Theory of Statistics*** (1995,
  [Springer](https://doi.org/10.1007/978-1-4612-4250-5)). A broad
  measure-theoretic graduate text: sufficiency, decision theory,
  estimation, testing, and asymptotics, with both Bayesian and
  frequentist developments.
* **A. A. Borovkov, *Mathematical Statistics*** (English ed., 1998,
  Gordon and Breach; [Routledge](https://doi.org/10.1201/9780203749326)
  reissue, 2019; Russian ed. 1984). Estimation, testing, and asymptotic
  methods in the rigorous style of the Russian school. A counterpart to
  Shao and Schervish, with a strong limit-theorem emphasis.
* **A. C. Davison, *Statistical Models*** (2003, [Cambridge University
  Press](https://doi.org/10.1017/CBO9780511815850)). Likelihood,
  regression, designed experiments, and stochastic models, with
  asymptotic and computational methods developed alongside examples.
  A broad graduate bridge between inference theory and modelling.
* **D. R. Cox and D. V. Hinkley, *Theoretical Statistics*** (1974,
  [Chapman and Hall](https://doi.org/10.1201/b14832)). A conceptual
  treatise on the formulation of statistical inference. Read for the
  questions it poses; the theorem-proof development is in Lehmann and in
  Shao.
* **D. R. Cox, *Principles of Statistical Inference*** (2006, [Cambridge
  University Press](https://doi.org/10.1017/CBO9780511813559)). Cox's
  later short synthesis of the same circle of ideas. A reflective
  companion to Cox–Hinkley, above.
* **G. Alastair Young and Richard L. Smith, *Essentials of Statistical
  Inference*** (2005, [Cambridge University
  Press](https://doi.org/10.1017/CBO9780511755392)). A short, rigorous
  graduate course, useful where Shao or Schervish is more book than a
  term will hold.
* **Larry Wasserman, *All of Statistics: A Concise Course in Statistical
  Inference*** (2004,
  [Springer](https://doi.org/10.1007/978-0-387-21736-9)). A one-volume
  map of the subject. Orientation, in place of a treatise.

#### More recent works

* **Victor M. Panaretos, *Statistics for Mathematicians: A Rigorous First
  Course*** (2016, [Birkhäuser](https://doi.org/10.1007/978-3-319-28341-8),
  Compact Textbooks in Mathematics). A short course in estimation,
  testing, likelihood, and linear models, written for readers with a
  mathematics background and no prior statistics.
* **Robert W. Keener, *Theoretical Statistics: Topics for a Core
  Course*** (2010,
  [Springer](https://doi.org/10.1007/978-0-387-93839-4)). A
  measure-theoretic core course in a single volume: decision theory,
  equivariance, asymptotics, and a selection of further topics. Often
  used in the role Shao plays elsewhere.
* **Bradley Efron and Trevor Hastie, *Computer Age Statistical
  Inference: Algorithms, Evidence, and Data Science*** (2016, [Cambridge
  University Press](https://doi.org/10.1017/CBO9781316576533)). Classical
  frequentist, Bayesian, and Fisherian inference followed by the
  computation-driven methods of the last half-century: the bootstrap,
  empirical Bayes, false discovery rates, and the lasso. A map of how the
  modern subject grew out of the classical one.

<a id="cks-101b"></a>

### 101B. Large References, Distribution Handbooks, and History

Encyclopedic treatises, the standard catalogues of distributions, collections
of landmark papers, and histories of the subject.

#### Foundational works

* **Kendall's Advanced Theory of Statistics** (Alan Stuart and J. Keith
  Ord, Vol. 1, *Distribution Theory*, [6th ed.,
  1994](https://www.wiley.com/en-us/Kendall's+Advanced+Theory+of+Statistics%2C+Volume+1%2C+Distribution+Theory%2C+6th+Edition-p-9780470665305);
  Alan Stuart, J. Keith Ord, and Steven Arnold, Vol. 2A, *Classical
  Inference and the Linear Model*, [6th ed.,
  1999](https://www.wiley.com/en-us/Kendall's+Advanced+Theory+of+Statistics%2C+Volume+2A%2C+Classical+Inference+and+the+Linear+Model%2C+6th+Edition-p-9780470689240);
  Anthony O'Hagan and Jonathan Forster, Vol. 2B, *Bayesian Inference*,
  [2nd ed.,
  2004](https://www.wiley.com/en-us/Kendall's+Advanced+Theory+of+Statistics%2C+Volume+2B%2C+Bayesian+Inference%2C+2nd+Edition-p-9780470685693);
  now Wiley; first ed., Kendall alone, 1943–1946). The large classical
  reference for distribution theory, moments and cumulants, estimation, and testing.
  Consulted for a formula or a classical result rather than read.
* **Norman L. Johnson, Samuel Kotz, and N. Balakrishnan, *Distributions
  in Statistics*** (*Continuous Univariate Distributions*
  [I](https://www.wiley.com/en-us/Continuous+Univariate+Distributions%2C+Volume+1%2C+2nd+Edition-p-9780471584957)–[II](https://www.wiley.com/en-us/Continuous+Univariate+Distributions%2C+Volume+2%2C+2nd+Edition-p-9780471584940),
  2nd ed., 1994–1995; *Discrete Multivariate Distributions*,
  [1997](https://www.wiley.com/en-us/Discrete+Multivariate+Distributions-p-9780471128441);
  *Continuous Multivariate Distributions*, Vol. 1, 2nd ed.,
  [2000](https://doi.org/10.1002/0471722065); with Norman L. Johnson,
  Adrienne W. Kemp, and Samuel Kotz, *Univariate Discrete
  Distributions*, 3rd ed., [2005](https://doi.org/10.1002/0471715816);
  Wiley). The standard catalogue of distributions: properties,
  characterizations, estimation, and relations between families.
* **Samuel Kotz, N. Balakrishnan, Campbell B. Read, and Brani Vidakovic
  (eds.), *Encyclopedia of Statistical Sciences*** (2nd ed., 16 volumes,
  2006, [Wiley](https://doi.org/10.1002/0471667196); first ed.
  1982–1988). Signed survey articles across the whole subject, with
  references. The first place to look for an unfamiliar named method or
  result.
* **Samuel Kotz and Norman L. Johnson (eds.), *Breakthroughs in
  Statistics I–III*** (1992–1997, Springer:
  [I](https://doi.org/10.1007/978-1-4612-0919-5),
  [II](https://doi.org/10.1007/978-1-4612-4380-9),
  [III](https://doi.org/10.1007/978-1-4612-0667-5)). Reprints of
  landmark papers, each introduced by a modern commentary. A guide to
  the original sources of the ideas in Sections 101–109.
* **Stephen M. Stigler, *The History of Statistics: The Measurement of
  Uncertainty before 1900*** (1986, [Belknap Press of Harvard University
  Press](https://www.hup.harvard.edu/books/9780674403413)). Least
  squares, the normal law, and correlation, from Legendre and Laplace to
  Galton, Edgeworth, and Pearson. The standard history.
* **Stephen M. Stigler, *Statistics on the Table: The History of
  Statistical Concepts and Methods*** (1999, [Harvard University
  Press](https://doi.org/10.2307/j.ctv1pdrpsj)). Essays on the origins
  of particular ideas and on priority questions. A companion to the 1986
  history.
* **Anders Hald, *A History of Probability and Statistics and Their
  Applications before 1750***, ***A History of Mathematical Statistics
  from 1750 to 1930***, and ***A History of Parametric Statistical
  Inference from Bernoulli to Fisher, 1713–1935*** (1990, 1998, and
  2007; [Wiley](https://doi.org/10.1002/0471725161), Wiley, and
  [Springer](https://doi.org/10.1007/978-0-387-46409-1)). Detailed
  mathematical histories that follow the derivations themselves. The
  reference when the question is who proved what, and how.

#### More recent works

* **Erich L. Lehmann, *Fisher, Neyman, and the Creation of Classical
  Statistics*** (2011, [Springer](https://doi.org/10.1007/978-1-4419-9500-1)).
  The collaboration and conflict that produced the classical theory of
  estimation, testing, and design, by a student of Neyman's school.
* **Stephen M. Stigler, *The Seven Pillars of Statistical Wisdom*** (2016,
  [Harvard University Press](https://doi.org/10.4159/9780674970199)). A
  short essay on the ideas that distinguish statistics as a subject:
  aggregation, information, likelihood, intercomparison, regression,
  design, and residuals.

---

<a id="cks-102"></a>

## 102. Classical Inference: Decision Theory, Estimation, and Testing

Minimaxity, admissibility, unbiasedness, equivariance, and uniformly most
powerful tests are the classical pillars. Exponential families, information,
the comparison of experiments, and simultaneous inference belong with them.
The asymptotic form of the theory is in Section 103; specifically Bayesian
theory is in Section 105, and large-scale multiple testing in Section 107.

### Foundational works

* **Erich L. Lehmann and George Casella, *Theory of Point Estimation***
  (2nd ed., 1998, [Springer](https://doi.org/10.1007/b98854); first ed.,
  Lehmann alone, 1983). Unbiasedness, equivariance, minimaxity, and
  admissibility. The standard research monograph on classical point
  estimation.
* **Erich L. Lehmann and Joseph P. Romano, *Testing Statistical
  Hypotheses*** (4th ed., 2022, [Springer](https://doi.org/10.1007/978-3-030-70578-7);
  first ed., Lehmann alone, 1959). The standard graduate and research
  reference for hypothesis testing. The fourth edition is organised
  into two volumes, on finite-sample and large-sample theory, with
  expanded coverage of multiple testing, high-dimensional testing,
  and permutation and randomization methods.
* **Thomas S. Ferguson, *Mathematical Statistics: A Decision Theoretic
  Approach*** (1967, [Academic
  Press](https://doi.org/10.1016/C2013-0-07705-5)). The classical
  graduate text for decision theory: sufficiency, admissibility,
  minimaxity, and invariant procedures, in a form still readable as a
  course.
* **Abraham Wald, *Statistical Decision Functions*** (1950, Wiley). The
  founding monograph of statistical decision theory.
* **David Blackwell and M. A. Girshick, *Theory of Games and Statistical
  Decisions*** (1954, Wiley;
  [Dover](https://store.doverpublications.com/products/9780486150895)
  reprint, 1979). Games, complete classes, and sufficient statistics, in
  the form the decision-theoretic generation learned them.
* **Lawrence D. Brown, *Fundamentals of Statistical Exponential Families
  with Applications in Statistical Decision Theory*** (1986, [Institute
  of Mathematical Statistics](https://doi.org/10.1214/lnms/1215466757)).
  Exponential families, their convex geometry, and the
  decision-theoretic consequences. The usual citation for the structure
  of an exponential family.
* **Ole E. Barndorff-Nielsen, *Information and Exponential Families in
  Statistical Theory*** (1978, Wiley;
  [Wiley](https://doi.org/10.1002/9781118857281) reissue, 2014). The
  companion monograph: likelihood, observed and expected information,
  and the geometry of exponential families. Higher-order likelihood
  expansions are in Section 103.
* **Solomon Kullback, *Information Theory and Statistics*** (1959,
  Wiley;
  [Dover](https://store.doverpublications.com/products/9780486696843)
  reprint, 1968). Relative entropy as a statistical quantity:
  discrimination information, its additivity and convexity, and its use
  in estimation and testing. The source of the Kullback–Leibler
  divergence as statisticians use it.
* **Johann Pfanzagl, *Parametric Statistical Theory*** (1994, [de
  Gruyter](https://doi.org/10.1515/9783110889765); with the
  collaboration of Ralf Hamböker). Sufficiency, unbiased estimation,
  testing, and the passage to asymptotic distributions. A European
  counterpart to the Lehmann monographs.
* **Friedrich Liese and Klaus-J. Miescke, *Statistical Decision Theory:
  Estimation, Testing, and Selection*** (2008,
  [Springer](https://doi.org/10.1007/978-0-387-73194-0)). A systematic
  monograph on finite-sample decision theory, including selection
  problems, written after Lehmann–Casella.
* **Erik N. Torgersen, *Comparison of Statistical Experiments*** (1991,
  [Cambridge University
  Press](https://doi.org/10.1017/CBO9780511666353)). The large reference
  for deficiency, sufficiency, and the comparison of experiments in the
  sense of Le Cam. The asymptotic theory of experiments is in Section
  103.
* **Rupert G. Miller, Jr., *Simultaneous Statistical Inference*** (2nd
  ed., 1981, [Springer](https://doi.org/10.1007/978-1-4613-8122-8);
  first ed. 1966). The classical monograph on multiple comparisons.
  Large-scale testing, as it developed later, is listed in Section 107.
* **James O. Berger, *Statistical Decision Theory and Bayesian
  Analysis***. Listed in full in Section 105. The decision-theoretic
  half is the graduate reference for admissibility, complete classes,
  and invariance alongside a Bayesian development.

### More recent works

* **Bradley Efron, *Large-Scale Inference: Empirical Bayes Methods for
  Estimation, Testing, and Prediction***. Listed in full in Section 107.
  The book that made empirical Bayes and false-discovery ideas part of
  the common language of large-scale testing.

---

<a id="cks-103"></a>

## 103. Asymptotic Statistics

Contiguity, local asymptotic normality, efficiency, M-estimation,
U-statistics, and empirical processes describe procedures as the sample
size grows; expansions, resampling, and the geometry of statistical models
refine the first-order picture. Subdivision 103A is the first-order theory,
103B its higher-order and resampling refinements. Weak convergence and
empirical-process theory as probability are in Sections 6 and 7; martingale
limit theorems for dependent samples are in Section 108. Books first
published from 2010 on that carry this theory into nonparametric or
high-dimensional models are in Sections 104 and 107.

<a id="cks-103a"></a>

### 103A. First-Order Asymptotics, Statistical Experiments, and Empirical Processes

#### Foundational works

* **Aad W. van der Vaart, *Asymptotic Statistics*** (1998, [Cambridge
  University Press](https://doi.org/10.1017/CBO9780511802256)). The
  modern standard: contiguity, local experiments, efficiency, M- and
  Z-estimators, empirical processes, and an introduction to
  semiparametric models. Also listed in Section 104.
* **Erich L. Lehmann, *Elements of Large-Sample Theory*** (1999,
  [Springer](https://doi.org/10.1007/b98855)). A readable passage from a
  first graduate course to asymptotic arguments, with the measure theory
  kept in the background. It sits between Casella–Berger and van der
  Vaart.
* **Thomas S. Ferguson, *A Course in Large Sample Theory*** (1996,
  [Chapman and Hall](https://doi.org/10.1201/9781315136288)). A
  theorem-proof course in asymptotics, shorter than van der Vaart and
  more formal than Lehmann's *Elements*.
* **Robert J. Serfling, *Approximation Theorems of Mathematical
  Statistics*** (1980, [Wiley](https://doi.org/10.1002/9780470316481)).
  Asymptotic theory for estimators, U-statistics, the delta method, and
  von Mises expansions. The classical reference for these
  approximations.
* **H. A. David and H. N. Nagaraja, *Order Statistics*** (3rd ed.,
  2003, [Wiley](https://doi.org/10.1002/0471722162)). Exact and
  asymptotic distribution theory for ordered samples, quantiles,
  spacings, and extremes, with statistical applications. A reference
  for the sample-ordering arguments used in nonparametric inference
  and tail estimation.
* **A. J. Lee, *U-Statistics: Theory and Practice*** (1990, Marcel
  Dekker; [Routledge](https://doi.org/10.1201/9780203734520) e-book,
  2019). Hoeffding decompositions, distribution theory, and asymptotics
  for U-statistics, including degenerate kernels. A specialised
  reference beyond the chapters in Serfling and van der Vaart.
* **Lucien Le Cam and Grace Lo Yang, *Asymptotics in Statistics: Some
  Basic Concepts*** (2nd ed., 2000,
  [Springer](https://doi.org/10.1007/978-1-4612-1166-2); first ed.
  1990). The readable route into Le Cam's theory: contiguity,
  deficiency, and local experiments, without the bulk of the 1986
  treatise.
* **Lucien Le Cam, *Asymptotic Methods in Statistical Decision Theory***
  (1986, [Springer](https://doi.org/10.1007/978-1-4612-4946-7)). The
  research treatise on statistical experiments, local asymptotic
  normality, and the decision-theoretic form of asymptotic efficiency. A
  demanding research reference, best approached after van der Vaart or
  Le Cam–Yang.
* **I. A. Ibragimov and R. Z. Has'minskii, *Statistical Estimation:
  Asymptotic Theory*** (English ed., 1981,
  [Springer](https://doi.org/10.1007/978-1-4899-0027-2)). Convergence of
  experiments, asymptotic estimation, and the behaviour of estimators
  under local alternatives. The classical research monograph of the
  Russian school.
* **Helmut Strasser, *Mathematical Theory of Statistics: Statistical
  Experiments and Asymptotic Decision Theory*** (1985, [de
  Gruyter](https://doi.org/10.1515/9783110850826)). A measure-theoretic
  development of experiments and their limits, with functional-analytic
  foundations and asymptotic decision theory treated systematically.
* **C. C. Heyde, *Quasi-Likelihood and Its Application: A General
  Approach to Optimal Parameter Estimation*** (1997,
  [Springer](https://doi.org/10.1007/b98823)). Estimating functions,
  their optimality in the sense of Godambe, and asymptotic theory for
  estimating equations in dependent and stochastic-process models.
* **Aad W. van der Vaart and Jon A. Wellner, *Weak Convergence and
  Empirical Processes: With Applications to Statistics***. Listed in full
  in Section 7. The standard statistical reference for weak convergence,
  entropy, and the limit theorems that use them. The second edition
  (2023, [Springer](https://doi.org/10.1007/978-3-031-29040-4); first ed.
  1996) adds generic chaining, concentration, and high-dimensional
  applications.
* **Galen R. Shorack and Jon A. Wellner, *Empirical Processes with
  Applications to Statistics*** (1986, Wiley;
  [SIAM](https://doi.org/10.1137/1.9780898719017) Classics reprint,
  2009). The classical statistician's treatise: weighted empirical
  processes, bounds, and applications to survival and rank statistics.
  Heavier on those applications than van der Vaart–Wellner.
* **Miklós Csörgő and Pál Révész, *Strong Approximations in Probability
  and Statistics*** (1981, [Academic
  Press](https://doi.org/10.1016/C2013-0-10553-3)). Hungarian (KMT)
  construction, strong invariance principles, and their use for
  empirical and quantile processes. The source for coupling-based
  asymptotics of statistics.
* **David Pollard, *Convergence of Stochastic Processes* and *Empirical
  Processes: Theory and Applications***. Listed in full in Section 7.
  Maximal inequalities for M-estimators; the second is the 1990 IMS
  monograph many statistics courses actually assigned.
* **R. M. Dudley, *Uniform Central Limit Theorems***. Listed in full in
  Section 7. Vapnik–Červonenkis classes and Donsker theorems, with
  measurability handled carefully.
* **Sara van de Geer, *Empirical Processes in M-Estimation*** (2000,
  Cambridge University Press). A short monograph aimed at the
  empirical-process arguments for M-estimators, including rates. The
  high-dimensional continuation is listed in Section 107.
* **Anirban DasGupta, *Asymptotic Theory of Statistics and
  Probability*** (2008,
  [Springer](https://doi.org/10.1007/978-0-387-75971-5)). An
  encyclopedic reference: limit theorems, expansions, and a great many
  special topics, to be consulted rather than read through.
* **Peter Hall and C. C. Heyde, *Martingale Limit Theory and Its
  Application***. Listed in full in Section 108. The martingale central
  limit theorem in the form statisticians use.

#### More recent works

* **Jiming Jiang, *Large Sample Techniques for Statistics*** (2nd ed.,
  2022, [Springer](https://doi.org/10.1007/978-3-030-91695-4); first ed.
  2010). Inequalities, limit theorems, martingales, empirical processes,
  and their use for mixed models, time series, and resampling. A
  technique-oriented graduate text with many worked examples.

<a id="cks-103b"></a>

### 103B. Higher-Order Asymptotics, Resampling, and Information Geometry

Edgeworth expansion, saddlepoint approximation, the bootstrap and
subsampling, empirical likelihood, and the differential geometry of
parametric models refine the first-order theory of 103A.

#### Foundational works

* **R. N. Bhattacharya and R. Ranga Rao, *Normal Approximation and
  Asymptotic Expansions*** (1976, Wiley;
  [SIAM](https://doi.org/10.1137/1.9780898719895) Classics reprint,
  2010). Berry–Esseen bounds and Edgeworth expansions for sums of
  independent random vectors. The mathematical basis for the expansions
  used throughout this subdivision.
* **Peter Hall, *The Bootstrap and Edgeworth Expansion*** (1992,
  [Springer](https://doi.org/10.1007/978-1-4612-4384-7)). The research
  monograph that ties the bootstrap to Edgeworth correction. The
  standard citation for the asymptotic theory of resampling.
* **Bradley Efron, *The Jackknife, the Bootstrap, and Other Resampling
  Plans*** (1982, [SIAM](https://doi.org/10.1137/1.9781611970319)). The
  short SIAM monograph in which the bootstrap was set out as a general
  method.
* **Bradley Efron and Robert J. Tibshirani, *An Introduction to the
  Bootstrap*** (1993, [Chapman and
  Hall](https://doi.org/10.1201/9780429246593)). The standard textbook.
  Less theoretical than Hall, and the book from which most readers learn
  the range of the method.
* **A. C. Davison and D. V. Hinkley, *Bootstrap Methods and their
  Application*** (1997, [Cambridge University
  Press](https://doi.org/10.1017/CBO9780511802843)). Bootstrap tests,
  confidence intervals, regression, and dependent observations, with
  theory, worked examples, and computational guidance. A detailed
  methodological companion to Hall's asymptotic monograph.
* **Jun Shao and Dongsheng Tu, *The Jackknife and Bootstrap*** (1995,
  [Springer](https://doi.org/10.1007/978-1-4612-0795-5)). A
  theorem-proof treatment of consistency, higher-order accuracy, and the
  bootstrap for dependent and complex samples.
* **Dimitris N. Politis, Joseph P. Romano, and Michael Wolf,
  *Subsampling*** (1999, [Springer](https://doi.org/10.1007/978-1-4612-1554-7)).
  Estimation of sampling distributions from smaller subsamples,
  including nonstandard limiting laws and dependent observations.
  Gives an alternative where the ordinary bootstrap can fail. Also
  listed in Section 108.
* **S. N. Lahiri, *Resampling Methods for Dependent Data*** (2003,
  [Springer](https://doi.org/10.1007/978-1-4757-3803-2)). Block
  bootstrap methods for time series and spatial data, with their
  consistency and second-order properties. The theoretical reference for
  resampling under dependence. Also listed in Section 108.
* **O. E. Barndorff-Nielsen and D. R. Cox, *Asymptotic Techniques for
  Use in Statistics* and *Inference and Asymptotics*** (1989 and 1994,
  Chapman and Hall: [I](https://doi.org/10.1007/978-1-4899-3424-6),
  [II](https://doi.org/10.1201/9780203750940)). The first develops
  expansions, saddlepoint approximation, and likelihood asymptotics as
  tools; the second is the account of higher-order likelihood inference.
  Read as a pair.
* **Ronald W. Butler, *Saddlepoint Approximations with Applications***
  (2007, [Cambridge University Press](https://doi.org/10.1017/CBO9780511619083)).
  Density, distribution, and conditional saddlepoint approximations, with
  applications to likelihood inference and stochastic systems. The
  book-length reference for the method.
* **Thomas A. Severini, *Likelihood Methods in Statistics*** (2000,
  [Oxford University
  Press](https://doi.org/10.1093/oso/9780198506508.001.0001)).
  Likelihood, conditional and marginal likelihood, pseudo-likelihood,
  and the higher-order corrections to likelihood-ratio inference. A
  graduate route into the Barndorff-Nielsen–Cox circle of ideas.
* **Jayanta K. Ghosh, *Higher Order Asymptotics*** (1994, [Institute of
  Mathematical Statistics and American Statistical
  Association](https://doi.org/10.1214/cbms/1462297300), NSF-CBMS
  Regional Conference Series in Probability and Statistics 4). The IMS
  lecture notes on Edgeworth expansion, second-order efficiency, and
  matching priors. A compact research survey.
* **Art B. Owen, *Empirical Likelihood*** (2001, [Chapman and
  Hall/CRC](https://doi.org/10.1201/9781420036152)). The monograph on
  empirical likelihood: likelihood ratios without a parametric model,
  and their asymptotic chi-squared limits.
* **Robert E. Kass and Paul W. Vos, *Geometrical Foundations of
  Asymptotic Inference*** (1997,
  [Wiley](https://doi.org/10.1002/9781118165980)). Statistical
  manifolds, curvature, and the geometric reading of higher-order
  inference. The statistician's route into information geometry.
* **Shun-ichi Amari, *Differential-Geometrical Methods in Statistics***
  (1985, [Springer](https://doi.org/10.1007/978-1-4612-5056-2), Lecture
  Notes in Statistics 28). Dual connections, exponential and mixture
  families, and higher-order efficiency. An influential account linking
  the geometry of statistical models to asymptotic inference.
* **Shun-ichi Amari and Hiroshi Nagaoka, *Methods of Information
  Geometry*** (English ed., 2000, [American Mathematical
  Society](https://doi.org/10.1090/mmono/191)). The systematic
  mathematical development, written so that a reader can learn the
  geometry without first reconstructing it from papers.
* **N. N. Čencov, *Statistical Decision Rules and Optimal Inference***
  (English ed., 1982, [American Mathematical
  Society](https://doi.org/10.1090/mmono/053); Russian ed. 1972). The
  earlier monograph in which a category of statistical experiments and
  an invariant geometry are used to describe optimal inference.

#### More recent works

* **Louis H. Y. Chen, Larry Goldstein, and Qi-Man Shao, *Normal
  Approximation by Stein's Method***. Listed in full in Section 6.
  Quantitative normal approximation for dependent statistics, an
  alternative to Edgeworth-type arguments.
* **Shun-ichi Amari, *Information Geometry and Its Applications***
  (2016, [Springer](https://doi.org/10.1007/978-4-431-55978-8)). A later
  synthesis, wider than the 1985 lecture notes and more explicit about
  applications.
* **Nihat Ay, Jürgen Jost, Hông Vân Lê, and Lorenz Schwachhöfer,
  *Information Geometry*** (2017,
  [Springer](https://doi.org/10.1007/978-3-319-56478-4)). A rigorous
  foundation of information geometry for finite- and infinite-dimensional
  statistical models. Parametrized measure models, the Fisher metric,
  the Amari–Chentsov tensor, sufficiency, and statistical inequalities
  are central.

---

<a id="cks-104"></a>

## 104. Nonparametric, Semiparametric, and Robust Inference

Infinite-dimensional models, ranks, smoothing, minimax rates, shape
constraints, semiparametric efficiency, and robustness extend the parametric
theory of Sections 102 and 103. Subdivision 104A collects classical
nonparametrics, smoothing, and the modern minimax theory; 104B semiparametric
models and missing data; 104C robust statistics; 104D functional
observations. Nonparametric Bayesian theory is in Section 105, and
high-dimensional and learning-theoretic questions are in Section 107.

<a id="cks-104a"></a>

### 104A. Ranks, Smoothing, Shape Constraints, and Minimax Estimation

Rank tests, density and regression estimation, reproducing kernels, wavelet
methods, order restrictions, and the Gaussian sequence model are the main
finite-sample and asymptotic traditions.

#### Foundational works

* **Erich L. Lehmann, *Nonparametrics: Statistical Methods Based on
  Ranks***, with the special assistance of H. J. M. D'Abrera (revised
  ed., 2006, [Springer](https://doi.org/10.1007/978-0-387-46324-7); first
  ed. 1975, Holden-Day). Rank tests and
  estimates for one-, two-, and several-sample problems, blocked
  comparisons, independence, and randomness. The classical textbook.
* **Jaroslav Hájek, Zbyněk Šidák, and Pranab K. Sen, *Theory of Rank
  Tests*** (2nd ed., 1999, [Academic
  Press](https://doi.org/10.1016/B978-0-12-642350-1.X5017-6); first ed.,
  Hájek and Šidák, 1967). Contiguity, local alternatives, and the
  asymptotic efficiency of rank tests. The research monograph behind
  Lehmann's course, and a source for contiguity itself.
* **Bernard W. Silverman, *Density Estimation for Statistics and Data
  Analysis*** (1986, Chapman and Hall;
  [Routledge](https://doi.org/10.1201/9781315140919) e-book, 2018). The
  short classical account of kernel density estimation.
* **M. P. Wand and M. C. Jones, *Kernel Smoothing*** (1995, [Chapman and
  Hall](https://doi.org/10.1201/b14876)). Kernel density estimation and
  kernel regression, with the bias, variance, and bandwidth theory
  carried further than in Silverman.
* **Luc Devroye and László Györfi, *Nonparametric Density Estimation:
  The L1 View*** (1985, Wiley). Consistency and rates for density
  estimators in total variation, where no smoothness or moment assumption
  is needed for consistency. The mathematical counterpart to the
  mean-square theory of Silverman and Wand–Jones.
* **Jianqing Fan and Irène Gijbels, *Local Polynomial Modelling and Its
  Applications*** (1996, Chapman and Hall;
  [Routledge](https://doi.org/10.1201/9780203748725) e-book, 2018).
  Local polynomials as the basic smoother, with applications and the
  asymptotic theory of the fits.
* **Peter J. Green and Bernard W. Silverman, *Nonparametric Regression
  and Generalized Linear Models: A Roughness Penalty Approach***
  (1994, [Chapman and Hall](https://doi.org/10.1201/b15710)). Smoothing
  splines, roughness penalties, and their extension to generalised
  linear models. A graduate introduction emphasising statistical
  formulation and computation.
* **Grace Wahba, *Spline Models for Observational Data*** (1990,
  [SIAM](https://doi.org/10.1137/1.9781611970128)). Smoothing splines,
  reproducing-kernel Hilbert spaces, regularisation, and selection of
  smoothing parameters. The short mathematical monograph connecting
  spline estimation with inverse problems and kernel methods.
* **Alain Berlinet and Christine Thomas-Agnan, *Reproducing Kernel
  Hilbert Spaces in Probability and Statistics*** (2004,
  [Kluwer](https://doi.org/10.1007/978-1-4419-9096-9)). The theory of
  reproducing kernels and its uses in spline smoothing, Gaussian
  processes, density estimation, and the representation of random
  processes. A natural bridge to the analysis of Section 15.
* **Wolfgang Härdle, Gérard Kerkyacharian, Dominique Picard, and
  Alexander Tsybakov, *Wavelets, Approximation, and Statistical
  Applications*** (1998,
  [Springer](https://doi.org/10.1007/978-1-4612-2222-4), Lecture Notes
  in Statistics). Wavelet bases, Besov spaces, and thresholding
  estimators with their minimax properties. A short account of where
  approximation theory meets nonparametric estimation.
* **Alexandre B. Tsybakov, *Introduction to Nonparametric Estimation***
  (English ed., 2009, [Springer](https://doi.org/10.1007/b13794); French
  ed. 2004). Minimax rates, the Gaussian sequence model, and the
  information-theoretic lower bounds. The standard graduate text for the
  modern theory.
* **Arkadi Nemirovski, *Topics in Non-Parametric Statistics*** (2000,
  [Springer](https://doi.org/10.1007/BFb0106703), Lecture Notes in
  Mathematics, Saint-Flour XXVIII). Minimax estimation over smoothness
  classes, adaptive estimation, and aggregation, by the
  approximation-theoretic route.
* **László Györfi, Michael Kohler, Adam Krzyżak, and Harro Walk, *A
  Distribution-Free Theory of Nonparametric Regression*** (2002,
  [Springer](https://doi.org/10.1007/b97848)). Universal consistency and
  rates for nonparametric regression, under weak assumptions on the
  design and the noise. The research monograph.
* **Luc Devroye and Gábor Lugosi, *Combinatorial Methods in Density
  Estimation*** (2001,
  [Springer](https://doi.org/10.1007/978-1-4613-0125-7)). Density
  estimation through combinatorial and metric entropy arguments, with an
  emphasis on methods that adapt without a smoothness index.
* **Yu. I. Ingster and Irina A. Suslina, *Nonparametric Goodness-of-Fit
  Testing Under Gaussian Models*** (2003,
  [Springer](https://doi.org/10.1007/978-0-387-21580-8), Lecture Notes
  in Statistics 169). Minimax detection boundaries for nonparametric
  alternatives in Gaussian white noise and sequence models. The research
  monograph on nonparametric testing.
* **Tim Robertson, F. T. Wright, and R. L. Dykstra, *Order Restricted
  Statistical Inference*** (1988, Wiley). Isotonic regression, estimation
  and testing under order restrictions, and the chi-bar-squared
  distributions. The classical reference for shape-constrained inference.
* **Larry Wasserman, *All of Nonparametric Statistics*** (2006,
  [Springer](https://doi.org/10.1007/0-387-30623-4)). A one-volume map
  of smoothing, testing, and the Gaussian sequence model. Orientation,
  next to Tsybakov.

#### More recent works

* **Alexander Korostelev and Olga Korosteleva, *Mathematical Statistics:
  Asymptotic Minimax Theory*** (2011, [American Mathematical
  Society](https://doi.org/10.1090/gsm/119), Graduate Studies in
  Mathematics). Parametric and nonparametric minimax lower and upper
  bounds, developed as a graduate course. A shorter route than Tsybakov.
* **Iain M. Johnstone, *Gaussian Estimation: Sequence and Wavelet
  Models*** (unpublished [draft dated 16 September
  2019](https://imjohnstone.su.domains/GE_09_16_19.pdf)). The Gaussian
  sequence model, sparsity, thresholding, and wavelet estimation, with
  risk bounds and minimax theory. Cite the dated draft rather than
  treating it as a published book. Also listed in Section 107.
* **Evarist Giné and Richard Nickl, *Mathematical Foundations of
  Infinite-Dimensional Statistical Models***. Listed in full in Section
  7. Empirical processes, concentration, function spaces, and minimax and
  Bayesian nonparametric theory in one graduate monograph. The recent
  synthesis closest to analysis.
* **Richard J. Samworth and Rajen D. Shah, *Modern Statistical Methods
  and Theory***. Listed in full in Section 107. A graduate course
  joining nonparametric estimation, finite-sample guarantees, and
  high-dimensional methods.
* **Victor Chernozhukov, Alfred Galichon, Marc Hallin, and Marc Henry,
  “Monge–Kantorovich Depth, Quantiles, Ranks and Signs”** (2017,
  [Annals of Statistics 45,
  223–256](https://doi.org/10.1214/16-AOS1450)). Multivariate
  quantiles and ranks defined by transport to a reference measure. The
  origin of the transport-based approach to multivariate
  distribution-free inference.
* **Piet Groeneboom and Geurt Jongbloed, *Nonparametric Estimation under
  Shape Constraints: Estimators, Algorithms and Asymptotics*** (2014,
  [Cambridge University
  Press](https://doi.org/10.1017/CBO9781139020893)). Monotone, convex,
  and other shape-constrained estimators, and the nonstandard
  asymptotics that go with them.

<a id="cks-104b"></a>

### 104B. Semiparametric Models and Missing Data

Efficiency bounds, influence functions, and missing data are the core.
The empirical-process books of 103A are the technical companions.

#### Foundational works

* **Peter J. Bickel, Chris A. J. Klaassen, Ya'acov Ritov, and Jon A.
  Wellner, *Efficient and Adaptive Estimation for Semiparametric
  Models*** (1993, Johns Hopkins University Press;
  [Springer](https://link.springer.com/book/9780387984735) reprint
  1998). Tangent spaces, efficiency bounds, and the construction of
  efficient estimators. The research monograph.
* **Roderick J. A. Little and Donald B. Rubin, *Statistical Analysis
  with Missing Data*** (3rd ed., 2019,
  [Wiley](https://doi.org/10.1002/9781119482260); first ed. 1987).
  Missingness mechanisms, ignorability, likelihood and Bayesian
  inference, EM algorithms, and multiple imputation. The general
  reference for incomplete data, complementing Tsiatis's
  semiparametric approach.
* **Anastasios A. Tsiatis, *Semiparametric Theory and Missing Data***
  (2006, [Springer](https://doi.org/10.1007/0-387-37345-4)). Influence
  functions and augmented inverse-probability estimators, developed for
  missing data and coarsening. The accessible book-length treatment.
  Also listed in Section 109.
* **Mark J. van der Laan and James M. Robins, *Unified Methods for
  Censored Longitudinal Data and Causality*** (2003,
  [Springer](https://doi.org/10.1007/978-0-387-21700-0)). Estimating
  functions and efficiency theory for coarsened data, with censoring and
  time-dependent treatment as the main applications. The research
  monograph behind much of the later semiparametric causal literature.
  Also listed in Section 109.
* **Michael R. Kosorok, *Introduction to Empirical Processes and
  Semiparametric Inference*** (2008,
  [Springer](https://doi.org/10.1007/978-0-387-74978-5)). Empirical
  processes taught in the order a semiparametric argument uses them,
  with Z-estimators and censored data as applications. A bridge from van
  der Vaart–Wellner to the models.
* **Peter J. Bickel and Kjell A. Doksum, *Mathematical Statistics:
  Basic Ideas and Selected Topics***. Listed in full in Section 101.
  Volume II is a textbook route into the semiparametric material.
* **Aad W. van der Vaart, *Asymptotic Statistics***. Listed in full in
  Section 103. The semiparametric chapters are the usual first reading
  before Bickel–Klaassen–Ritov–Wellner.
* **Aad W. van der Vaart and Jon A. Wellner, *Weak Convergence and
  Empirical Processes***. Listed in full in Section 7. The technical
  reference for the empirical-process steps.

#### More recent works

* **Jae Kwang Kim and Jun Shao, *Statistical Methods for Handling
  Incomplete Data*** (2nd ed., 2021, [Chapman and
  Hall/CRC](https://doi.org/10.1201/9780429321740); first ed. 2013).
  Likelihood, EM, imputation, propensity scores, and nonignorable
  missingness, with asymptotic theory for the estimators. A
  theoretical complement to Little–Rubin.

<a id="cks-104c"></a>

### 104C. Robust Statistics

Influence functions, breakdown, M-estimation under contamination,
rank-based robust methods, high-breakdown regression, and outlier
diagnostics form the classical core; robust estimation in high dimension is
the recent frontier.

#### Foundational works

* **Peter J. Huber and Elvezio M. Ronchetti, *Robust Statistics*** (2nd
  ed., 2009, [Wiley](https://doi.org/10.1002/9780470434697); first ed.,
  Huber alone, 1981). M-estimation, influence, and the asymptotic theory
  of robust procedures. The research monograph that organised the
  subject.
* **Frank R. Hampel, Elvezio M. Ronchetti, Peter J. Rousseeuw, and
  Werner A. Stahel, *Robust Statistics: The Approach Based on Influence
  Functions*** (1986, [Wiley](https://doi.org/10.1002/9781118186435)).
  Influence functions, the change-of-variance function, and a broad
  catalogue of robust procedures. The companion to Huber.
* **Jana Jurečková and Pranab Kumar Sen, *Robust Statistical
  Procedures: Asymptotics and Interrelations*** (1996, Wiley). Asymptotic
  representations of M-, L-, and R-estimators and the relations between
  them. The theorem-proof monograph on the asymptotics of robust
  procedures.
* **Thomas P. Hettmansperger and Joseph W. McKean, *Robust Nonparametric
  Statistical Methods*** (2nd ed., 2011, [CRC
  Press](https://doi.org/10.1201/b10451); first ed. 1998). Rank-based
  estimation and testing for location, linear models, and multivariate
  problems. Joins the robust and nonparametric traditions.
* **Peter J. Rousseeuw and Annick M. Leroy, *Robust Regression and
  Outlier Detection*** (1987, [Wiley](https://doi.org/10.1002/0471725382)).
  High-breakdown regression, least-median-of-squares estimation,
  leverage points, and diagnostic methods. A complement to the
  influence-function and asymptotic approaches above.
* **Ricardo A. Maronna, R. Douglas Martin, and Victor J. Yohai, *Robust
  Statistics: Theory and Methods*** (2nd ed., 2019,
  [Wiley](https://doi.org/10.1002/9781119214656), with Matías
  Salibián-Barrera, as *Robust Statistics: Theory and Methods (with R)*;
  first ed. 2006). Location, regression, multivariate estimation, and
  time series, with the theory tied to computation. The second edition
  is the one usually consulted.

#### More recent works

* **Ilias Diakonikolas and Daniel M. Kane, *Algorithmic High-Dimensional
  Robust Statistics*** (2023, [Cambridge University
  Press](https://doi.org/10.1017/9781108943161)). Computationally
  efficient estimators of mean and covariance under adversarial
  contamination in high dimension, with information-theoretic and
  computational lower bounds.

<a id="cks-104d"></a>

### 104D. Functional Data Analysis

Curves and other function-valued observations require estimation of
mean functions, covariance operators, principal components, and
regression relationships. The statistical problems are collected here;
the underlying operator theory is in Sections 15 and 21.

#### Foundational works

* **J. O. Ramsay and B. W. Silverman, *Functional Data Analysis*** (2nd
  ed., 2005, [Springer](https://doi.org/10.1007/b98888); first ed.
  1997). Smoothing and registration of curves, functional principal
  components, and functional regression. The standard methodological
  entry point, with examples motivating the constructions.
* **Frédéric Ferraty and Philippe Vieu, *Nonparametric Functional Data
  Analysis: Theory and Practice*** (2006,
  [Springer](https://doi.org/10.1007/0-387-36620-2)). Kernel methods for
  regression and classification with functional covariates, and the role
  of small-ball probabilities in their rates.

#### More recent works

* **Lajos Horváth and Piotr Kokoszka, *Inference for Functional Data
  with Applications*** (2012, [Springer](https://doi.org/10.1007/978-1-4614-3655-3)).
  Asymptotic theory for functional principal components, tests, change
  points, and dependent functional time series.
* **Tailen Hsing and Randall Eubank, *Theoretical Foundations of
  Functional Data Analysis, with an Introduction to Linear Operators***
  (2015, [Wiley](https://doi.org/10.1002/9781118762547)). Random
  elements in Hilbert spaces, covariance operators, spectral
  perturbation, and asymptotics for functional principal components
  and regression. Supplies the mathematical theory behind the methods.

---

<a id="cks-105"></a>

## 105. Bayesian Statistics and Monte Carlo Methods

Subjective and decision-theoretic foundations, finite-dimensional Bayesian
inference, nonparametric priors, Bayesian inverse problems, and the Monte
Carlo methods that make the theory usable. Subdivision 105A is the
foundational and parametric theory, 105B nonparametric and
infinite-dimensional Bayesian theory, and 105C Monte Carlo and Bayesian
computation. Classical decision theory that is not specifically Bayesian is
in Section 102; general Markov chains are in Section 8.

<a id="cks-105a"></a>

### 105A. Foundations and Parametric Bayesian Theory

#### Foundational works

* **Harold Jeffreys, *Theory of Probability*** (3rd ed., 1961, [Oxford
  University Press](https://doi.org/10.1093/oso/9780198503682.001.0001);
  first ed. 1939). Invariant priors, and Bayesian inference as Jeffreys
  formulated it. The third edition is the one consulted. A founding
  book, not a modern textbook.
* **Leonard J. Savage, *The Foundations of Statistics*** (1954, Wiley;
  2nd revised ed.,
  [Dover](https://store.doverpublications.com/products/9780486623498),
  1972). Subjective probability and the decision-theoretic reading of
  inference. The usual citation for the axiomatic foundation.
* **Bruno de Finetti, *Theory of Probability*** (2 volumes, English ed.,
  1974–1975, Wiley; one-volume
  [Wiley](https://doi.org/10.1002/9781119286387) reissue, 2017).
  Exchangeability and the subjective theory, at book length. Listed for
  the foundation it supplies; it is not a manual of Bayesian methods.
* **Morris H. DeGroot, *Optimal Statistical Decisions*** (1970,
  McGraw-Hill; [Wiley](https://doi.org/10.1002/0471729000) Classics
  reissue, 2004). Conjugate analysis and Bayesian decision theory in the
  form of a classical textbook. Berger and Robert, below, are the books
  a course uses now.
* **George E. P. Box and George C. Tiao, *Bayesian Inference in
  Statistical Analysis*** (1973, Addison-Wesley;
  [Wiley](https://doi.org/10.1002/9781118033197) reprint, 1992).
  Noninformative priors, robustness to assumptions, and Bayesian
  analysis of the standard normal-theory models. The classical
  demonstration that Bayesian methods handle the textbook problems.
* **James O. Berger, *Statistical Decision Theory and Bayesian
  Analysis*** (2nd ed., 1985,
  [Springer](https://doi.org/10.1007/978-1-4757-4286-2); first ed.
  1980). Admissibility, complete classes, hierarchical and empirical
  Bayes, and robust Bayesian analysis. The standard graduate reference
  linking decision theory to Bayesian inference. Also listed in Section
  102.
* **Jayanta K. Ghosh, Mohan Delampady, and Tapas Samanta, *An
  Introduction to Bayesian Analysis: Theory and Methods*** (2006,
  [Springer](https://doi.org/10.1007/978-0-387-35433-0)). A graduate
  course in Bayesian decision theory, prior choice, large-sample
  approximations, and model selection, with computation and examples.
  A more compact route into the theory than Bernardo–Smith.
* **José M. Bernardo and Adrian F. M. Smith, *Bayesian Theory*** (1994,
  [Wiley](https://doi.org/10.1002/9780470316870)). The foundational
  treatise: exchangeability, information, reference analysis, and the
  decision-theoretic development. A reference more than a first course.
* **Christian P. Robert, *The Bayesian Choice: From Decision-Theoretic
  Foundations to Computational Implementation*** (2nd ed., 2001,
  [Springer](https://doi.org/10.1007/0-387-71599-1); paperback reprint
  2007; first ed. 1994). Decision theory, priors, model choice, and the
  first generation of Markov chain Monte Carlo, in one graduate text.
* **Andrew Gelman, John B. Carlin, Hal S. Stern, David B. Dunson, Aki
  Vehtari, and Donald B. Rubin, *Bayesian Data Analysis*** (3rd ed.,
  2013, [Chapman and Hall/CRC](https://doi.org/10.1201/b16018); first
  ed. 1995). The standard reference for Bayesian modelling practice.
  Hierarchical models and computation, rather than a measure-theoretic
  treatise; the third edition is the one usually consulted.

<a id="cks-105b"></a>

### 105B. Nonparametric Bayes, Posterior Asymptotics, and Inverse Problems

Priors on functions and distributions, posterior consistency and contraction,
and Bayesian formulations of inverse problems for differential equations.

#### Foundational works

* **Jayanta K. Ghosh and R. V. Ramamoorthi, *Bayesian Nonparametrics***
  (2003, [Springer](https://doi.org/10.1007/b97842)). Dirichlet
  processes, consistency, and the early asymptotic theory of
  nonparametric priors. The first systematic monograph.
* **Jari Kaipio and Erkki Somersalo, *Statistical and Computational
  Inverse Problems*** (2005,
  [Springer](https://doi.org/10.1007/b138659), Applied Mathematical
  Sciences). Inverse problems posed as Bayesian inference, with priors,
  posterior computation, and modelling errors. The applied entry point;
  the analytic theory of ill-posed problems is in Sections 22 and 25.

#### More recent works

* **Subhashis Ghosal and Aad van der Vaart, *Fundamentals of
  Nonparametric Bayesian Inference*** (2017, [Cambridge University
  Press](https://doi.org/10.1017/9781139029834)). Priors on functions
  and on distributions, posterior consistency, and contraction rates.
  The research treatise.
* **Nils Lid Hjort, Chris Holmes, Peter Müller, and Stephen G. Walker
  (eds.), *Bayesian Nonparametrics*** (2010, [Cambridge University
  Press](https://doi.org/10.1017/CBO9780511802478)). A coordinated set
  of surveys, useful as a map of the subject before Ghosal–van der
  Vaart.
* **Richard Nickl, *Bayesian Non-linear Statistical Inverse Problems***
  (2023, [EMS Press](https://doi.org/10.4171/ZLAM/30), Zurich Lectures
  in Advanced Mathematics). Posterior consistency, contraction rates, and
  Bernstein–von Mises theorems for parameters of PDEs, using elliptic
  regularity and Gaussian process priors. A short research account where
  nonparametric statistics meets PDE analysis.

<a id="cks-105c"></a>

### 105C. Monte Carlo and Bayesian Computation

Monte Carlo, Markov chain Monte Carlo, sequential Monte Carlo, and
variational approximation, with their convergence theory and
statistical uses. Langevin algorithms and their non-asymptotic
complexity, interacting-particle samplers, and diffusion-based
generation are in Section 112.

#### Foundational works

* **Christian P. Robert and George Casella, *Monte Carlo Statistical
  Methods*** (2nd ed., 2004,
  [Springer](https://doi.org/10.1007/978-1-4757-4145-2); first ed.
  1999). Rejection, importance sampling, and Markov chain Monte Carlo,
  with the convergence theory a statistician needs. The standard
  monograph.
* **Jun S. Liu, *Monte Carlo Strategies in Scientific Computing***
  (2001, [Springer](https://doi.org/10.1007/978-0-387-76371-2)).
  Sequential Monte Carlo, Markov chains, and data-augmentation
  algorithms. A complement to Robert–Casella, closer to the algorithms.
* **Søren Asmussen and Peter W. Glynn, *Stochastic Simulation:
  Algorithms and Analysis*** (2007, [Springer](https://doi.org/10.1007/978-0-387-69033-9)).
  Output analysis, variance reduction, rare-event simulation, and
  Markov chain Monte Carlo, with the probabilistic proofs. The
  mathematical reference for simulation outside the Bayesian setting.
* **Pierre Del Moral, *Feynman–Kac Formulae: Genealogical and
  Interacting Particle Systems with Applications*** (2004,
  [Springer](https://doi.org/10.1007/978-1-4684-9393-1)). Interacting
  particle approximations of Feynman–Kac measures, with limit theorems
  and stability. The mathematical theory behind particle filters.
* **Sean Meyn and Richard L. Tweedie, *Markov Chains and Stochastic
  Stability***. Listed in full in Section 8. Drift and minorization
  conditions, the tools for proving that a Markov chain Monte Carlo
  algorithm converges geometrically.

* **David A. Levin, Yuval Peres, and Elizabeth L. Wilmer, *Markov Chains
  and Mixing Times***. Listed in full in Section 8. Spectral gaps,
  coupling, and mixing-time bounds, the quantitative side of Markov
  chain Monte Carlo convergence.

#### More recent works

* **Steve Brooks, Andrew Gelman, Galin L. Jones, and Xiao-Li Meng
  (eds.), *Handbook of Markov Chain Monte Carlo*** (2011, [Chapman and
  Hall/CRC](https://doi.org/10.1201/b10905); [2nd
  ed.](https://doi.org/10.1201/9781003453420), 2026, eds. Radu V. Craiu,
  Dootika Vats, Galin L. Jones, Steve Brooks, Andrew Gelman, and Xiao-Li
  Meng). Survey chapters on convergence, algorithms, and applications. A
  reference, not a textbook.
* **Randal Douc, Eric Moulines, Pierre Priouret, and Philippe Soulier,
  *Markov Chains*** (2018, [Springer](https://doi.org/10.1007/978-3-319-97704-1)).
  General state-space Markov chains, with convergence rates, coupling,
  and limit theorems, and Monte Carlo methods as a central motivation. A
  modern successor to Meyn–Tweedie for the statistical reader.
* **David M. Blei, Alp Kucukelbir, and Jon D. McAuliffe, “Variational
  Inference: A Review for Statisticians”** (2017, [Journal of the
  American Statistical Association 112,
  859–877](https://doi.org/10.1080/01621459.2017.1285773)).
  Mean-field and stochastic variational inference, with their relation
  to Markov chain Monte Carlo. The standard introduction for
  statisticians; the exponential-family theory is in
  Wainwright–Jordan, Section 113.
* **Nicolas Chopin and Omiros Papaspiliopoulos, *An Introduction to
  Sequential Monte Carlo*** (2020,
  [Springer](https://doi.org/10.1007/978-3-030-47845-2)). Importance
  sampling, resampling, particle filters, and particle Markov chain
  Monte Carlo, with stability and limit theory. A graduate treatment
  of simulation for filtering and more general sequences of target
  distributions. Also listed in Section 108.

---

<a id="cks-106"></a>

## 106. Linear Models, Multivariate Analysis, and Experimental Design

Linear and generalised linear models, mixtures, classical multivariate
analysis, invariance, graphical models, directional and shape data, and the
theory of experimental design. High-dimensional covariance and sparsity are
in Section 107; causal uses of graphical models are in Section 109.

<a id="cks-106a"></a>

### 106A. Regression, Generalised Linear Models, and Mixtures

Linear, generalised linear, additive, and mixed models, quantile
regression, and finite mixtures.

#### Foundational works

* **C. Radhakrishna Rao, *Linear Statistical Inference and Its
  Applications*** (2nd ed., 1973,
  [Wiley](https://doi.org/10.1002/9780470316436); first ed. 1965). Least
  squares, the linear model, and a wide circle of estimation and testing
  theory around it. The classical synthesis.
* **Henry Scheffé, *The Analysis of Variance*** (1959, Wiley;
  [Wiley](https://www.wiley.com/en-us/The+Analysis+of+Variance-p-9780471345053)
  Classics reprint, 1999). Fixed and random effects, multiple
  comparisons, and the geometry of the analysis of variance. The
  classical monograph.
* **George A. F. Seber and Alan J. Lee, *Linear Regression Analysis***
  (2nd ed., 2003, [Wiley](https://doi.org/10.1002/9780471722199); first
  ed., Seber alone, 1977). The standard reference for the linear
  regression model: estimation, hypothesis tests, diagnostics, and the
  distribution theory.
* **Ronald Christensen, *Plane Answers to Complex Questions: The Theory
  of Linear Models*** (5th ed., 2020,
  [Springer](https://doi.org/10.1007/978-3-030-32097-3); first ed.
  1987). Linear models through projections and vector-space geometry.
  A graduate course, revised several times; the fifth edition is the
  one usually consulted.
* **Shayle R. Searle, George Casella, and Charles E. McCulloch,
  *Variance Components*** (1992,
  [Wiley](https://doi.org/10.1002/9780470316856)). ANOVA, maximum
  likelihood, and REML estimation of variance components, and prediction
  of random effects. The classical reference for random-effects models.
* **Peter McCullagh and John A. Nelder, *Generalized Linear Models***
  (2nd ed., 1989, [Chapman and
  Hall](https://doi.org/10.1007/978-1-4899-3242-6); first ed. 1983).
  Exponential dispersion families, the GLM, quasi-likelihood, and the
  asymptotic theory of the fits. The book that fixed the subject.
* **Trevor Hastie and Robert Tibshirani, *Generalized Additive Models***
  (1990, Chapman and Hall;
  [Routledge](https://doi.org/10.1201/9780203753781) reissue, 2017).
  Additive predictors fitted by backfitting smoothers, within the
  generalised linear model framework. The monograph that introduced the
  class.
* **Alan Agresti, *Categorical Data Analysis*** (3rd ed., 2013,
  [Wiley](https://www.wiley.com/en-us/Categorical+Data+Analysis%2C+3rd+Edition-p-9780470463635);
  first ed. 1990). Log-linear models, logistic regression, and
  contingency tables. The standard reference; the third edition is the
  one usually consulted.
* **Jiming Jiang and Thuan Nguyen, *Linear and Generalized Linear Mixed
  Models and Their Applications*** (2nd ed., 2021,
  [Springer](https://doi.org/10.1007/978-1-0716-1282-8); first ed.,
  Jiang alone, 2007). Prediction, estimation, and selection for mixed
  models. The theoretical monograph; the second edition is the one
  usually consulted.
* **Roger Koenker, *Quantile Regression*** (2005, [Cambridge
  University Press](https://doi.org/10.1017/CBO9780511754098)).
  Conditional quantiles, convex optimisation, rank-based inference,
  asymptotic theory, and nonparametric extensions. The standard
  monograph on regression beyond the conditional mean.
* **Geoffrey McLachlan and David Peel, *Finite Mixture Models***
  (2000, [Wiley](https://doi.org/10.1002/0471721182)). Identifiability,
  likelihood estimation, the EM algorithm, selection of the number of
  components, and model-based clustering. The reference for latent
  subpopulations and the nonregular inference problems they produce.

#### More recent works

* **Alan Agresti, *Foundations of Linear and Generalized Linear
  Models*** (2015,
  [Wiley](https://www.wiley.com/en-us/Foundations+of+Linear+and+Generalized+Linear+Models-p-9781118730034)).
  A shorter, more mathematical course in linear models and GLMs than
  Agresti's categorical-data treatise.

<a id="cks-106b"></a>

### 106B. Multivariate Analysis, Invariance, and Graphical Models

Wishart theory, group methods, conditional independence, graphical
structure, algebraic methods, and data on spheres, Stiefel and
Grassmann manifolds, and shape spaces. Nonparametric and Riemannian
statistics on manifolds are in 110A. Graphical representations of
interventions and causal assumptions are in Section 109.

#### Foundational works

* **Theodore W. Anderson, *An Introduction to Multivariate Statistical
  Analysis*** (3rd ed., 2003,
  [Wiley](https://www.wiley.com/en-us/An+Introduction+to+Multivariate+Statistical+Analysis%2C+3rd+Edition-p-9780471360919);
  first ed. 1958). The classical treatise: the multivariate normal
  model, Wishart distributions, correlation, and multivariate tests. The
  third edition is the one consulted.
* **K. V. Mardia, J. T. Kent, and J. M. Bibby, *Multivariate Analysis***
  (1979, Academic Press; [2nd
  ed.](https://www.wiley.com/en-us/Multivariate+Analysis%2C+2nd+Edition-p-9781118738023),
  2024, Wiley, by Kanti V. Mardia, John T. Kent, and Charles C. Taylor).
  Distribution theory, inference, and the descriptive methods of multivariate
  analysis — principal components, factor analysis, discrimination, and
  clustering. A standard graduate text, less specialised than Anderson.
* **Robb J. Muirhead, *Aspects of Multivariate Statistical Theory***
  (1982, [Wiley](https://doi.org/10.1002/9780470316559)). Invariance,
  zonal polynomials, and hypergeometric functions of matrix argument.
  The mathematical standard beyond Anderson.
* **Morris L. Eaton, *Multivariate Statistics: A Vector Space
  Approach*** (1983, Wiley; [Institute of Mathematical
  Statistics](https://doi.org/10.1214/lnms/1196285102) reprint, 2007).
  Coordinate-free linear models and multivariate theory. The reprint is
  the version usually obtained.
* **Martin Bilodeau and David Brenner, *Theory of Multivariate
  Statistics*** (1999, [Springer](https://doi.org/10.1007/b97615)). A
  shorter rigorous course: the multivariate normal model, invariance,
  and the classical tests, with less special-function machinery than
  Muirhead.
* **Steffen L. Lauritzen, *Graphical Models*** (2nd ed., 2026,
  [Oxford University Press](https://doi.org/10.1093/9780191775284.001.0001);
  first ed. 1996). Conditional independence, Markov properties,
  graphical log-linear and Gaussian models, and models for mixed data.
  The second edition adds a chapter on structure estimation. A
  mathematical foundation for graphical modelling. Also listed in
  Sections 107 and 109.
* **Morris L. Eaton, *Group Invariance Applications in Statistics***
  (1989, [Institute of Mathematical Statistics and American Statistical
  Association](https://doi.org/10.1214/cbms/1462061029), NSF-CBMS
  Regional Conference Series in Probability and Statistics 1). The IMS
  monograph on invariance in statistical models. The usual reference
  when an equivariant procedure has to be derived rather than quoted.
* **Persi Diaconis, *Group Representations in Probability and
  Statistics*** (1988, [Institute of Mathematical
  Statistics](https://doi.org/10.1214/lnms/1215467407)). Representation
  theory as a tool for probability and statistics: Fourier analysis on
  finite groups, and random walks that produce statistical models.
  Lecture notes, and a standard citation.
* **Robert A. Wijsman, *Invariant Measures on Groups and Their Use in
  Statistics*** (1990, [Institute of Mathematical
  Statistics](https://doi.org/10.1214/lnms/1215540653), Lecture
  Notes–Monograph Series 14). Haar measure and its statistical uses, in
  the detail Eaton's monograph does not attempt.
* **Yasuko Chikuse, *Statistics on Special Manifolds*** (2003,
  [Springer](https://doi.org/10.1007/978-0-387-21540-2), Lecture Notes
  in Statistics). Distributions, estimation, and asymptotics on the
  Stiefel and Grassmann manifolds. The classical special-manifold theory
  that the later geometric statistics extends.
* **Kanti V. Mardia and Peter E. Jupp, *Directional Statistics*** (2000,
  [Wiley](https://doi.org/10.1002/9780470316979)). Distributions on
  circles, spheres, and other manifolds, with estimation, testing, and
  invariance. The standard reference for data that are directions or
  rotations.
* **Ian L. Dryden and Kanti V. Mardia, *Statistical Shape Analysis***
  (2nd ed., 2016, [Wiley](https://doi.org/10.1002/9781119072492), as
  *Statistical Shape Analysis, with Applications in R*; first ed. 1998).
  Kendall's shape spaces, Procrustes analysis, and distributions of
  shape. The reference for statistics on these non-Euclidean spaces.

#### More recent works

* **Yasunori Fujikoshi, Vladimir V. Ulyanov, and Ryoichi Shimizu,
  *Multivariate Statistics: High-Dimensional and Large-Sample
  Approximations*** (2010,
  [Wiley](https://doi.org/10.1002/9780470539873)). Asymptotic expansions
  and high-dimensional approximations for classical multivariate
  procedures. Also listed in Section 107.
* **Seth Sullivant, *Algebraic Statistics*** (2018, [American Mathematical
  Society](https://doi.org/10.1090/gsm/194), Graduate Studies in
  Mathematics). Exponential families, graphical models, and exact tests
  studied through polynomial ideals and varieties. The graduate text of
  the algebraic approach to statistical models.

<a id="cks-106c"></a>

### 106C. Experimental Design

Randomisation, optimality criteria, information matrices, and the
combinatorial structure of factorial experiments.

#### Foundational works

* **D. R. Cox and Nancy Reid, *The Theory of the Design of
  Experiments*** (2000, [Chapman and
  Hall/CRC](https://doi.org/10.1201/9781420035834)). Randomisation,
  blocking, factorial structure, and the relation between design and
  analysis. A conceptual foundation to read before the specialised
  theory of optimal information matrices.
* **S. D. Silvey, *Optimal Design*** (1980, [Chapman and
  Hall](https://doi.org/10.1007/978-94-009-5912-5)). A short
  introduction to approximate design theory and optimality criteria.
* **V. V. Fedorov, *Theory of Optimal Experiments*** (English ed., 1972,
  [Academic
  Press](https://shop.elsevier.com/books/theory-of-optimal-experiments/fedorov/978-0-12-250750-2)).
  Continuous designs, the Kiefer–Wolfowitz equivalence theorem, and
  iterative construction of optimal designs. The early systematic
  monograph.
* **Friedrich Pukelsheim, *Optimal Design of Experiments*** (1993,
  Wiley; [SIAM](https://doi.org/10.1137/1.9780898719109) reprint, 2006).
  Information matrices, Loewner order, and the general equivalence
  theory. The research monograph.
* **R. A. Bailey, *Design of Comparative Experiments*** (2008,
  [Cambridge University
  Press](https://doi.org/10.1017/cbo9780511611483)). Factorial
  structure, orthogonal block structures, and the algebra of comparative
  experiments. A graduate text with the combinatorics kept visible.
* **A. S. Hedayat, N. J. A. Sloane, and John Stufken, *Orthogonal
  Arrays: Theory and Applications*** (1999,
  [Springer](https://doi.org/10.1007/978-1-4612-1478-6)). Existence and
  construction of orthogonal arrays through codes, finite fields, and
  difference schemes. The reference for the combinatorics behind
  fractional factorial designs.

#### More recent works

* **Ching-Shui Cheng, *Theory of Factorial Design: Single- and
  Multi-Stratum Experiments*** (2014, [Chapman and
  Hall/CRC](https://doi.org/10.1201/b16253)). Regular and nonregular
  factorials, minimum aberration, and experiments with several error
  strata. A systematic research monograph.

---

<a id="cks-107"></a>

## 107. High-Dimensional Statistics and Statistical Learning

Estimation and testing when the number of parameters is large compared
with the sample, and the learning theory that grew from the same
empirical-process and complexity ideas. Subdivision 107A is the
statistical theory of high-dimensional models and large-scale testing; 107B
is statistical learning theory. The probabilistic toolkits — concentration,
chaining, and random matrices — are developed in Section 7 and cited here
where a statistician opens them. General machine-learning texts,
graphical-model computation, and bandits have their primary home in
Section 113, and optimization algorithms in Section 114; they are
cross-referenced here where the theory uses them.

<a id="cks-107a"></a>

### 107A. High-Dimensional and Large-Scale Inference

Sparsity, regularised estimation, covariance in high dimension, model
selection, information-theoretic lower bounds, and testing many hypotheses
at once. Much of the textbook literature appeared from 2010 onward;
earlier monographs developed model-selection penalties, concentration, and
multiple testing.

#### Foundational works

* **Pascal Massart, *Concentration Inequalities and Model Selection***
  (2007, [Springer](https://doi.org/10.1007/978-3-540-48503-2),
  Saint-Flour XXXIII lecture course). Concentration of empirical
  processes, penalised estimation, oracle inequalities, and adaptive
  model selection. An important precursor to the later
  high-dimensional textbooks.
* **Sandrine Dudoit and Mark J. van der Laan, *Multiple Testing
  Procedures with Applications to Genomics*** (2008,
  [Springer](https://doi.org/10.1007/978-0-387-49317-6)). Type I error
  control for large families of hypotheses, with the multiple-testing
  theory developed for high-throughput data. The pre-2010 monograph.
* **Aad W. van der Vaart and Jon A. Wellner, *Weak Convergence and
  Empirical Processes***. Listed in full in Section 7. Entropy and
  maximal inequalities in the form the high-dimensional arguments use.
* **Zhidong Bai and Jack W. Silverstein, *Spectral Analysis of Large
  Dimensional Random Matrices***. Listed in full in Section 7. Limiting
  spectral distributions of sample covariance matrices, the starting
  point for high-dimensional multivariate analysis.

#### More recent works

* **Martin J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic
  Viewpoint*** (2019, [Cambridge University
  Press](https://doi.org/10.1017/9781108627771)). Sparse linear models,
  concentration, and non-asymptotic bounds, organised as a graduate
  course. The standard text. Also listed in 107B.
* **Peter Bühlmann and Sara van de Geer, *Statistics for
  High-Dimensional Data: Methods, Theory and Applications*** (2011,
  [Springer](https://doi.org/10.1007/978-3-642-20192-9)). The Lasso and
  its relatives, with oracle inequalities and the empirical-process
  arguments. A systematic reference for sparse estimation and variable
  selection.
* **Richard J. Samworth and Rajen D. Shah, *Modern Statistical Methods
  and Theory: An Introduction to Nonparametric and High-Dimensional
  Statistics*** (2026, [Cambridge University
  Press](https://doi.org/10.1017/9781009160421); open access).
  Finite-sample theory for sparse regression, smoothing, kernel
  methods, conditional independence, and shape constraints, together
  with minimax lower bounds. A recent graduate course linking Sections
  104, 106, and 107. Also listed in Section 104.
* **Christophe Giraud, *Introduction to High-Dimensional Statistics***
  (2nd ed., 2021, [Chapman and
  Hall/CRC](https://doi.org/10.1201/9781003158745); first ed. 2015). A
  shorter graduate course: model selection, sparsity, aggregation, and
  minimax lower bounds.
* **Trevor Hastie, Robert Tibshirani, and Martin Wainwright,
  *Statistical Learning with Sparsity: The Lasso and Generalizations***
  (2015, [Chapman and Hall/CRC](https://doi.org/10.1201/b18401)). The
  Lasso, generalised linear models, and structured sparsity, written as
  the shared account of the methods and their theory. Also listed in
  107B.
* **Sara van de Geer, *Estimation and Testing Under Sparsity*** (2016,
  [Springer](https://doi.org/10.1007/978-3-319-32774-7), Lecture Notes in
  Mathematics, Saint-Flour XLV). Sharp oracle inequalities for the Lasso
  and its relatives, and confidence intervals by de-sparsifying. The
  concise research account, continuing *Empirical Processes in
  M-Estimation*.
* **Bradley Efron, *Large-Scale Inference: Empirical Bayes Methods for
  Estimation, Testing, and Prediction*** (2010, [Cambridge University
  Press](https://doi.org/10.1017/cbo9780511761362)). Empirical Bayes,
  false-discovery rates, and estimation after testing, at the scale of
  thousands of simultaneous problems. Also listed in Section 102.
* **Thorsten Dickhaus, *Simultaneous Statistical Inference: With
  Applications in the Life Sciences*** (2014,
  [Springer](https://doi.org/10.1007/978-3-642-45182-9)). Familywise error
  and false discovery rate control, their dependence assumptions, and
  simultaneous confidence regions. A theoretical account of multiple
  testing that updates Miller (Section 102).
* **Jianfeng Yao, Shurong Zheng, and Zhidong Bai, *Large Sample
  Covariance Matrices and High-Dimensional Data Analysis*** (2015,
  [Cambridge University Press](https://doi.org/10.1017/CBO9781107588080)).
  Random-matrix limits and fluctuations for sample covariance
  matrices, with applications to testing, spectral estimation, and
  spiked models. The statistical continuation of the random-matrix
  references in Section 7.
* **Yasunori Fujikoshi, Vladimir V. Ulyanov, and Ryoichi Shimizu,
  *Multivariate Statistics: High-Dimensional and Large-Sample
  Approximations***. Listed in full in Section 106. High-dimensional
  approximations to the classical multivariate procedures.
* **Yury Polyanskiy and Yihong Wu, *Information Theory: From Coding to
  Learning*** (2025, [Cambridge University
  Press](https://doi.org/10.1017/9781108966351)). Information measures,
  their variational characterisations, and their use for minimax lower
  bounds, density estimation, and hypothesis testing, alongside the
  coding theorems. An information-theory graduate text with a
  substantial statistical-learning part.
* **Jianqing Fan, Runze Li, Cun-Hui Zhang, and Hui Zou, *Statistical
  Foundations of Data Science*** (2020, [Chapman and
  Hall/CRC](https://doi.org/10.1201/9780429096280)). A broad graduate
  text joining classical theory to high-dimensional and learning topics.
  A map of the area, alongside the sharper monographs above.
* **Roman Vershynin, *High-Dimensional Probability: An Introduction with
  Applications in Data Science***. Listed in full in Section 7.
  Concentration, random vectors and matrices, and bounds for random
  processes, with applications to covariance estimation and learning.
  The second edition (2026, [Cambridge University
  Press](https://doi.org/10.1017/9781009490672); first ed. 2018) expands
  the prerequisites and exercises.
* **Stéphane Boucheron, Gábor Lugosi, and Pascal Massart,
  *Concentration Inequalities: A Nonasymptotic Theory of
  Independence***. Listed in full in Section 7. The systematic account
  of the concentration inequalities used throughout this subdivision.
* **Joel A. Tropp, *An Introduction to Matrix Concentration
  Inequalities***. Listed in full in Section 7. Matrix Bernstein and
  Chernoff bounds, the tools behind covariance estimation and
  randomized matrix algorithms (114B).
* **Simon Foucart and Holger Rauhut, *A Mathematical Introduction to
  Compressive Sensing***. Listed in full in Section 29. Sparse recovery,
  restricted isometry, and random measurement matrices, including
  stability under noise and approximate sparsity.
* **Iain M. Johnstone, *Gaussian Estimation: Sequence and Wavelet
  Models***. Listed in full in Section 104. The Gaussian sequence model
  is a canonical setting for studying sparsity, thresholding, and minimax
  estimation, connecting finite normal-means problems with infinite
  sequences and nonparametric function estimation.
* **Evarist Giné and Richard Nickl, *Mathematical Foundations of
  Infinite-Dimensional Statistical Models***. Listed in full in Section
  7. Concentration and empirical processes in the form closest to the
  nonparametric theory.

<a id="cks-107b"></a>

### 107B. Statistical Learning Theory

Uniform convergence over function classes, Vapnik–Chervonenkis theory,
kernel methods, conformal prediction, and online prediction. The
methodological texts of machine learning are in 113A, and bandits and
reinforcement learning in 113D.

#### Foundational works

* **Vladimir N. Vapnik, *Statistical Learning Theory*** (1998,
  [Wiley](https://www.wiley.com/en-us/Statistical+Learning+Theory-p-9780471030034)).
  The research monograph on empirical risk minimisation, VC dimension,
  and structural risk minimisation. *The Nature of Statistical Learning
  Theory* (2nd ed., 2000,
  [Springer](https://doi.org/10.1007/978-1-4757-3264-1); first ed. 1995)
  is the shorter conceptual account.
* **Luc Devroye, László Györfi, and Gábor Lugosi, *A Probabilistic
  Theory of Pattern Recognition*** (1996,
  [Springer](https://doi.org/10.1007/978-1-4612-0711-5)). Pattern
  recognition through probability: consistency, VC classes, and error
  bounds. The mathematical textbook of that theory.
* **Trevor Hastie, Robert Tibshirani, and Jerome Friedman, *The
  Elements of Statistical Learning***. Listed in full in 113A. The
  methodological map of the methods whose theory this subdivision
  develops.
* **Martin Anthony and Peter L. Bartlett, *Neural Network Learning:
  Theoretical Foundations*** (1999, [Cambridge University
  Press](https://doi.org/10.1017/cbo9780511624216)). VC and
  fat-shattering dimension, and learning bounds for networks, in the
  theorem-proof form of the 1990s.
* **Bernhard Schölkopf and Alexander J. Smola, *Learning with Kernels***
  (2002, [MIT Press](https://doi.org/10.7551/mitpress/4175.001.0001)).
  Positive definite kernels, support vector machines, regularisation,
  and kernel principal components. The standard reference for kernel
  methods at their formation.
* **Felipe Cucker and Ding-Xuan Zhou, *Learning Theory: An Approximation
  Theory Viewpoint*** (2007, [Cambridge University
  Press](https://doi.org/10.1017/cbo9780511618796)). Sample and
  approximation error for regularised least squares in
  reproducing-kernel Hilbert spaces, with covering-number estimates.
  Learning theory as analysts would write it.
* **Nicolò Cesa-Bianchi and Gábor Lugosi, *Prediction, Learning, and
  Games*** (2006, [Cambridge University
  Press](https://doi.org/10.1017/cbo9780511546921)). Online prediction,
  regret, and the minimax theory of sequential decisions. The standard
  monograph.
* **Ingo Steinwart and Andreas Christmann, *Support Vector Machines***
  (2008, [Springer](https://doi.org/10.1007/978-0-387-77242-4)).
  Kernels, reproducing-kernel Hilbert spaces, and the statistical theory
  of support vector machines. The research monograph.
* **Vladimir Vovk, Alexander Gammerman, and Glenn Shafer, *Algorithmic
  Learning in a Random World*** (2nd ed., 2022,
  [Springer](https://doi.org/10.1007/978-3-031-06649-8); first ed.
  2005). Conformal prediction, prediction sets with finite-sample
  marginal coverage under exchangeability, and tests of randomness.
  The second edition extends the treatment to predictive distributions
  and tests for changes in distribution.

#### More recent works

* **Vladimir Koltchinskii, *Oracle Inequalities in Empirical Risk
  Minimization and Sparse Recovery Problems*** (2011,
  [Springer](https://doi.org/10.1007/978-3-642-22147-7), Lecture Notes in
  Mathematics, Saint-Flour XXXVIII). Local Rademacher complexities,
  excess-risk bounds, and sparse recovery, by the empirical-process
  route. The research account of the localisation method.
* **Shai Shalev-Shwartz and Shai Ben-David, *Understanding Machine
  Learning: From Theory to Algorithms*** (2014, [Cambridge University
  Press](https://doi.org/10.1017/cbo9781107298019)). A graduate text
  from PAC bounds and VC theory to kernels, boosting, and online
  learning.
* **Mehryar Mohri, Afshin Rostamizadeh, and Ameet Talwalkar,
  *Foundations of Machine Learning*** (2nd ed., 2018, [MIT
  Press](https://doi.org/10.7551/mitpress/10290.001.0001); first ed.
  2012). A theorem-proof course, with Rademacher complexity and kernel
  methods emphasised. The second edition is the one usually consulted.
* **Tor Lattimore and Csaba Szepesvári, *Bandit Algorithms***. Listed
  in full in 113D. Regret bounds and information-theoretic lower
  bounds for learning under partial feedback.
* **Francis Bach, *Learning Theory from First Principles*** (2024, [MIT
  Press](https://mitpress.mit.edu/9780262049443/learning-theory-from-first-principles/)).
  Optimisation, approximation, and statistical error treated together,
  including overparameterised models. A recent graduate text.
* **Martin J. Wainwright, *High-Dimensional Statistics***. Listed in
  full in 107A. The non-asymptotic theory used throughout this
  subdivision.
* **Trevor Hastie, Robert Tibshirani, and Martin Wainwright,
  *Statistical Learning with Sparsity***. Listed in full in 107A.

---

<a id="cks-108"></a>

## 108. Dependent Data and Stochastic Models

Time series and inference for stochastic processes, survival and counting
processes, sequential analysis and change detection, spatial and
Gaussian-process models, and extremes. The probability of the underlying
processes is in Sections 6 and 8; the books here develop their statistical
theory.

<a id="cks-108a"></a>

### 108A. Time Series and Inference for Stochastic Processes

Second-order structure, likelihood for Gaussian series, spectral analysis,
state-space and hidden Markov models, long-range dependence, nonlinear and
nonparametric time series, and parameter estimation for diffusions and
other continuous-time processes.

#### Foundational works

* **Peter J. Brockwell and Richard A. Davis, *Time Series: Theory and
  Methods*** (2nd ed., 1991,
  [Springer](https://doi.org/10.1007/978-1-4419-0320-4); first ed.
  1987). ARMA and ARIMA models, prediction, and the asymptotic theory of
  the estimators. The mathematical standard. Their *Introduction to Time
  Series and Forecasting* is the more applied companion.
* **George E. P. Box, Gwilym M. Jenkins, Gregory C. Reinsel, and Greta
  M. Ljung, *Time Series Analysis: Forecasting and Control*** (5th ed.,
  2015,
  [Wiley](https://www.wiley.com/en-us/Time+Series+Analysis%3A+Forecasting+and+Control%2C+5th+Edition-p-9781118675021);
  first ed., Box and Jenkins, 1970). Identification, estimation, and
  diagnostic checking of ARIMA models. The book that established the
  modelling cycle.
* **David R. Brillinger, *Time Series: Data Analysis and Theory***
  (expanded ed., 1981, Holden-Day; first ed. 1975;
  [SIAM](https://doi.org/10.1137/1.9780898719246) reprint 2001).
  Spectral analysis and the Fourier methods for stationary series. The
  classical monograph.
* **E. J. Hannan and Manfred Deistler, *The Statistical Theory of Linear
  Systems*** (1988, Wiley;
  [SIAM](https://doi.org/10.1137/1.9781611972191) Classics reprint,
  2012). Linear systems, identification, and the statistical theory of
  multivariate time series. The research monograph on that side of the
  subject.
* **M. B. Priestley, *Spectral Analysis and Time Series*** (2 volumes,
  1981, [Academic
  Press](https://shop.elsevier.com/books/spectral-analysis-and-time-series-two-volume-set/priestley/978-0-08-057055-6)).
  A large reference for spectral methods, including nonstationary
  extensions. Consulted for a specific development rather than read as a
  course.
* **Masanobu Taniguchi and Yoshihide Kakizawa, *Asymptotic Theory of
  Statistical Inference for Time Series*** (2000,
  [Springer](https://doi.org/10.1007/978-1-4612-1162-4)). Local
  asymptotic normality, efficiency, and higher-order asymptotics for
  stationary processes. Brings the theory of Section 103 to time series.
* **James Durbin and Siem Jan Koopman, *Time Series Analysis by State
  Space Methods*** (2nd ed., 2012, [Oxford University
  Press](https://doi.org/10.1093/acprof:oso/9780199641178.001.0001);
  first ed. 2001). Kalman filtering and smoothing, likelihood
  evaluation, simulation, and non-Gaussian state-space models.
  The standard statistical reference for the state-space approach.
* **Olivier Cappé, Eric Moulines, and Tobias Rydén, *Inference in Hidden
  Markov Models*** (2005, [Springer](https://doi.org/10.1007/0-387-28982-8)).
  Filtering, smoothing, sequential Monte Carlo, and the consistency and
  asymptotic normality of maximum likelihood for general hidden Markov
  models. The research reference.
* **Jianqing Fan and Qiwei Yao, *Nonlinear Time Series: Nonparametric
  and Parametric Methods*** (2003,
  [Springer](https://doi.org/10.1007/978-0-387-69395-8)). Nonparametric
  regression methods for time series, and the nonlinear parametric
  models that sit beside them.
* **Peter Hall and C. C. Heyde, *Martingale Limit Theory and Its
  Application*** (1980, [Academic
  Press](https://doi.org/10.1016/C2013-0-10818-5)). Martingale central
  limit theorems, the strong law, and invariance principles, written for
  statistical application. Also listed in Section 103.
* **Ishwar V. Basawa and B. L. S. Prakasa Rao, *Statistical Inference
  for Stochastic Processes*** (1980, [Academic
  Press](https://doi.org/10.1016/C2009-0-22045-9)). Likelihood,
  estimation, and testing for Markov chains, branching processes, point
  processes, and diffusions. The early systematic monograph.
* **Robert S. Liptser and Albert N. Shiryaev, *Statistics of Random
  Processes I–II*** (2nd ed., 2001, Springer:
  [I](https://doi.org/10.1007/978-3-662-13043-8),
  [II](https://doi.org/10.1007/978-3-662-10028-8); first English ed.
  1977–1978). Absolute continuity of measures of diffusion-type
  processes, nonlinear filtering, and parameter estimation, by
  stochastic calculus. The classical treatise.
* **Yury A. Kutoyants, *Statistical Inference for Ergodic Diffusion
  Processes*** (2004,
  [Springer](https://doi.org/10.1007/978-1-4471-3866-2)). Parametric and
  nonparametric estimation for continuously observed ergodic diffusions,
  with asymptotic efficiency in the sense of Hájek and Le Cam.
* **Dimitris N. Politis, Joseph P. Romano, and Michael Wolf,
  *Subsampling***. Listed in full in Section 103. Resampling theory
  for stationary and nonstationary series and random fields.
* **S. N. Lahiri, *Resampling Methods for Dependent Data***. Listed in
  full in Section 103. Block bootstrap for time series and spatial data.

#### More recent works

* **Liudas Giraitis, Hira L. Koul, and Donatas Surgailis, *Large Sample
  Inference for Long Memory Processes*** (2012, [Imperial College
  Press](https://doi.org/10.1142/p591)). Limit theorems for sums and
  quadratic forms under long-range dependence, and their use in
  estimation and testing.
* **Randal Douc, Eric Moulines, and David S. Stoffer, *Nonlinear Time
  Series: Theory, Methods, and Applications with R Examples*** (2014,
  [Chapman and Hall/CRC](https://doi.org/10.1201/b16331)). Markovian
  nonlinear series, stability, and likelihood inference. A modern
  theoretical text.
* **Gennady Samorodnitsky, *Stochastic Processes and Long Range
  Dependence***. Listed in full in Section 6. The probabilistic
  background to long memory and heavy tails.
* **Nicolas Chopin and Omiros Papaspiliopoulos, *An Introduction to
  Sequential Monte Carlo***. Listed in full in Section 105. Particle
  filtering and smoothing for nonlinear, non-Gaussian state-space
  models, with convergence theory.

<a id="cks-108b"></a>

### 108B. Survival Analysis and Counting Processes

Censoring, the Cox model, and the counting-process formulation of
survival data.

#### Foundational works

* **Per Kragh Andersen, Ørnulf Borgan, Richard D. Gill, and Niels
  Keiding, *Statistical Models Based on Counting Processes*** (1993,
  [Springer](https://doi.org/10.1007/978-1-4612-4348-9)). Martingale
  methods for survival, the multiplicative intensity model, and the
  asymptotic theory. The research treatise.
* **Thomas R. Fleming and David P. Harrington, *Counting Processes and
  Survival Analysis*** (1991,
  [Wiley](https://doi.org/10.1002/9781118150672)). The same theory in
  the form of a graduate course, shorter than
  Andersen–Borgan–Gill–Keiding.
* **John D. Kalbfleisch and Ross L. Prentice, *The Statistical Analysis
  of Failure Time Data*** (2nd ed., 2002,
  [Wiley](https://doi.org/10.1002/9781118032985); first ed. 1980).
  Likelihood for censored data, the Cox model, and competing risks. The
  classical reference; the second edition is the one consulted.
* **Odd O. Aalen, Ørnulf Borgan, and Håkon K. Gjessing, *Survival and
  Event History Analysis: A Process Point of View*** (2008,
  [Springer](https://doi.org/10.1007/978-0-387-68560-1)). Event
  histories through counting processes, with dynamic covariates and a
  more applied development than the 1993 treatise.

#### More recent works

* **John P. Klein, Hans C. van Houwelingen, Joseph G. Ibrahim, and
  Thomas H. Scheike (eds.), *Handbook of Survival Analysis*** (2014,
  [Chapman and Hall/CRC](https://doi.org/10.1201/b16248)). Survey
  chapters on regression, competing risks, multivariate events, and
  clinical trials. A reference for the state of the methods.

<a id="cks-108c"></a>

### 108C. Sequential Analysis, Change Detection, and Anytime-Valid Inference

Sequential tests, confidence intervals after optional stopping, renewal
theory for the boundary, the detection of a change in distribution, and
inference valid at arbitrary stopping times.

#### Foundational works

* **Abraham Wald, *Sequential Analysis*** (1947, Wiley;
  [Dover](https://store.doverpublications.com/products/9780486615790)
  reprint). The founding monograph: the sequential probability ratio
  test and its operating characteristics.
* **David Siegmund, *Sequential Analysis: Tests and Confidence
  Intervals*** (1985,
  [Springer](https://doi.org/10.1007/978-1-4757-1862-1)). Corrected
  significance levels and confidence intervals for sequential and
  repeated experiments. The modern classic.
* **Michael Woodroofe, *Nonlinear Renewal Theory in Sequential
  Analysis*** (1982, [SIAM](https://doi.org/10.1137/1.9781611970302)).
  The renewal theory behind the boundary corrections in Siegmund. A
  technical monograph.
* **Herman Chernoff, *Sequential Analysis and Optimal Design*** (1972,
  [SIAM](https://doi.org/10.1137/1.9781611970593)). The SIAM lectures
  connecting sequential tests with the design of the experiment that
  feeds them.
* **Malay Ghosh, Nitis Mukhopadhyay, and Pranab K. Sen, *Sequential
  Estimation*** (1997, [Wiley](https://doi.org/10.1002/9781118165928)).
  Sequential point estimation and confidence intervals, at monograph
  length.
* **Michèle Basseville and Igor V. Nikiforov, *Detection of Abrupt
  Changes: Theory and Application*** (1993, Prentice Hall). Change
  detection in signals and in statistical models. The classical
  reference.
* **Miklós Csörgő and Lajos Horváth, *Limit Theorems in Change-Point
  Analysis*** (1997,
  [Wiley](https://www.wiley.com/en-us/Limit+Theorems+in+Change-Point+Analysis-p-9780471955221)).
  Asymptotic distributions of CUSUM, likelihood-ratio, and related
  change-point statistics, by weighted approximation of partial-sum and
  empirical processes. The theoretical reference for retrospective
  change-point tests.
* **Goran Peskir and Albert N. Shiryaev, *Optimal Stopping and
  Free-Boundary Problems***. Listed in full in Section 8. Includes the
  sequential testing and quickest-detection problems solved through
  free-boundary methods.

#### More recent works

* **Alexander Tartakovsky, Igor Nikiforov, and Michèle Basseville,
  *Sequential Analysis: Hypothesis Testing and Changepoint Detection***
  (2014, [Chapman and Hall/CRC](https://doi.org/10.1201/b17279)).
  Sequential tests and quickest detection in one systematic monograph,
  continuing Basseville–Nikiforov.
* **Aaditya Ramdas and Ruodu Wang, *Hypothesis Testing with
  E-values*** (2025, [Foundations and Trends in
  Statistics](https://doi.org/10.1561/3600000002)). E-values, test
  martingales, and anytime-valid inference, with their use in multiple
  testing. A book-length synthesis of a rapidly growing literature.

<a id="cks-108d"></a>

### 108D. Spatial Data, Point Patterns, and Gaussian Processes

Kriging, Gaussian random fields, Markov random fields, spatial point
patterns, and spatio-temporal models.

#### Foundational works

* **Michael L. Stein, *Interpolation of Spatial Data: Some Theory for
  Kriging*** (1999,
  [Springer](https://doi.org/10.1007/978-1-4612-1494-6)). Equivalence
  and orthogonality of Gaussian measures, and what they imply for
  prediction. The mathematical monograph on kriging.
* **Noel Cressie, *Statistics for Spatial Data*** (revised ed., 1993,
  [Wiley](https://doi.org/10.1002/9781119115151); first ed. 1991).
  Geostatistics, lattice data, and spatial point patterns, in one large
  reference.
* **Jesper Møller and Rasmus Plenge Waagepetersen, *Statistical
  Inference and Simulation for Spatial Point Processes*** (2003,
  [Chapman and Hall/CRC](https://doi.org/10.1201/9780203496930)).
  Poisson, Cox, and Markov point processes, likelihood and
  simulation-based inference, and perfect simulation. The mathematical
  monograph on point-process inference.
* **Håvard Rue and Leonhard Held, *Gaussian Markov Random Fields: Theory
  and Applications*** (2005, [Chapman and
  Hall/CRC](https://doi.org/10.1201/9780203492024)). Sparse precision
  matrices, conditional specifications, and fast sampling. The reference
  behind much of modern spatial computation.
* **Carl Edward Rasmussen and Christopher K. I. Williams, *Gaussian
  Processes for Machine Learning*** (2006, [MIT
  Press](https://doi.org/10.7551/mitpress/3206.001.0001); [authors'
  site](https://gaussianprocess.org/gpml/)). Gaussian processes as
  priors for regression and classification, with the approximation
  methods used to compute them. The standard reference on that side of
  the subject.
* **D. J. Daley and D. Vere-Jones, *An Introduction to the Theory of
  Point Processes***. Listed in full in Section 6. The probabilistic
  foundation for point-pattern models.
* **Robert J. Adler and Jonathan E. Taylor, *Random Fields and
  Geometry***. Listed in full in Section 6. Excursion sets and the
  expected Euler characteristic, used for thresholds in random-field
  inference.

#### More recent works

* **Noel Cressie and Christopher K. Wikle, *Statistics for
  Spatio-Temporal Data*** (2011, Wiley). Hierarchical models for
  processes indexed by space and time. The reference that extends
  Cressie's spatial treatise.
* **Adrian Baddeley, Ege Rubak, and Rolf Turner, *Spatial Point
  Patterns: Methodology and Applications with R*** (2015, [Chapman and
  Hall/CRC](https://doi.org/10.1201/b19708); [authors' companion
  site](https://book.spatstat.org/)). Intensity estimation, spatial
  interaction, point-process likelihood, and model assessment, developed
  with the `spatstat` software. The methodological complement to
  Møller–Waagepetersen.

<a id="cks-108e"></a>

### 108E. Extreme-Value Statistics

Maxima, threshold exceedances, tail indices, and rare-event quantiles
require limit approximations different from central-limit theory.
Both independent and dependent observations are included here.

#### Foundational works

* **Stuart Coles, *An Introduction to Statistical Modeling of Extreme
  Values*** (2001, [Springer](https://doi.org/10.1007/978-1-4471-3675-0)).
  Block maxima, threshold models, return levels, and likelihood
  inference, including dependent and nonstationary sequences.
  A concise methodological entry point; the proofs and tail-estimation
  asymptotics are developed more fully in de Haan–Ferreira.
* **M. R. Leadbetter, Georg Lindgren, and Holger Rootzén, *Extremes and
  Related Properties of Random Sequences and Processes*** (1983,
  [Springer](https://doi.org/10.1007/978-1-4612-5449-2)). Extremal
  types, extremes of stationary sequences under mixing conditions, and
  the extremal index. The classical probabilistic foundation.
* **Sidney I. Resnick, *Extreme Values, Regular Variation, and Point
  Processes*** and ***Heavy-Tail Phenomena: Probabilistic and
  Statistical Modeling*** (1987 and 2007, Springer:
  [I](https://doi.org/10.1007/978-0-387-75953-1),
  [II](https://doi.org/10.1007/978-0-387-45024-7)). Regular variation
  and point processes as the language of extremes; the second book adds
  the statistical estimation of heavy tails.
* **Paul Embrechts, Claudia Klüppelberg, and Thomas Mikosch, *Modelling
  Extremal Events for Insurance and Finance*** (1997,
  [Springer](https://doi.org/10.1007/978-3-642-33483-2)). Fluctuations
  of sums and maxima, tail estimation, and extremes of time series, with
  risk applications. A widely used reference joining probability and
  statistics of extremes.
* **Laurens de Haan and Ana Ferreira, *Extreme Value Theory: An
  Introduction*** (2006, [Springer](https://doi.org/10.1007/0-387-34471-3)).
  Domains of attraction, regular variation, tail-index and extreme
  quantile estimation, and multivariate and dependent extremes.
  A graduate-to-research treatment joining the probability theory to
  the consistency and asymptotic distributions of estimators.
* **Jan Beirlant, Yuri Goegebeur, Johan Segers, and Jozef Teugels,
  *Statistics of Extremes: Theory and Applications*** (2004,
  [Wiley](https://doi.org/10.1002/0470012382)). Tail-index and quantile
  estimation, regression for extremes, and multivariate and time-series
  extremes. A statistical counterpart to de Haan–Ferreira.

---

<a id="cks-109"></a>

## 109. Causal Inference

Potential outcomes, graphical and structural models, and the semiparametric
estimators that target intervention effects. The missing-data and efficiency
theory that many of the estimators use is in Section 104; conditional
independence and graphical models are in Section 106.

### Foundational works

* **Paul R. Rosenbaum, *Observational Studies*** (2nd ed., 2002,
  [Springer](https://doi.org/10.1007/978-1-4757-3692-2); first ed. 1995).
  Randomisation inference, matching, and sensitivity analysis for
  unmeasured confounding. The statistical theory of observational
  studies in the Fisher–Rubin tradition.
* **Judea Pearl, *Causality: Models, Reasoning, and Inference*** (2nd
  ed., 2009, [Cambridge University
  Press](https://doi.org/10.1017/CBO9780511803161); first ed. 2000).
  Directed graphical models, structural causal models, interventions,
  and the do-calculus. A principal reference for the graphical approach.
* **Peter Spirtes, Clark Glymour, and Richard Scheines, *Causation,
  Prediction, and Search*** (2nd ed., 2000, [MIT
  Press](https://doi.org/10.7551/mitpress/1754.001.0001); first ed.
  1993). Conditional independence and the discovery of graphical
  structure from data. The research monograph of that programme.
* **Steffen L. Lauritzen, *Graphical Models***. Listed in full in
  Section 106. The mathematical background on conditional
  independence and Markov properties; causal interpretations require
  additional assumptions, developed in the books in this section.
* **Anastasios A. Tsiatis, *Semiparametric Theory and Missing Data***.
  Listed in full in Section 104. Coarsening and missingness in the form
  used by many causal estimators.
* **Mark J. van der Laan and James M. Robins, *Unified Methods for
  Censored Longitudinal Data and Causality***. Listed in full in Section
  104. Efficient estimation of treatment effects under time-dependent
  confounding.

### More recent works

* **Guido W. Imbens and Donald B. Rubin, *Causal Inference for
  Statistics, Social, and Biomedical Sciences: An Introduction*** (2015,
  [Cambridge University
  Press](https://doi.org/10.1017/CBO9781139025751)). Potential outcomes,
  assignment mechanisms, and matching, developed as a statistical
  theory. The standard monograph of that approach.
* **Peng Ding, *A First Course in Causal Inference*** (2024, [Chapman
  and Hall/CRC](https://doi.org/10.1201/9781003484080)). Randomised
  experiments, observational studies, instrumental variables, and
  sensitivity analysis, with the statistical theory of each estimator. A
  concise graduate text in the potential-outcomes framework.
* **Miguel A. Hernán and James M. Robins, *Causal Inference: What If***
  (authors' suggested citation 2020, [Chapman and
  Hall/CRC](https://www.routledge.com/Causal-Inference-What-If/Hernan-Robins/p/book/9781420076165);
  freely available as an evolving [online
  book](https://miguelhernan.org/whatifbook)). Identification
  assumptions, standardisation, inverse-probability weighting,
  g-methods, and time-varying confounding. A substantial account of
  observational and longitudinal causal inference. Use the authors' site
  for the current text; a print edition has been listed for several years
  and is not yet settled.
* **Jonas Peters, Dominik Janzing, and Bernhard Schölkopf, *Elements of
  Causal Inference: Foundations and Learning Algorithms*** (2017, [MIT
  Press](https://mitpress.mit.edu/9780262037310/elements-of-causal-inference/);
  [open access](https://library.oapen.org/handle/20.500.12657/26040)). A
  shorter modern account joining graphical models, structural equations,
  and learning algorithms.
* **Mark J. van der Laan and Sherri Rose, *Targeted Learning: Causal
  Inference for Observational and Experimental Data*** (2011,
  [Springer](https://doi.org/10.1007/978-1-4419-9782-1)). Targeted
  minimum loss-based estimation, including targeted maximum likelihood,
  built from semiparametric efficiency theory and flexible estimation of
  nuisance functions. A methodological synthesis; the theorem-proof
  development of the efficiency theory is in Section 104.

---

# Part XII. Data Science

Mathematical and algorithmic foundations for representing, comparing,
learning from, and generating data. Section 110 covers geometric and
topological methods, 111 optimal transport and kernel discrepancies
between distributions, 112 stochastic dynamics, particle methods, and
diffusion generative models, 113 machine-learning models, networks,
sequential decisions, and responsible data analysis, and 114
optimization and numerical computation. The emphasis is on
graduate texts and research references; selected foundational papers and
surveys fill gaps where a book alone would not give a direct entry point.

High-dimensional estimation and statistical learning theory are in
Section 107; general machine-learning texts, graphical-model
computation, and bandits have their primary home here, in Section 113.
Classical directional and special-manifold statistics are in Section
106, multivariate transport ranks in Section 104, and variational
inference as a Bayesian method in Section 105. The analytic theory of
optimal transport and Wasserstein gradient flows is in Section 39,
Markov processes and stochastic control in Section 8, convex analysis
in Section 12, and matrix analysis in Section 13.

---

<a id="cks-110"></a>

## 110. Geometric and Topological Data Analysis

Point clouds, shapes, and manifold-valued observations, read through
spectral geometry or through persistent homology. Subdivision 110A is
manifold learning, statistics on manifolds, and shape; 110B is
computational topology and topological data analysis. Classical
multivariate analysis, including Kendall shape spaces, is in Section 106,
and functional data in the linear sense are in Section 104. Metric
geometry is in Section 39. Sparse and high-dimensional models of a more
linear kind are in Section 107.

<a id="cks-110a"></a>

### 110A. Manifold Learning, Geometric Statistics, and Shape

Spectral embeddings, intrinsic and extrinsic means, and metrics on shape
spaces, together with spectral clustering on similarity graphs.
Optimization on these spaces is collected in 114A; low-rank and
union-of-subspaces models are also treated in 114B.

#### Foundational works

* **Trevor Hastie and Werner Stuetzle, “Principal Curves”** (1989,
  [Journal of the American Statistical Association 84,
  502–516](https://doi.org/10.1080/01621459.1989.10478797)).
  Self-consistent curves passing through the middle of a
  distribution, as a nonlinear generalization of the first principal
  component. The statistical starting point for fitting
  low-dimensional curved structure to data.
* **Fan R. K. Chung, *Spectral Graph Theory*** (1997, [American
  Mathematical Society](https://doi.org/10.1090/cbms/092), CBMS
  Regional Conference Series in Mathematics 92). The normalized graph
  Laplacian, its eigenvalues, Cheeger inequalities, random walks, and
  isoperimetry. The mathematical background for spectral clustering
  and Laplacian embeddings.
* **Joshua B. Tenenbaum, Vin de Silva, and John C. Langford, “A Global
  Geometric Framework for Nonlinear Dimensionality Reduction”** (2000,
  [Science 290,
  2319–2323](https://doi.org/10.1126/science.290.5500.2319)). Isomap:
  geodesic distances estimated on a neighbourhood graph, followed by
  classical multidimensional scaling. One of the two papers that
  opened modern manifold learning.
* **Sam T. Roweis and Lawrence K. Saul, “Nonlinear Dimensionality
  Reduction by Locally Linear Embedding”** (2000, [Science 290,
  2323–2326](https://doi.org/10.1126/science.290.5500.2323)). Local
  linear reconstruction weights preserved by a global low-dimensional
  embedding, computed as an eigenvalue problem. The companion paper to
  Isomap.
* **Mikhail Belkin and Partha Niyogi, “Laplacian Eigenmaps for
  Dimensionality Reduction and Data Representation”** (2003, [Neural
  Computation 15,
  1373–1396](https://doi.org/10.1162/089976603321780317)). Embedding
  by eigenvectors of a graph Laplacian, justified through the
  Laplace–Beltrami operator of the underlying manifold. The bridge
  between spectral graph theory and manifold geometry.
* **Steven Rosenberg, *The Laplacian on a Riemannian Manifold***.
  Listed in full in Section 53. The Laplace–Beltrami operator and heat
  kernel that graph Laplacians and diffusion maps approximate.
* **Alexander Grigor'yan, *Introduction to Analysis on Graphs***.
  Listed in full in Section 39. Graph Laplacians, random walks, and
  eigenvalue estimates, the discrete analysis behind spectral
  embeddings.
* **Ronald R. Coifman and Stéphane Lafon, “Diffusion Maps”** (2006,
  [Applied and Computational Harmonic Analysis 21, 5–30](https://doi.org/10.1016/j.acha.2006.04.006)).
  Markov operators on a point cloud, diffusion distances, and spectral
  coordinates that reveal geometry across scales. A foundational paper
  connecting manifold learning, kernels, and stochastic processes.
* **Ulrike von Luxburg, “A Tutorial on Spectral Clustering”** (2007,
  [Statistics and Computing 17, 395–416](https://doi.org/10.1007/s11222-007-9033-z)).
  Similarity graphs, graph Laplacians, spectral embeddings, and
  clustering, derived through graph cuts, random walks, and
  perturbation theory. A concise entry point to the graph-based
  methods behind several nonlinear embeddings.
* **John A. Lee and Michel Verleysen, *Nonlinear Dimensionality
  Reduction*** (2007,
  [Springer](https://doi.org/10.1007/978-0-387-39351-3)).
  Multidimensional scaling, Isomap, locally linear embedding, Laplacian
  eigenmaps, and the related spectral methods, developed from the
  geometric idea through the algorithm. The book from which that first
  generation of manifold-learning methods is read as a group.
* **Laurens van der Maaten and Geoffrey Hinton, “Visualizing Data using
  t-SNE”** (2008, [Journal of Machine Learning Research 9,
  2579–2605](https://www.jmlr.org/papers/v9/vandermaaten08a.html)).
  Neighbour probabilities matched between data space and a
  heavy-tailed low-dimensional map. The standard nonlinear
  visualization method for high-dimensional data; its geometry is
  less transparent than that of the spectral embeddings above.
* **Yasuko Chikuse, *Statistics on Special Manifolds***. Listed in
  full in Section 106. Distributions, estimation, and asymptotics on
  the Stiefel and Grassmann manifolds.
* **Kanti V. Mardia and Peter E. Jupp, *Directional Statistics***.
  Listed in full in Section 106. Distributions and inference for data
  that are directions or rotations.
* **Ian L. Dryden and Kanti V. Mardia, *Statistical Shape Analysis***.
  Listed in full in Section 106. Kendall's shape spaces, Procrustes
  analysis, and distributions of shape.
* **Laurent Younes, *Shapes and Diffeomorphisms***. Listed in full in
  Section 39. Shape spaces of curves and surfaces, and the
  diffeomorphic metrics used to compare them.

#### More recent works

* **Jianzhong Wang, *Geometric Structure of High-Dimensional Data and
  Dimensionality Reduction*** (2012,
  [Springer](https://doi.org/10.1007/978-3-642-27497-8)). Spectral
  embeddings, diffusion maps, and related nonlinear methods, treated as
  a methods survey with the geometry kept in view. A companion to
  Lee–Verleysen.
* **Christopher R. Genovese, Marco Perone-Pacifico, Isabella
  Verdinelli, and Larry Wasserman, “Minimax Manifold Estimation”**
  (2012, [Journal of Machine Learning Research 13,
  1263–1291](https://www.jmlr.org/papers/v13/genovese12a.html)).
  Minimax rates in Hausdorff distance for recovering a submanifold
  from noisy samples. A statistical account of how well the geometry
  behind manifold learning can be estimated.
* **Abhishek Bhattacharya and Rabi Bhattacharya, *Nonparametric
  Inference on Manifolds: With Applications to Shape Spaces*** (2012,
  [Cambridge University Press](https://doi.org/10.1017/CBO9781139094764),
  Institute of Mathematical Statistics Monographs). Extrinsic and
  intrinsic Fréchet means, nonparametric density estimation and
  classification, and nonparametric Bayes on manifolds, with landmark
  shape spaces as the main application. The research monograph.
* **Victor Patrangenaru and Leif Ellingson, *Nonparametric Statistics
  on Manifolds and Their Applications to Object Data Analysis***
  (2016, [Chapman and Hall/CRC](https://doi.org/10.1201/b18969)).
  Asymptotics and bootstrap methods for nonparametric inference on
  manifolds, then object data: contours, directions, and shapes. A
  broad methodological development beside Bhattacharya–Bhattacharya.
* **Charles Fefferman, Sanjoy Mitter, and Hariharan Narayanan, “Testing
  the Manifold Hypothesis”** (2016, [Journal of the American
  Mathematical Society 29,
  983–1049](https://doi.org/10.1090/jams/852)). Sample complexity of
  deciding whether data lie near a manifold of given dimension,
  volume, and reach, with an algorithm for fitting one. The
  manifold hypothesis made into a precise statistical problem.
* **Anuj Srivastava and Eric P. Klassen, *Functional and Shape Data
  Analysis*** (2016,
  [Springer](https://doi.org/10.1007/978-1-4939-4020-2)). Elastic
  metrics on functions and curves, registration by reparameterization,
  and statistical inference for the resulting shapes. Functional data
  in the sense of Section 104 are the linear theory; this book is the
  elastic and geometric one.
* **René Vidal, Yi Ma, and S. Shankar Sastry, *Generalized Principal
  Component Analysis*** (2016,
  [Springer](https://doi.org/10.1007/978-0-387-87811-9)). Subspaces and
  unions of subspaces, and the algebraic and statistical methods that
  fit them. Geometric models built from linear pieces, between classical
  principal components and the nonlinear embeddings above.
* **Xavier Pennec, Stefan Sommer, and Tom Fletcher (eds.), *Riemannian
  Geometric Statistics in Medical Image Analysis*** (2019, [Academic
  Press](https://doi.org/10.1016/C2017-0-01561-6)). Riemannian centers
  of mass, covariance, and principal components on manifolds, with shape
  spaces and diffeomorphic deformations. A reference for geometric
  statistics beyond the medical-image applications of the title.
* **Leland McInnes, John Healy, and James Melville, “UMAP: Uniform
  Manifold Approximation and Projection for Dimension Reduction”**
  (2018, [author manuscript](https://arxiv.org/abs/1802.03426)).
  A fuzzy simplicial-set model of the neighbourhood graph, optimized
  to a low-dimensional layout. Together with t-SNE, the visualization
  method most used in practice; read beside the spectral theory
  above.
* **J. S. Marron and Ian L. Dryden, *Object Oriented Data Analysis***
  (2021, [Chapman and Hall/CRC](https://doi.org/10.1201/9781351189675)).
  A framework for choosing representations of curves, images, shapes,
  and other data objects. The geometry is kept visible and the
  formulas light; the theorem-proof development is in the monographs
  above.
* **Jean-Daniel Boissonnat, Frédéric Chazal, and Mariette Yvinec,
  *Geometric and Topological Inference***. Listed in full in 110B.
  Reconstruction of a submanifold from a finite, possibly noisy,
  sample.

<a id="cks-110b"></a>

### 110B. Persistent Homology and Computational Topology

Simplicial complexes built from data, the homology that persists across
scales, and the inference of geometry from a point sample. Prerequisites
vary: the introductory texts develop the needed homology, while the
research monographs require greater algebraic maturity.

#### Foundational works

* **Herbert Edelsbrunner, David Letscher, and Afra Zomorodian,
  “Topological Persistence and Simplification”** (2002, [Discrete &
  Computational Geometry 28,
  511–533](https://doi.org/10.1007/s00454-002-2885-2)). Persistence
  pairs of a filtered simplicial complex and the algorithm that
  computes them. The paper that introduced persistent homology in its
  computational form.
* **Afra Zomorodian and Gunnar Carlsson, “Computing Persistent
  Homology”** (2005, [Discrete & Computational Geometry 33,
  249–274](https://doi.org/10.1007/s00454-004-1146-y)). Persistence
  modules as graded modules over a polynomial ring, with barcodes as
  their classification and an algorithm over any field. The algebraic
  formulation on which the later theory rests.
* **Afra J. Zomorodian, *Topology for Computing*** (2005, [Cambridge
  University Press](https://doi.org/10.1017/CBO9780511546945)).
  Persistence as a computational theory: filtered complexes, the
  persistence algorithm, and the algebraic structure of the output. The
  early systematic account.
* **David Cohen-Steiner, Herbert Edelsbrunner, and John Harer,
  “Stability of Persistence Diagrams”** (2007, [Discrete &
  Computational Geometry 37,
  103–120](https://doi.org/10.1007/s00454-006-1276-5)). Persistence
  diagrams of tame functions move by at most the sup-norm
  perturbation in bottleneck distance. The stability theorem that
  makes persistence usable on noisy data.
* **Gurjeet Singh, Facundo Mémoli, and Gunnar Carlsson, “Topological
  Methods for the Analysis of High Dimensional Data Sets and 3D Object
  Recognition”** (2007, [Eurographics Symposium on Point-Based Graphics,
  91–100](https://doi.org/10.2312/SPBG/SPBG07/091-100)). The Mapper
  construction: the nerve of a cover pulled back through a filter
  function. The original description of the most widely used exploratory
  tool of applied topology.
* **Robert Ghrist, “Barcodes: The Persistent Topology of Data”** (2008,
  [Bulletin of the American Mathematical Society 45,
  61–75](https://doi.org/10.1090/S0273-0979-07-01191-3)). A short
  expository account of filtrations, barcodes, and their use on point
  clouds. A first reading before the monographs.
* **Partha Niyogi, Stephen Smale, and Shmuel Weinberger, “Finding the
  Homology of Submanifolds with High Confidence from Random
  Samples”** (2008, [Discrete & Computational Geometry 39,
  419–441](https://doi.org/10.1007/s00454-008-9053-2)). Sample sizes,
  in terms of the condition number of the manifold, at which a union
  of balls recovers its homology with high probability. The
  probabilistic link between manifold learning in 110A and
  topological inference.
* **Gunnar Carlsson, “Topology and Data”** (2009, [Bulletin of the
  American Mathematical Society 46,
  255–308](https://doi.org/10.1090/S0273-0979-09-01249-X)). Persistent
  homology, Mapper, and qualitative analysis of point clouds, with
  the motivation from data. The programmatic survey that defined the
  field.
* **Herbert Edelsbrunner and John L. Harer, *Computational Topology:
  An Introduction*** (2010, [American Mathematical
  Society](https://doi.org/10.1090/mbk/069)). Computational geometry,
  simplicial complexes, homology, and persistent homology, built up as
  a graduate course. The standard introduction.
* **Robert Ghrist, *Elementary Applied Topology*** (ed. 1.0, 2014,
  Createspace; [author's
  site](https://www2.math.upenn.edu/~ghrist/notes.html)). A broad tour
  of applied topology: persistence, sensors, networks, and sheaves,
  written so that the range of the subject is visible. The algebraic
  development is in Oudot and in Chazal–de Silva–Glisse–Oudot, below.
* **Steve Y. Oudot, *Persistence Theory: From Quiver Representations
  to Data Analysis*** (2015, [American Mathematical
  Society](https://doi.org/10.1090/surv/209), Mathematical Surveys and
  Monographs 209). Interval decompositions, barcodes, and the
  stability of persistence diagrams, then topological inference from
  geometric constructions. The research monograph.
* **Frédéric Chazal, Vin de Silva, Marc Glisse, and Steve Oudot, *The
  Structure and Stability of Persistence Modules*** (2016,
  [Springer](https://doi.org/10.1007/978-3-319-42545-0)). Persistence
  modules indexed by the real line, their structure, and the isometry
  theorem relating the interleaving distance to the bottleneck
  distance, under hypotheses met by the modules that arise from data.
  The algebraic core of the stability theory.

#### More recent works

* **Frédéric Chazal, David Cohen-Steiner, and Quentin Mérigot,
  “Geometric Inference for Probability Measures”** (2011, [Foundations
  of Computational Mathematics 11,
  733–751](https://doi.org/10.1007/s10208-011-9098-0)). The distance to
  a measure, a substitute for the distance function that is stable
  under Wasserstein perturbations and so robust to outliers. The
  construction behind robust topological inference.
* **Brittany Terese Fasy, Fabrizio Lecci, Alessandro Rinaldo, Larry
  Wasserman, Sivaraman Balakrishnan, and Aarti Singh, “Confidence Sets
  for Persistence Diagrams”** (2014, [Annals of Statistics 42,
  2301–2339](https://doi.org/10.1214/14-AOS1252)). Subsampling,
  bootstrap, and density-based methods that separate topological
  signal from noise in a persistence diagram. A foundational paper of
  statistical inference for topological summaries.
* **Peter Bubenik, “Statistical Topological Data Analysis using
  Persistence Landscapes”** (2015, [Journal of Machine Learning
  Research 16,
  77–102](https://www.jmlr.org/papers/v16/bubenik15a.html)).
  Persistence landscapes as random elements of a Banach space, with
  laws of large numbers and central limit theorems. A functional
  summary of persistence on which standard statistics can operate.
* **Larry Wasserman, “Topological Data Analysis”** (2018, [Annual
  Review of Statistics and Its Application 5,
  501–532](https://doi.org/10.1146/annurev-statistics-031017-100045)).
  Density clusters, manifold estimation, ridges, and persistent
  homology, surveyed from a statistician's point of view. A short
  statistical complement to the algebraic and computational accounts.
* **Jean-Daniel Boissonnat, Frédéric Chazal, and Mariette Yvinec,
  *Geometric and Topological Inference*** (2018, [Cambridge University
  Press](https://doi.org/10.1017/9781108297806), Cambridge Texts in
  Applied Mathematics). Inference of the geometry and topology of an
  unknown set from a finite noisy sample: simplicial complexes,
  distance functions, manifold reconstruction, persistent homology,
  and distances to measures. The mathematical link between this
  subdivision and 110A. Also listed in 110A.
* **Frédéric Chazal and Bertrand Michel, “An Introduction to Topological
  Data Analysis: Fundamental and Practical Aspects for Data Scientists”**
  (2021, [Frontiers in Artificial Intelligence 4, article
  667963](https://doi.org/10.3389/frai.2021.667963)). A survey of
  filtrations, persistence, stability, and statistical inference,
  including ways to use topological summaries in learning. A direct
  statistical introduction alongside the algebraic and computational
  monographs.
* **Gunnar Carlsson and Mikael Vejdemo-Johansson, *Topological Data
  Analysis with Applications*** (2021, [Cambridge University
  Press](https://doi.org/10.1017/9781108975704)). Persistent homology,
  cohomology, and the Mapper construction, with a closing set of case
  studies. A self-contained graduate route into the methods Carlsson's
  school developed.
* **Tamal Krishna Dey and Yusu Wang, *Computational Topology for Data
  Analysis*** (2022, [Cambridge University
  Press](https://doi.org/10.1017/9781009099950)). Algorithms for
  persistent homology and for zigzag persistence, multiparameter
  persistence, discrete Morse theory, Mapper, and Reeb graphs. The
  current computational reference.

---

<a id="cks-111"></a>

## 111. Optimal Transport and Kernel Discrepancies for Comparing Datasets

Distances and discrepancies between probability measures, and the
datasets that represent them. Subdivision 111A is optimal transport:
Wasserstein distances, transport maps, and their entropic
regularizations. Subdivision 111B is the kernel and integral
probability metrics — maximum mean discrepancy, energy distance, and
kernel mean embeddings — that compare distributions without solving a
transport problem. The analytic theory of transport — Kantorovich
duality, displacement interpolation, and Wasserstein geometry — is in
Section 39 and is cited here for the reader who needs it. Gradient
flows in the Wasserstein space, and the Schrödinger-bridge formulation
that ties entropic transport to diffusion, are taken up in 112A and
112C. The convex optimization and matrix algorithms behind transport
computation are collected in Section 114.

<a id="cks-111a"></a>

### 111A. Optimal Transport, Wasserstein Distances, and Their Statistics

Transport between measures as a metric on distributions, its
computation through entropic regularization, and the statistical
behaviour of empirical transport.

#### Foundational works

* **Cédric Villani, *Topics in Optimal Transportation***. Listed in full
  in Section 39. The short route to Kantorovich duality, displacement
  interpolation, and transport inequalities.
* **Cédric Villani, *Optimal Transport: Old and New***. Listed in full
  in Section 39. The comprehensive reference, connecting transport with
  partial differential equations, geometry, and probability.
* **Svetlozar T. Rachev and Ludger Rüschendorf, *Mass Transportation
  Problems***, Volume I, *Theory*, and Volume II, *Applications* (1998,
  Springer: [I](https://doi.org/10.1007/b98893),
  [II](https://doi.org/10.1007/b98894)). Probability metrics and the
  Monge–Kantorovich problem as they were used to compare distributions
  and to quantify the stability of stochastic models. The probabilistic
  treatise that preceded the geometric synthesis in Section 39.
* **Luigi Ambrosio, Nicola Gigli, and Giuseppe Savaré, *Gradient Flows
  in Metric Spaces and in the Space of Probability Measures***. Listed
  in full in Section 39. Gradient flows of entropy and interaction
  energies in the Wasserstein space. The analytic form of several
  algorithms in Section 112. Also listed in Section 112.
* **Facundo Mémoli, “Gromov–Wasserstein Distances and the Metric
  Approach to Object Matching”** (2011, [Foundations of Computational
  Mathematics 11,
  417–487](https://doi.org/10.1007/s10208-011-9093-5)). Metric
  measure spaces compared by transport of their distance matrices,
  with stability and lower bounds by computable invariants. The
  transport distance for datasets that live in different spaces.

#### More recent works

* **Filippo Santambrogio, *Optimal Transport for Applied
  Mathematicians***. Listed in full in Section 39. Duality, Wasserstein
  distances, and transport maps, developed toward variational problems
  a reader can compute with.
* **Alessio Figalli and Federico Glaudo, *An Invitation to Optimal
  Transport, Wasserstein Distances, and Gradient Flows***. Listed in
  full in Section 39. A short mathematical introduction, useful before
  Villani or Santambrogio.
* **Alfred Galichon, *Optimal Transport Methods in Economics*** (2016,
  [Princeton University
  Press](https://doi.org/10.23943/princeton/9780691172767.001.0001)).
  Matching, identification, and quantile methods formulated as optimal
  transport, with the linear-programming and computational side written
  for estimation. An economist's book; the statistical content is the
  comparison of distributions and the estimation theory that goes with
  it.
* **Marco Cuturi, “Sinkhorn Distances: Lightspeed Computation of Optimal
  Transport”** (2013, [Advances in Neural Information Processing
  Systems 26](https://proceedings.neurips.cc/paper_files/paper/2013/hash/af21d0c97db2e27e13572cbf59eb343d-Abstract.html)).
  Entropic regularization makes discrete transport accessible through
  matrix scaling. The foundational computational paper behind much
  of the data-science use of optimal transport; the broader theory
  and algorithms are developed by Peyré–Cuturi.
* **Nicolas Fournier and Arnaud Guillin, “On the Rate of Convergence in
  Wasserstein Distance of the Empirical Measure”** (2015, [Probability
  Theory and Related Fields 162,
  707–738](https://doi.org/10.1007/s00440-014-0583-7)). Moment and
  concentration bounds for the Wasserstein distance between a measure
  and its empirical version, with the dimension-dependent rates. The
  basic estimate behind statistical use of transport distances.
* **Victor Chernozhukov, Alfred Galichon, Marc Hallin, and Marc Henry,
  “Monge–Kantorovich Depth, Quantiles, Ranks and Signs”**. Listed in
  full in Section 104. Multivariate ranks and quantiles defined by
  transport to a reference measure.
* **Martin Arjovsky, Soumith Chintala, and Léon Bottou, “Wasserstein
  Generative Adversarial Networks”** (2017, [Proceedings of the 34th
  International Conference on Machine
  Learning](https://proceedings.mlr.press/v70/arjovsky17a.html); [author
  manuscript](https://arxiv.org/abs/1701.07875)). Training a generative
  model by the Kantorovich–Rubinstein dual of the Wasserstein-1
  distance. The paper that brought transport distances into generative
  modelling.
* **Sergey G. Bobkov and Michel Ledoux, *One-dimensional Empirical
  Measures, Order Statistics, and Kantorovich Transport Distances***.
  Listed in full in Section 7. Exact rates for empirical transport
  distances on the line, through order statistics and quantile
  functions.
* **Jonathan Weed and Francis Bach, “Sharp Asymptotic and Finite-Sample
  Rates of Convergence of Empirical Measures in Wasserstein
  Distance”** (2019, [Bernoulli 25,
  2620–2648](https://doi.org/10.3150/18-BEJ1065)). Rates governed by an
  intrinsic dimension of the measure rather than the ambient one.
  Explains why transport distances remain usable for data on
  low-dimensional structures.
* **Jean Feydy, Thibault Séjourné, François-Xavier Vialard, Shun-ichi
  Amari, Alain Trouvé, and Gabriel Peyré, “Interpolating between Optimal
  Transport and MMD using Sinkhorn Divergences”** (2019, [Proceedings of
  the 22nd International Conference on Artificial Intelligence and
  Statistics](https://proceedings.mlr.press/v89/feydy19a.html); [author
  manuscript](https://arxiv.org/abs/1810.08278)). Debiased entropic
  transport as a family of divergences between Wasserstein distance and
  maximum mean discrepancy. The bridge to 111B.
* **Victor M. Panaretos and Yoav Zemel, “Statistical Aspects of
  Wasserstein Distances”** (2019, [Annual Review of Statistics and
  Its Application 6,
  405–431](https://doi.org/10.1146/annurev-statistics-030718-104938)).
  Empirical transport, goodness-of-fit, barycenters, and
  registration, surveyed for statisticians. A short entry point
  before the monographs below.
* **Gabriel Peyré and Marco Cuturi, *Computational Optimal Transport:
  With Applications to Data Science*** (2019, [Now
  Publishers](https://doi.org/10.1561/9781680835519), Foundations and
  Trends in Machine Learning). Entropic regularization, Sinkhorn
  scaling, barycenters, and Gromov–Wasserstein discrepancies, as
  computational tools for comparing measures and datasets, together
  with the link between entropic transport and the Schrödinger bridge.
  The standard computational reference. Also listed in Section 39.
* **Victor M. Panaretos and Yoav Zemel, *An Invitation to Statistics
  in Wasserstein Space*** (2020,
  [Springer](https://doi.org/10.1007/978-3-030-38438-8)). The Wasserstein
  space as a sample space: Fréchet means, barycenters, and inference
  linearized in a tangent space, with deformation models for
  distributions. A short research monograph, openly available. The
  analytic background it assumes is in Section 39.
* **Sinho Chewi, Jonathan Niles-Weed, and Philippe Rigollet,
  *Statistical Optimal Transport*** (2025,
  [Springer](https://doi.org/10.1007/978-3-031-85160-5), Lecture Notes
  in Mathematics 2364). The Saint-Flour XLIX lectures, delivered in
  2019 and expanded for publication: empirical measures and their
  Wasserstein convergence, estimation of transport maps, and entropic
  regularization. A graduate research course on the statistical
  questions that complement the computational reference above.

<a id="cks-111b"></a>

### 111B. Kernel Mean Embeddings and Integral Probability Metrics

Distances between distributions defined as suprema over a class of
test functions, especially the unit ball of a reproducing-kernel
Hilbert space, and the two-sample and independence tests built on them.
Kernel methods for regression and classification are in Section 107.

#### Foundational works

* **Alfred Müller, “Integral Probability Metrics and Their Generating
  Classes of Functions”** (1997, [Advances in Applied Probability 29,
  429–443](https://doi.org/10.2307/1428011)). Probability metrics
  defined by a class of test functions, with the Kantorovich,
  total-variation, and Kolmogorov distances as cases. The unifying
  framework for the discrepancies of this subdivision.
* **Alain Berlinet and Christine Thomas-Agnan, *Reproducing Kernel
  Hilbert Spaces in Probability and Statistics***. Listed in full in
  Section 104. Reproducing kernels, embeddings of measures, and their
  statistical uses.
* **Arthur Gretton, Karsten M. Borgwardt, Malte J. Rasch, Bernhard
  Schölkopf, and Alexander Smola, “A Kernel Two-Sample Test”** (2012,
  [Journal of Machine Learning Research 13,
  723–773](https://www.jmlr.org/papers/v13/gretton12a.html)). Maximum
  mean discrepancy, its unbiased estimators, and their null
  distributions. The standard reference for kernel comparison of two
  samples.
* **Bharath K. Sriperumbudur, Kenji Fukumizu, Arthur Gretton, Bernhard
  Schölkopf, and Gert R. G. Lanckriet, “On the Empirical Estimation of
  Integral Probability Metrics”** (2012, [Electronic Journal of
  Statistics 6, 1550–1599](https://doi.org/10.1214/12-EJS722)).
  Estimators and convergence rates for Wasserstein, Dudley, and
  kernel distances, and the relation to classification risk. A
  comparison of the metrics of 111A and 111B on one footing.

#### More recent works

* **Gábor J. Székely and Maria L. Rizzo, “Energy Statistics: A Class of
  Statistics Based on Distances”** (2013, [Journal of Statistical
  Planning and Inference 143,
  1249–1272](https://doi.org/10.1016/j.jspi.2013.03.018)). Energy
  distance and distance covariance, with tests of equality of
  distributions and of independence. A survey of the distance-based
  strand by its originators.
* **Dino Sejdinovic, Bharath Sriperumbudur, Arthur Gretton, and Kenji
  Fukumizu, “Equivalence of Distance-Based and RKHS-Based Statistics
  in Hypothesis Testing”** (2013, [Annals of Statistics 41,
  2263–2291](https://doi.org/10.1214/13-AOS1140)). Energy distance and
  distance covariance identified with maximum mean discrepancy and
  the Hilbert–Schmidt independence criterion for suitable kernels.
  Joins the distance-based and kernel literatures.
* **Krikamol Muandet, Kenji Fukumizu, Bharath Sriperumbudur, and
  Bernhard Schölkopf, “Kernel Mean Embedding of Distributions: A
  Review and Beyond”** (2017, [Foundations and Trends in Machine
  Learning 10, 1–141](https://doi.org/10.1561/2200000060)).
  Characteristic kernels, embeddings of marginal and conditional
  distributions, estimation, and applications to testing and
  learning. The comprehensive survey.

---

<a id="cks-112"></a>

## 112. Mean-Field Limits and Stochastic Dynamics for Data

Langevin diffusions, Wasserstein gradient flows, stochastic
approximation, and interacting particle systems, used as algorithms for
sampling, filtering, training, and generation. Subdivision 112A is the
diffusion and gradient-flow theory; 112B is the particle, filtering, and
mean-field training theory; 112C is score matching, diffusion generation,
and Schrödinger bridges. Markov chain Monte Carlo as a statistical
method is in Section 105, inference for stochastic processes is in
Section 108, and mean-field games as a control theory are in Section 8.
The mean-field limit in this section is a law of large numbers for
particles, or for parameters, in simulation and in learning.

General neural-network architectures and deep-learning theory are
collected in 113B. Optimization algorithms and their complexity bounds
are in 114A; the emphasis here is on their continuous-time and
measure-valued descriptions.

<a id="cks-112a"></a>

### 112A. Langevin Dynamics, Sampling, and Gradient Flows

The diffusion that samples a target measure, the ordinary differential
equation that a stochastic approximation tracks, and the gradient-flow
structure that organizes both.

#### Foundational works

* **Herbert Robbins and Sutton Monro, “A Stochastic Approximation
  Method”** (1951, [Annals of Mathematical Statistics 22,
  400–407](https://doi.org/10.1214/aoms/1177729586)). Root finding
  from noisy evaluations with decreasing step sizes, and its
  convergence in probability. The origin of stochastic approximation
  and hence of stochastic gradient descent.
* **Boris T. Polyak and Anatoli B. Juditsky, “Acceleration of
  Stochastic Approximation by Averaging”** (1992, [SIAM Journal on
  Control and Optimization 30,
  838–855](https://doi.org/10.1137/0330046)). Averaging the iterates of
  a slowly decaying step-size scheme attains the optimal asymptotic
  covariance. The basic efficiency result for stochastic gradient
  methods.
* **Gareth O. Roberts and Richard L. Tweedie, “Exponential Convergence
  of Langevin Distributions and Their Discrete Approximations”**
  (1996, [Bernoulli 2, 341–363](https://doi.org/10.2307/3318418)).
  Ergodicity of the Langevin diffusion, the possible failure of its
  Euler discretization, and the Metropolis-adjusted correction. The
  classical analysis of Langevin-based sampling.
* **Richard Jordan, David Kinderlehrer, and Felix Otto, “The
  Variational Formulation of the Fokker–Planck Equation”** (1998,
  [SIAM Journal on Mathematical Analysis 29,
  1–17](https://doi.org/10.1137/S0036141096303359)). The Fokker–Planck
  equation as the gradient flow of free energy in the Wasserstein
  metric, obtained as the limit of a minimizing-movement scheme. The
  paper that links Langevin sampling to the transport geometry of
  Section 111.
* **Harold J. Kushner and G. George Yin, *Stochastic Approximation and
  Recursive Algorithms and Applications*** (2nd ed., 2003,
  [Springer](https://doi.org/10.1007/b97441); first ed., 1997, as
  *Stochastic Approximation Algorithms and Applications*). Almost-sure
  convergence and asymptotic distributions for stochastic approximation.
  The classical monograph on the recursive scheme behind stochastic
  gradient methods.
* **Vivek S. Borkar, *Stochastic Approximation: A Dynamical Systems
  Viewpoint*** (2nd ed., 2023,
  [Springer](https://doi.org/10.1007/978-981-99-8277-6), Texts and
  Readings in Mathematics; first ed., 2008, Hindustan Book Agency).
  The ordinary-differential-equation method: interpolated iterates
  track a limiting dynamical system. The second edition adds
  concentration, avoidance of traps, and multiple timescales. The
  dynamical reading of stochastic gradient descent.
* **Grigorios A. Pavliotis, *Stochastic Processes and Applications:
  Diffusion Processes, the Fokker–Planck and Langevin Equations***.
  Listed in full in Section 8. Langevin diffusions studied together
  with their forward equations and invariant measures.
* **Luigi Ambrosio, Nicola Gigli, and Giuseppe Savaré, *Gradient Flows
  in Metric Spaces and in the Space of Probability Measures***. Listed
  in full in Section 39. The law of an overdamped Langevin diffusion
  evolves as a Wasserstein gradient flow of free energy, under the
  appropriate hypotheses. The same structure organizes mean-field
  algorithms in 112B. Also listed in Section 111.

#### More recent works

* **Dominique Bakry, Ivan Gentil, and Michel Ledoux, *Analysis and
  Geometry of Markov Diffusion Operators***. Listed in full in Section
  14. Curvature-dimension conditions and the Γ-calculus, which give
  convergence rates for diffusion semigroups, including the Langevin
  diffusion.
* **Weinan E, Tiejun Li, and Eric Vanden-Eijnden, *Applied Stochastic
  Analysis***. Listed in full in Section 8. Stochastic differential
  equations, Fokker–Planck equations, averaging, and rare events,
  written with algorithms in view.
* **Max Welling and Yee Whye Teh, “Bayesian Learning via Stochastic
  Gradient Langevin Dynamics”** (2011, [Proceedings of the 28th
  International Conference on Machine
  Learning](https://icml.cc/2011/papers/398_icmlpaper.pdf), 681–688).
  Langevin updates with minibatch gradients and decreasing steps, moving
  from optimization to posterior sampling. The algorithm that joined
  stochastic approximation and Langevin Monte Carlo at data scale.
* **Arnak S. Dalalyan, “Theoretical Guarantees for Approximate Sampling
  from Smooth and Log-Concave Densities”** (2017, [Journal of the
  Royal Statistical Society Series B 79,
  651–676](https://doi.org/10.1111/rssb.12183)). Non-asymptotic
  total-variation bounds for the unadjusted Langevin algorithm under
  strong log-concavity. With Durmus–Moulines, the start of the
  non-asymptotic complexity theory of sampling.
* **Alain Durmus and Éric Moulines, “Nonasymptotic Convergence Analysis
  for the Unadjusted Langevin Algorithm”** (2017, [Annals of Applied
  Probability 27, 1551–1587](https://doi.org/10.1214/16-AAP1238)).
  Explicit bounds, with their dependence on dimension, for the
  discretized Langevin diffusion without Metropolis correction. The
  companion analysis to Dalalyan.
* **Sinho Chewi, *Log-Concave Sampling*** (unpublished [draft dated
  20 August 2026](https://chewisinho.github.io/main.pdf)). The
  complexity of sampling log-concave measures by the Langevin diffusion
  and its discretizations, using the Wasserstein geometry of Section
  39. Cite the dated draft rather than treating it as a published book.

<a id="cks-112b"></a>

### 112B. Particle Methods, Data Assimilation, and Training Dynamics

Mean-field particle models for integration and filtering, ensemble
methods that couple a dynamical model to observations, and the
infinite-width and feature-learning descriptions of how a network is
trained.

#### Foundational works

* **Alain-Sol Sznitman, “Topics in Propagation of Chaos”** (1991, in
  *École d'Été de Probabilités de Saint-Flour XIX—1989*,
  [Springer](https://doi.org/10.1007/BFb0085169), Lecture Notes in
  Mathematics 1464, pp. 165–251). Nonlinear processes, empirical
  measures, and asymptotic independence for weakly interacting
  particles. The probabilistic foundation for interpreting a
  mean-field equation as a limit of a finite particle system.
* **Pierre Del Moral, *Feynman–Kac Formulae: Genealogical and
  Interacting Particle Systems with Applications***. Listed in full in
  Section 105. Measure-valued equations and the genealogical particle
  systems that approximate them. The probabilistic foundation for the
  particle methods below.
* **Pierre Del Moral, *Mean Field Simulation for Monte Carlo
  Integration*** (2013, [Chapman and
  Hall/CRC](https://doi.org/10.1201/b14924), Monographs on Statistics
  and Applied Probability 126). Nonlinear Markov models and their
  mean-field particle approximations, for integration, filtering, rare
  events, and calibration. The research monograph that organizes
  ensemble and interacting-particle Monte Carlo.
* **Geir Evensen, *Data Assimilation: The Ensemble Kalman Filter***
  (2nd ed., 2009, [Springer](https://doi.org/10.1007/978-3-642-03711-5);
  first ed. 2007). The ensemble Kalman filter and smoother, their
  derivation, and their use with large geophysical models. The
  reference by the originator of the method.

* **René Carmona and François Delarue, *Probabilistic Theory of Mean
  Field Games with Applications***. Listed in full in Section 8.
  McKean–Vlasov dynamics and propagation of chaos, developed for games
  but used throughout mean-field analysis.

#### More recent works

* **Kody Law, Andrew M. Stuart, and Konstantinos Zygalakis, *Data
  Assimilation: A Mathematical Introduction*** (2015,
  [Springer](https://doi.org/10.1007/978-3-319-20325-6), Texts in
  Applied Mathematics). Bayesian formulation of filtering and smoothing
  for dynamical models, including variational methods and the ensemble
  Kalman filter. A mathematical introduction to the use of stochastic
  dynamics with data.
* **Sebastian Reich and Colin Cotter, *Probabilistic Forecasting and
  Bayesian Data Assimilation*** (2015, [Cambridge University
  Press](https://doi.org/10.1017/CBO9781107706804)). Probabilistic
  forecasting and Bayesian filtering, with transport maps and ensemble
  methods among the tools that couple a forecast distribution to
  observations. A bridge from this section to the transport methods of
  Section 111.
* **Qiang Liu and Dilin Wang, “Stein Variational Gradient Descent: A
  General Purpose Bayesian Inference Algorithm”** (2016, [Advances in
  Neural Information Processing Systems
  29](https://proceedings.neurips.cc/paper_files/paper/2016/hash/b3ba8f1bee1238a2f37603d90b58898d-Abstract.html);
  [author manuscript](https://arxiv.org/abs/1608.04471)). Deterministic
  interacting particles that follow a kernelized gradient flow of
  relative entropy. A particle method for sampling that sits between
  variational inference and Markov chain Monte Carlo.
* **Lénaïc Chizat and Francis Bach, “On the Global Convergence of
  Gradient Descent for Over-parameterized Models using Optimal
  Transport”** (2018, [Advances in Neural Information Processing Systems
  31](https://proceedings.neurips.cc/paper_files/paper/2018/hash/a1afc58c6ca9540d057299ec3016d726-Abstract.html);
  [author manuscript](https://arxiv.org/abs/1805.09545)). Training of
  wide two-layer networks as a Wasserstein gradient flow, with
  conditions for convergence to global minimizers. A companion to
  Mei–Montanari–Nguyen, below.
* **Song Mei, Andrea Montanari, and Phan-Minh Nguyen, “A Mean Field View
  of the Landscape of Two-Layer Neural Networks”** (2018,
  [Proceedings of the National Academy of Sciences 115,
  E7665–E7671](https://doi.org/10.1073/pnas.1806579115)).
  In a suitable scaling, stochastic gradient training of wide
  two-layer networks has a nonlinear PDE description for the
  distribution of parameters. A foundational paper on feature
  learning through mean-field dynamics; the graduate treatment is
  Spiliopoulos–Sowers–Sirignano in 113B.
* **Alfredo Garbuno-Inigo, Franca Hoffmann, Wuchen Li, and Andrew M.
  Stuart, “Interacting Langevin Diffusions: Gradient Structure and
  Ensemble Kalman Sampler”** (2020, [SIAM Journal on Applied Dynamical
  Systems 19, 412–441](https://doi.org/10.1137/19M1251655)). Ensemble
  methods derived as interacting Langevin systems with a
  preconditioned Wasserstein gradient structure. Connects the ensemble
  Kalman methods above with the sampling theory of 112A.
* **Justin Sirignano and Konstantinos Spiliopoulos, “Mean Field
  Analysis of Neural Networks: A Law of Large Numbers”** (2020, [SIAM
  Journal on Applied Mathematics 80,
  725–752](https://doi.org/10.1137/18M1192184)). Weak convergence of
  the empirical measure of network parameters under stochastic
  gradient descent to a deterministic measure-valued limit. A rigorous
  probabilistic form of the mean-field limit.
* **Grant M. Rotskoff and Eric Vanden-Eijnden, “Trainability and
  Accuracy of Artificial Neural Networks: An Interacting Particle
  System Approach”** (2022, [Communications on Pure and Applied
  Mathematics 75, 1889–1935](https://doi.org/10.1002/cpa.22074)).
  Network parameters as interacting particles, with a law of large
  numbers, a central limit theorem, and the resulting error scaling in
  the number of units. The mean-field analysis written in the
  language of statistical physics.
* **Louis-Pierre Chaintron and Antoine Diez, “Propagation of Chaos: A
  Review of Models, Methods and Applications”** (2022, Kinetic and
  Related Models 15, [895–1015](https://doi.org/10.3934/krm.2022017) and
  [1017–1173](https://doi.org/10.3934/krm.2022018)). Coupling,
  compactness, and entropy methods for mean-field limits, with
  applications that include particle algorithms and network training. A
  current survey that continues Sznitman.

<a id="cks-112c"></a>

### 112C. Score Matching, Diffusion Generative Models, and Schrödinger Bridges

Learning the gradient of a log-density, reversing a noising process to
generate data, and fitting path measures between prescribed marginals,
together with the flow-matching and interpolant methods that learn a
deterministic transport instead. A diffusion generative model and a
Schrödinger bridge solve related problems, but a general diffusion
model need not minimize the
path-space relative entropy defining the bridge.

#### Foundational works

* **Brian D. O. Anderson, “Reverse-Time Diffusion Equation Models”**
  (1982, [Stochastic Processes and Their Applications 12,
  313–326](https://doi.org/10.1016/0304-4149(82)90051-5)). The
  time reversal of a diffusion is again a diffusion, with drift
  corrected by the score of the marginal density. The result on which
  score-based generation by reverse-time SDEs rests.
* **Aapo Hyvärinen, “Estimation of Non-Normalized Statistical Models by
  Score Matching”** (2005, [Journal of Machine Learning Research 6,
  695–709](https://www.jmlr.org/papers/v6/hyvarinen05a.html)).
  Estimates a model through its gradient of log-density, avoiding
  evaluation of its normalization constant. The original statistical
  formulation of the score-matching objective used in later
  score-based generative methods.
* **Pascal Vincent, “A Connection Between Score Matching and Denoising
  Autoencoders”** (2011, [Neural Computation 23,
  1661–1674](https://doi.org/10.1162/NECO_a_00142)). Denoising score
  matching: the score of a noise-smoothed density is learned by
  regression on the added noise. The objective used to train modern
  diffusion models.
* **Christian Léonard, “A Survey of the Schrödinger Problem and Some of
  Its Connections with Optimal Transport”** (2014, [Discrete and
  Continuous Dynamical Systems 34,
  1533–1574](https://doi.org/10.3934/dcds.2014.34.1533)).
  Relative-entropy minimization on path space, endpoint constraints,
  and the relation to optimal transport through small-noise limits.
  The mathematical reference for the bridge problem underlying the
  algorithms below.

#### More recent works

* **Jascha Sohl-Dickstein, Eric Weiss, Niru Maheswaranathan, and Surya
  Ganguli, “Deep Unsupervised Learning using Nonequilibrium
  Thermodynamics”** (2015, [Proceedings of the 32nd International
  Conference on Machine
  Learning](https://proceedings.mlr.press/v37/sohl-dickstein15.html);
  [author manuscript](https://arxiv.org/abs/1503.03585)). A generative
  model obtained by learning to reverse a gradual noising Markov chain.
  The first diffusion probabilistic model.
* **Yang Song and Stefano Ermon, “Generative Modeling by Estimating
  Gradients of the Data Distribution”** (2019, [Advances in Neural
  Information Processing Systems
  32](https://proceedings.neurips.cc/paper_files/paper/2019/hash/3001ef257407d5a371a96dcd947c7d93-Abstract.html);
  [author manuscript](https://arxiv.org/abs/1907.05600)). Scores
  estimated at several noise levels and used in annealed Langevin
  sampling. The score-based counterpart to Ho–Jain–Abbeel.
* **Jonathan Ho, Ajay N. Jain, and Pieter Abbeel, “Denoising Diffusion
  Probabilistic Models”** (2020, [Advances in Neural Information
  Processing Systems 33](https://proceedings.neurips.cc/paper/2020/hash/4c5bcfec8584af0d967f1ab10179ca4b-Abstract.html)).
  Forward noising and learned reverse transitions, with a variational
  training objective related to denoising score matching. A
  foundational paper for modern discrete-time diffusion generation.
* **Yang Song, Jascha Sohl-Dickstein, Diederik P. Kingma, Abhishek
  Kumar, Stefano Ermon, and Ben Poole, “Score-Based Generative Modeling
  through Stochastic Differential Equations”** (2021,
  [ICLR](https://openreview.net/forum?id=PxTIG12RRHS); [author
  manuscript](https://arxiv.org/abs/2011.13456)). A continuous-time
  account of score-based generation: forward and reverse-time SDEs,
  score estimation, predictor-corrector sampling, and the
  probability-flow ODE. The direct link between learned generative
  models and the diffusion theory of 112A.
* **Valentin De Bortoli, James Thornton, Jeremy Heng, and Arnaud Doucet,
  “Diffusion Schrödinger Bridge with Applications to Score-Based
  Generative Modeling”** (2021, [Advances in Neural Information
  Processing Systems 34](https://proceedings.neurips.cc/paper_files/paper/2021/hash/940392f5f32a7ade1cc201767cf83e31-Abstract.html)).
  Iterative fitting of forward and backward diffusions to endpoint
  distributions, using score estimation. Connects the path-space
  problem in Léonard to computational generative modelling.
* **Sitan Chen, Sinho Chewi, Jerry Li, Yuanzhi Li, Adil Salim, and Anru
  R. Zhang, “Sampling is as Easy as Learning the Score: Theory for
  Diffusion Models with Minimal Data Assumptions”** (2023,
  [ICLR](https://openreview.net/forum?id=zyLVMgsZ0U_); [author
  manuscript](https://arxiv.org/abs/2209.11215)). Polynomial convergence
  guarantees for diffusion sampling given an L²-accurate score, without
  log-concavity. A central result of the theory of diffusion models.
* **Yaron Lipman, Ricky T. Q. Chen, Heli Ben-Hamu, Maximilian Nickel,
  and Matt Le, “Flow Matching for Generative Modeling”** (2023,
  [ICLR](https://openreview.net/forum?id=PqvMRDCJT9t); [author
  manuscript](https://arxiv.org/abs/2210.02747)). Regression onto the
  velocity field of a prescribed probability path, training a continuous
  normalizing flow without simulation. The deterministic counterpart of
  score-based diffusion.
* **Michael S. Albergo, Nicholas M. Boffi, and Eric Vanden-Eijnden,
  “Stochastic Interpolants: A Unifying Framework for Flows and
  Diffusions”** (2025, [Journal of Machine Learning Research 26, paper
  209](https://www.jmlr.org/papers/v26/23-1605.html); [author
  manuscript](https://arxiv.org/abs/2303.08797)). Interpolating
  processes between two arbitrary densities, from which both
  probability-flow ODEs and diffusions are learned by quadratic
  regression. A mathematical framework containing flow matching and
  score-based diffusion as cases.

---

<a id="cks-113"></a>

## 113. Machine-Learning Models, Representation, and Sequential Decisions

General accounts of data analysis and machine learning, neural
representations and generative models, learning on graphs, decisions
made while data are being collected, and the constraints of privacy,
fairness, and changing distributions. Subdivision 113A supplies broad
foundations, 113B deep learning, 113C networks and graph
representations, 113D bandits and reinforcement learning, and 113E
privacy, fairness, and distribution shift. Statistical learning theory
remains in Section 107; stochastic training limits and diffusion
generation are in Section 112, and optimization algorithms in Section
114.

<a id="cks-113a"></a>

### 113A. General Foundations, Probabilistic Modelling, and Ensembles

The data-analytic tradition from which data science grew, algorithmic
and probabilistic views of learning, clustering, latent variables and
variational inference, and the tree ensembles that dominate tabular
prediction.

#### Foundational works

* **John W. Tukey, “The Future of Data Analysis”** (1962, [Annals of
  Mathematical Statistics 33,
  1–67](https://doi.org/10.1214/aoms/1177704711)). Data analysis as a
  science distinct from mathematical statistics, with its own
  standards of evidence and its need for computation. The essay usually
  cited as the intellectual origin of data science.
* **John W. Tukey, *Exploratory Data Analysis*** (1977, Addison-Wesley;
  [Pearson](https://www.pearson.com/store/p/exploratory-data-analysis-classic-version-/P200000006400/9780134995458)
  reissue, 2019). Graphical and resistant summaries for looking at data
  before modelling it. The founding text of exploratory analysis.
* **David Pollard, “Strong Consistency of *k*-Means Clustering”**
  (1981, [Annals of Statistics 9,
  135–140](https://doi.org/10.1214/aos/1176345339)). Almost-sure
  convergence of optimal *k*-means centres to those of the population.
  The first asymptotic theory of a clustering criterion.
* **Leo Breiman, Jerome H. Friedman, Richard A. Olshen, and Charles J.
  Stone, *Classification and Regression Trees*** (1984, Wadsworth;
  [Chapman and Hall/CRC](https://doi.org/10.1201/9781315139470)
  reissue). Recursive partitioning, pruning by cost-complexity, and
  consistency of tree rules. The monograph behind the tree ensembles
  below.
* **Leo Breiman, “Random Forests”** (2001, [Machine Learning 45,
  5–32](https://doi.org/10.1023/A:1010933404324)). Bagged randomized
  trees, out-of-bag error, and variable importance. The original
  paper of one of the most used prediction methods.
* **Jerome H. Friedman, “Greedy Function Approximation: A Gradient
  Boosting Machine”** (2001, [Annals of Statistics 29,
  1189–1232](https://doi.org/10.1214/aos/1013203451)). Boosting as
  functional gradient descent on a loss, with regression trees as base
  learners. The source of gradient-boosted trees.
* **Trevor Hastie, Robert Tibshirani, and Jerome Friedman, *The Elements
  of Statistical Learning*** (2nd ed., 2009,
  [Springer](https://doi.org/10.1007/978-0-387-84858-7); first ed.
  2001). The shared map of modern statistical learning: regression,
  classification, kernels, boosting, and model assessment. A
  methodological synthesis with enough theory to be the book the field
  cites in common; the second edition is the one consulted.
* **Leo Breiman, “Statistical Modeling: The Two Cultures”** (2001,
  [Statistical Science 16,
  199–231](https://doi.org/10.1214/ss/1009213726), with discussion).
  Data-modelling and algorithmic-modelling cultures contrasted, and
  predictive accuracy argued as a criterion. The essay that framed
  the relation between statistics and machine learning.
* **David J. C. MacKay, *Information Theory, Inference, and Learning
  Algorithms*** (2003, [Cambridge University
  Press](https://www.cambridge.org/9780521642989); [author's
  site](https://www.inference.org.uk/itila/book.html)). Coding, Bayesian
  inference, Monte Carlo, and neural networks treated as one subject. A
  distinctive graduate text joining information theory to learning.
* **Christopher M. Bishop, *Pattern Recognition and Machine Learning***
  (2006, [Springer](https://link.springer.com/book/9780387310732)).
  Bayesian linear models, kernel methods, graphical models, mixtures and
  EM, variational inference, and sampling. The standard probabilistic
  text of its generation; Murphy, below, is its successor.
* **Daphne Koller and Nir Friedman, *Probabilistic Graphical Models:
  Principles and Techniques*** (2009, [MIT
  Press](https://mitpress.mit.edu/9780262013192/probabilistic-graphical-models/)).
  Representation, exact and approximate inference, and learning for
  Bayesian networks and Markov random fields. The comprehensive
  computational reference for graphical models; the statistical theory
  is in Sections 106 and 107.
* **Steffen L. Lauritzen, *Graphical Models***. Listed in full in
  Section 106. Conditional independence and Markov properties, the
  statistical foundation of the graphical models above.
* **Martin J. Wainwright and Michael I. Jordan, *Graphical Models,
  Exponential Families, and Variational Inference*** (2008,
  [Foundations and Trends in Machine
  Learning 1, 1–305](https://doi.org/10.1561/2200000001)). A
  book-length survey of graphical models, exponential families, and
  the variational methods used to compute with them: belief
  propagation, mean-field, and convex relaxations. The theoretical
  account of approximate inference beside Koller–Friedman.

#### More recent works

* **Christian Hennig, Marina Meilă, Fionn Murtagh, and Roberto Rocci
  (eds.), *Handbook of Cluster Analysis*** (2015, [Chapman and
  Hall/CRC](https://doi.org/10.1201/b19706)). Partitioning,
  hierarchical, model-based, density-based, and spectral clustering,
  with validation and the choice of number of clusters. The reference
  for clustering as a statistical problem.
* **Gérard Biau and Erwan Scornet, “A Random Forest Guided Tour”**
  (2016, [TEST 25, 197–227](https://doi.org/10.1007/s11749-016-0481-7),
  with discussion). Consistency results, variable importance, and the
  open theoretical questions for random forests. The survey of what
  is proved about Breiman's method.
* **David M. Blei, Alp Kucukelbir, and Jon D. McAuliffe, “Variational
  Inference: A Review for Statisticians”**. Listed in full in Section
  105. Mean-field and stochastic variational inference.
* **Bradley Efron and Trevor Hastie, *Computer Age Statistical
  Inference***. Listed in full in Section 101. Classical and
  computer-age methods, from the bootstrap to boosting and neural
  networks, told as one history.
* **David Donoho, “50 Years of Data Science”** (2017, [Journal of
  Computational and Graphical Statistics 26,
  745–766](https://doi.org/10.1080/10618600.2017.1384734)). A history
  of data science from Tukey onward and a proposal for its content as
  an academic field. A perspective on the scope of this part of the
  bibliography.
* **Avrim Blum, John Hopcroft, and Ravindran Kannan, *Foundations of Data
  Science*** (2020, [Cambridge University
  Press](https://doi.org/10.1017/9781108755528)). High-dimensional
  geometry, singular value decomposition, random walks, learning,
  streaming and sketching, clustering, random graphs, and latent
  models. A mathematical introduction to the algorithmic side of
  data science, useful as an entry point to this part.
* **Kevin P. Murphy, *Probabilistic Machine Learning: An Introduction***
  (2022, [MIT
  Press](https://mitpress.mit.edu/9780262046824/probabilistic-machine-learning/);
  [author's site](https://probml.github.io/book1)). Supervised and
  unsupervised learning, probabilistic modelling, decision theory, and
  neural networks in a common framework. A broad first course that
  connects statistical modelling to modern machine-learning practice.
* **Kevin P. Murphy, *Probabilistic Machine Learning: Advanced Topics***
  (2023, [MIT
  Press](https://mitpress.mit.edu/9780262048439/probabilistic-machine-learning/);
  [author's site](https://probml.github.io/pml-book/book2.html)).
  Graphical models, approximate inference, latent-variable and
  generative models, and sequential decision-making. The research
  reference following the introductory volume, with variational
  inference and modern generative methods treated together.
* **Jianqing Fan, Runze Li, Cun-Hui Zhang, and Hui Zou, *Statistical
  Foundations of Data Science***. Listed in full in Section 107. The
  high-dimensional statistical theory of the methods in this
  subdivision.
* **Moritz Hardt and Benjamin Recht, *Patterns, Predictions, and
  Actions: Foundations of Machine Learning*** (2022, [Princeton
  University
  Press](https://press.princeton.edu/books/hardcover/9780691233734/patterns-predictions-and-actions);
  [author's site](https://mlstory.org/)). Prediction, supervised
  learning, datasets and benchmarks, causality, and sequential
  decisions, written with attention to how data are collected and used.
  A graduate course that connects 113A to 113D and 113E.

* **Carl Edward Rasmussen and Christopher K. I. Williams, *Gaussian
  Processes for Machine Learning***. Listed in full in Section 108.
  Gaussian-process regression and classification.

<a id="cks-113b"></a>

### 113B. Deep Learning: Architectures, Approximation, and Training Theory

Neural architectures, representation and generative modelling,
expressivity, generalization, and the kernel and feature-learning
descriptions of training. The mean-field PDE viewpoint is developed
further in 112B, and diffusion models in 112C.

#### Foundational works

* **David E. Rumelhart, Geoffrey E. Hinton, and Ronald J. Williams,
  “Learning Representations by Back-Propagating Errors”** (1986,
  [Nature 323, 533–536](https://doi.org/10.1038/323533a0)). Gradient
  computation through a layered network by the chain rule, and the
  internal representations it learns. The paper that made multilayer
  networks trainable; the general algorithm is reverse-mode automatic
  differentiation, in 114A.
* **George Cybenko, “Approximation by Superpositions of a Sigmoidal
  Function”** (1989, [Mathematics of Control, Signals and Systems 2,
  303–314](https://doi.org/10.1007/BF02551274)). Density of
  one-hidden-layer networks in the continuous functions on a compact
  set. With Hornik–Stinchcombe–White, the universal approximation
  theorem.
* **Kurt Hornik, Maxwell Stinchcombe, and Halbert White, “Multilayer
  Feedforward Networks are Universal Approximators”** (1989, [Neural
  Networks 2, 359–366](https://doi.org/10.1016/0893-6080(89)90020-8)).
  Universal approximation for general squashing activations and in
  measurable-function metrics. The companion to Cybenko.
* **Andrew R. Barron, “Universal Approximation Bounds for
  Superpositions of a Sigmoidal Function”** (1993, [IEEE Transactions
  on Information Theory 39,
  930–945](https://doi.org/10.1109/18.256500)). Approximation rates
  independent of dimension for functions with a finite Fourier moment.
  The first quantitative account of why networks can escape the curse
  of dimensionality.
* **Martin Anthony and Peter L. Bartlett, *Neural Network Learning:
  Theoretical Foundations***. Listed in full in Section 107. VC and
  fat-shattering bounds for networks.
* **Diederik P. Kingma and Max Welling, “Auto-Encoding Variational
  Bayes”** (2014, ICLR; [author
  manuscript](https://arxiv.org/abs/1312.6114)). The variational
  autoencoder and the reparameterization gradient for latent-variable
  models. The basic method of amortized variational inference.
* **Ian Goodfellow, Jean Pouget-Abadie, Mehdi Mirza, Bing Xu, David
  Warde-Farley, Sherjil Ozair, Aaron Courville, and Yoshua Bengio,
  “Generative Adversarial Nets”** (2014, [Advances in Neural Information
  Processing Systems
  27](https://proceedings.neurips.cc/paper_files/paper/2014/hash/f033ed80deb0234979a61f95710dbe25-Abstract.html);
  [author manuscript](https://arxiv.org/abs/1406.2661)). A generator
  trained against a discriminator in a minimax game whose population
  solution is the data distribution. The original adversarial generative
  model; the transport form is in 111A.
* **Ian Goodfellow, Yoshua Bengio, and Aaron Courville, *Deep
  Learning*** (2016, [MIT
  Press](https://mitpress.mit.edu/9780262035613/deep-learning/);
  [author-hosted text](https://www.deeplearningbook.org/)). Feedforward,
  convolutional, and recurrent networks, regularization, optimization,
  representation learning, and generative models. The foundational
  general text; later architectures and diffusion models require the
  more recent references below and in 112C.

#### More recent works

* **Allan Pinkus, *Ridge Functions***. Listed in full in Section 47.
  Density and approximation by ridge functions, the mathematics of
  one-hidden-layer networks.
* **Ashish Vaswani, Noam Shazeer, Niki Parmar, Jakob Uszkoreit, Llion
  Jones, Aidan N. Gomez, Łukasz Kaiser, and Illia Polosukhin, “Attention
  Is All You Need”** (2017, [Advances in Neural Information Processing
  Systems
  30](https://proceedings.neurips.cc/paper_files/paper/2017/hash/3f5ee243547dee91fbd053c1c4a845aa-Abstract.html);
  [author manuscript](https://arxiv.org/abs/1706.03762)). The
  transformer: sequence modelling by multi-head self-attention without
  recurrence. The architecture of modern language and foundation models.
* **Arthur Jacot, Franck Gabriel, and Clément Hongler, “Neural Tangent
  Kernel: Convergence and Generalization in Neural Networks”** (2018,
  [Advances in Neural Information Processing Systems
  31](https://proceedings.neurips.cc/paper_files/paper/2018/hash/5a4be1fa34e62bb8a6ec6b91d2462f5a-Abstract.html);
  [author manuscript](https://arxiv.org/abs/1806.07572)). In the
  infinite-width limit with standard scaling, training follows kernel
  gradient dynamics with a fixed limiting neural tangent kernel. The
  connection to kernel regression is developed for least-squares loss
  under suitable convergence conditions. The lazy-training regime;
  the mean-field regime is treated in 112B.
* **Mikhail Belkin, Daniel Hsu, Siyuan Ma, and Soumik Mandal,
  “Reconciling Modern Machine-Learning Practice and the Classical
  Bias–Variance Trade-off”** (2019, [Proceedings of the National
  Academy of Sciences 116,
  15849–15854](https://doi.org/10.1073/pnas.1903070116)). The double
  descent of test risk beyond the interpolation threshold. The paper
  that set the agenda for the theory of overparameterized models.
* **Johannes Schmidt-Hieber, “Nonparametric Regression using Deep
  Neural Networks with ReLU Activation Function”** (2020, [Annals of
  Statistics 48, 1875–1897](https://doi.org/10.1214/19-AOS1875), with
  discussion). Minimax rates for sparse deep networks over
  compositional function classes. The statistical case for depth in
  nonparametric regression.
* **Peter L. Bartlett, Andrea Montanari, and Alexander Rakhlin, “Deep
  Learning: A Statistical Viewpoint”** (2021, [Acta Numerica 30,
  87–201](https://doi.org/10.1017/S0962492921000027)). Benign
  overfitting, implicit regularization, and the linear and mean-field
  regimes of training. A comprehensive survey of the statistical
  theory of overparameterized networks.
* **George Papamakarios, Eric Nalisnick, Danilo Jimenez Rezende, Shakir
  Mohamed, and Balaji Lakshminarayanan, “Normalizing Flows for
  Probabilistic Modeling and Inference”** (2021, [Journal of Machine
  Learning Research 22, paper
  57](https://www.jmlr.org/papers/v22/19-1028.html)). Invertible
  transformations with tractable Jacobians as density models and
  samplers. The standard survey of flow-based generative models.
* **Trevor Hastie, Andrea Montanari, Saharon Rosset, and Ryan J.
  Tibshirani, “Surprises in High-Dimensional Ridgeless Least Squares
  Interpolation”** (2022, [Annals of Statistics 50,
  949–986](https://doi.org/10.1214/21-AOS2133)). Exact asymptotic risk
  of minimum-norm interpolation in linear and random-features models,
  including double descent. The linear model in which the
  overparameterized phenomena are proved.
* **Simon J. D. Prince, *Understanding Deep Learning*** (2023, [MIT
  Press](https://mitpress.mit.edu/9780262048644/understanding-deep-learning/);
  [author's site](https://udlbook.github.io/udlbook/)). Architectures,
  training, generalization, and generative models including diffusion,
  with careful figures and derivations. A current introductory course,
  beside Bishop–Bishop below.
* **Daniel A. Roberts and Sho Yaida, with contributions by Boris Hanin,
  *The Principles of Deep Learning Theory: An Effective Theory Approach
  to Understanding Neural Networks*** (2022, [Cambridge University
  Press](https://doi.org/10.1017/9781009023405)). A perturbative
  description of wide networks about the infinite-width kernel limit,
  including finite-width corrections.
  The feature-learning regime is treated in
  Spiliopoulos–Sowers–Sirignano, below.
* **Philipp Grohs and Gitta Kutyniok (eds.), *Mathematical Aspects of
  Deep Learning*** (2023, [Cambridge University
  Press](https://doi.org/10.1017/9781009025096)). A coordinated set of
  surveys on the mathematical theory of deep learning, including
  expressivity, generalization, generative models, and a dynamical
  systems and optimal-control account of training by Weinan E, Jiequn
  Han, and Qianxiao Li. The statistical learning theory of the same
  models is in Section 107.
* **Christopher M. Bishop and Hugh Bishop, *Deep Learning: Foundations
  and Concepts*** (2024,
  [Springer](https://doi.org/10.1007/978-3-031-45468-4)). Neural
  networks, attention and transformers, graph networks, and
  generative models, developed from probabilistic and computational
  principles. A modern conceptual course; the other references in
  this subdivision provide more detailed mathematical theory.
* **Konstantinos Spiliopoulos, Richard B. Sowers, and Justin Sirignano,
  *Mathematical Foundations of Deep Learning Models and Algorithms***
  (2025, [American Mathematical
  Society](https://doi.org/10.1090/gsm/252), Graduate Studies in
  Mathematics 252). Models, approximation, and the convergence theory
  of gradient descent and stochastic gradient descent, including the
  neural tangent kernel regime and the feature-learning regime. A
  graduate text by authors of the mean-field analysis of network
  training.

<a id="cks-113c"></a>

### 113C. Networks and Graph Representation Learning

Network structure, community detection, graph embeddings, and
message-passing neural networks. Graphical models based on conditional
independence are in Sections 106 and 107; the graphs here are also
observations and objects to be represented. Spectral graph theory is
in 110A.

#### Foundational works

* **Paul W. Holland, Kathryn Blackmond Laskey, and Samuel Leinhardt,
  “Stochastic Blockmodels: First Steps”** (1983, [Social Networks 5,
  109–137](https://doi.org/10.1016/0378-8733(83)90021-7)). Random
  graphs whose edge probabilities depend only on latent block
  memberships. The model on which the statistical theory of community
  detection is built.
* **Eric D. Kolaczyk, *Statistical Analysis of Network Data: Methods
  and Models*** (2009,
  [Springer](https://doi.org/10.1007/978-0-387-88146-1)). Network
  sampling, descriptive statistics, random graph and exponential
  random graph models, and processes on networks. The statistician's
  introduction to network data.
* **Karl Rohe, Sourav Chatterjee, and Bin Yu, “Spectral Clustering and
  the High-Dimensional Stochastic Blockmodel”** (2011, [Annals of
  Statistics 39, 1878–1915](https://doi.org/10.1214/11-AOS887)).
  Consistency of spectral clustering for blockmodels with a growing
  number of communities. A basic statistical guarantee for the
  spectral methods of 110A applied to networks.
* **László Lovász, *Large Networks and Graph Limits*** (2012,
  [American Mathematical Society](https://doi.org/10.1090/coll/060),
  Colloquium Publications 60). Graphons, cut distance, and the limit
  theory of dense graph sequences. The mathematical foundation for
  nonparametric network models.

#### More recent works

* **Mark Newman, *Networks*** (2nd ed., 2018, [Oxford University
  Press](https://doi.org/10.1093/oso/9780198805090.001.0001);
  first ed. 2010, as *Networks: An Introduction*). Network
  measurements, random graph models, spectral methods, community
  detection, and dynamical processes on networks. A broad
  mathematical reference for network data.
* **Harry Crane, *Probabilistic Foundations of Statistical Network
  Analysis*** (2018, [Chapman and
  Hall/CRC](https://doi.org/10.1201/9781315209661), Monographs on
  Statistics and Applied Probability 157). Exchangeability, sampling,
  and projectivity as the basis for network models. A foundational
  examination of what a statistical network model should be.
* **Emmanuel Abbe, “Community Detection and Stochastic Block Models:
  Recent Developments”** (2018, [Journal of Machine Learning Research
  18, paper 177](https://www.jmlr.org/papers/v18/16-480.html)). Exact
  recovery, weak recovery, and the information-theoretic thresholds of
  the stochastic block model, with the algorithms that achieve them. The
  standard survey of the threshold theory.
* **Thomas N. Kipf and Max Welling, “Semi-Supervised Classification with
  Graph Convolutional Networks”** (2017,
  [ICLR](https://openreview.net/forum?id=SJU4ayYgl); [author
  manuscript](https://arxiv.org/abs/1609.02907)). A first-order spectral
  approximation that yields a simple graph convolution layer. The paper
  that made graph neural networks a standard tool.
* **Justin Gilmer, Samuel S. Schoenholz, Patrick F. Riley, Oriol
  Vinyals, and George E. Dahl, “Neural Message Passing for Quantum
  Chemistry”** (2017, [Proceedings of the 34th International Conference
  on Machine
  Learning](https://proceedings.mlr.press/v70/gilmer17a.html); [author
  manuscript](https://arxiv.org/abs/1704.01212)). The message-passing
  framework that unifies graph neural network architectures.
* **Keyulu Xu, Weihua Hu, Jure Leskovec, and Stefanie Jegelka, “How
  Powerful are Graph Neural Networks?”** (2019,
  [ICLR](https://openreview.net/forum?id=ryGs6iA5Km); [author
  manuscript](https://arxiv.org/abs/1810.00826)). The expressive power
  of message passing bounded by the Weisfeiler–Leman test, and an
  architecture that attains it. The basic expressivity result.
* **William L. Hamilton, *Graph Representation Learning*** (2020, Morgan
  & Claypool, now [Springer](https://doi.org/10.1007/978-3-031-01588-5),
  Synthesis Lectures on Artificial Intelligence and Machine Learning;
  [author's site](https://www.cs.mcgill.ca/~wlh/grl_book/)). Node
  embeddings, relational data, graph neural networks, and generative
  graph models. A concise graduate account of learning representations
  when the observed data have graph structure.
* **Michael M. Bronstein, Joan Bruna, Taco Cohen, and Petar
  Veličković, *Geometric Deep Learning: Grids, Groups, Graphs,
  Geodesics, and Gauges*** (2021, [author
  manuscript](https://arxiv.org/abs/2104.13478)). Architectures derived
  from symmetry and invariance: convolutional, graph, and equivariant
  networks in one framework. A unifying text linking 113B and this
  subdivision.

<a id="cks-113d"></a>

### 113D. Bandits and Reinforcement Learning

Exploration, feedback, regret, and learning to act in a dynamical
environment. Sequential testing is in 108C; here decisions influence
the observations or rewards available for subsequent learning.
Stochastic control and dynamic programming as mathematics are in
Section 8, and online prediction in 107B.

#### Foundational works

* **Tze Leung Lai and Herbert Robbins, “Asymptotically Efficient
  Adaptive Allocation Rules”** (1985, [Advances in Applied Mathematics
  6, 4–22](https://doi.org/10.1016/0196-8858(85)90002-8)). The
  logarithmic lower bound on regret for stochastic bandits, and
  allocation rules that attain it. The foundational paper of
  statistical bandit theory.
* **Christopher J. C. H. Watkins and Peter Dayan, “Q-Learning”**
  (1992, [Machine Learning 8,
  279–292](https://doi.org/10.1007/BF00992698)). Convergence of the
  tabular Q-learning iteration to the optimal action values. The
  basic stochastic-approximation result of reinforcement learning.
* **Martin L. Puterman, *Markov Decision Processes: Discrete Stochastic
  Dynamic Programming*** (1994,
  [Wiley](https://doi.org/10.1002/9780470316887)). Finite- and
  infinite-horizon criteria, value and policy iteration, linear
  programming, and average-reward theory. The standard reference for
  the models on which reinforcement learning operates.
* **Dimitri P. Bertsekas and John N. Tsitsiklis, *Neuro-Dynamic
  Programming*** (1996, [Athena
  Scientific](http://www.athenasc.com/ndpbook.html)). Approximate
  dynamic programming, temporal-difference methods, and their
  convergence through stochastic approximation. The first rigorous
  monograph on reinforcement learning with function approximation.
* **Peter Auer, Nicolò Cesa-Bianchi, and Paul Fischer, “Finite-Time
  Analysis of the Multiarmed Bandit Problem”** (2002, [Machine Learning
  47, 235–256](https://doi.org/10.1023/A:1013689704352)). Upper
  confidence bound policies with logarithmic regret uniformly in time.
  The source of the UCB algorithms.
* **Wendell H. Fleming and H. Mete Soner, *Controlled Markov Processes
  and Viscosity Solutions***. Listed in full in Section 8. Dynamic
  programming and stochastic optimal control in continuous time.
* **Nicolò Cesa-Bianchi and Gábor Lugosi, *Prediction, Learning, and
  Games***. Listed in full in Section 107. Prediction with expert
  advice and adversarial bandits.
* **Richard S. Sutton and Andrew G. Barto, *Reinforcement Learning:
  An Introduction*** (2nd ed., 2018, [MIT
  Press](https://mitpress.mit.edu/9780262039246/reinforcement-learning/);
  first ed. 1998). Markov decision processes, dynamic programming,
  Monte Carlo and temporal-difference learning, function
  approximation, and policy-gradient methods. The standard
  conceptual and algorithmic introduction.

#### More recent works

* **Csaba Szepesvári, *Algorithms for Reinforcement Learning*** (2010,
  [Morgan & Claypool](https://doi.org/10.2200/S00268ED1V01Y201005AIM009),
  Synthesis Lectures on Artificial Intelligence and Machine Learning).
  Temporal-difference learning, control, and the theory behind them in
  a short monograph. A concise mathematical companion to
  Sutton–Barto.
* **John Gittins, Kevin Glazebrook, and Richard Weber, *Multi-armed
  Bandit Allocation Indices*** (2nd ed., 2011,
  [Wiley](https://doi.org/10.1002/9780470980033); first ed., Gittins
  alone, 1989). The Gittins index and its optimality for discounted
  Bayesian bandits. The Bayesian decision-theoretic strand of the
  subject.
* **Sébastien Bubeck and Nicolò Cesa-Bianchi, “Regret Analysis of
  Stochastic and Nonstochastic Multi-armed Bandit Problems”** (2012,
  [Foundations and Trends in Machine Learning 5,
  1–122](https://doi.org/10.1561/2200000024)). Stochastic,
  adversarial, and linear bandits with upper and lower bounds. A
  survey preceding Lattimore–Szepesvári.
* **Daniel J. Russo, Benjamin Van Roy, Abbas Kazerouni, Ian Osband, and
  Zheng Wen, “A Tutorial on Thompson Sampling”** (2018, [Foundations
  and Trends in Machine Learning 11,
  1–96](https://doi.org/10.1561/2200000070)). Posterior sampling for
  exploration, its approximations, and its regret. The reference for
  the Bayesian heuristic most used in practice.
* **Aleksandrs Slivkins, “Introduction to Multi-Armed Bandits”** (2019,
  [Foundations and Trends in Machine Learning 12,
  1–286](https://doi.org/10.1561/2200000068)). Stochastic, Bayesian,
  Lipschitz, adversarial, and contextual bandits, with bandits and
  games. An introductory monograph beside Lattimore–Szepesvári.
* **Tor Lattimore and Csaba Szepesvári, *Bandit Algorithms*** (2020,
  [Cambridge University Press](https://doi.org/10.1017/9781108571401)).
  Stochastic, adversarial, linear, and contextual bandits,
  exploration–exploitation tradeoffs, regret bounds, and lower
  bounds. The rigorous graduate and research reference for
  learning from partial feedback.
* **Sean Meyn, *Control Systems and Reinforcement Learning*** (2022,
  [Cambridge University Press](https://doi.org/10.1017/9781009051873)).
  Control theory, Markov decision processes, stochastic approximation,
  and the ODE analysis of reinforcement-learning algorithms. A
  graduate text written from the control-theoretic side.
* **Alekh Agarwal, Kianté Brantley, Nan Jiang, Sham M. Kakade, and Wen
  Sun, *Reinforcement Learning: Theory and Algorithms*** (unpublished
  [draft dated 27 June
  2026](https://rltheorybook.github.io/rltheorybook_ABJKS.pdf);
  [authors' site](https://rltheorybook.github.io/)). Sample complexity
  of tabular and function-approximation reinforcement learning,
  policy-gradient convergence, exploration, and offline learning. The
  standard theoretical reference. Cite the dated draft rather than
  treating it as a published book.

<a id="cks-113e"></a>

### 113E. Privacy, Fairness, and Distribution Shift

Constraints on how data may be released and used, and the failure of
the assumption that training and deployment data share a distribution.
Robust statistics is in Section 104 and causal inference, which bears
on both fairness and shift, in Section 109.

#### Foundational works

* **Hidetoshi Shimodaira, “Improving Predictive Inference under
  Covariate Shift by Weighting the Log-Likelihood Function”** (2000,
  [Journal of Statistical Planning and Inference 90,
  227–244](https://doi.org/10.1016/S0378-3758(00)00115-4)). Importance
  weighting of the likelihood when covariate distributions differ
  between training and prediction. The basic statistical treatment of
  covariate shift.
* **Cynthia Dwork, Frank McSherry, Kobbi Nissim, and Adam Smith,
  “Calibrating Noise to Sensitivity in Private Data Analysis”** (2006,
  [Theory of Cryptography Conference, Lecture Notes in Computer
  Science 3876, 265–284](https://doi.org/10.1007/11681878_14)). The
  definition of differential privacy and the Laplace mechanism. The
  founding paper.
* **Joaquin Quiñonero-Candela, Masashi Sugiyama, Anton Schwaighofer, and
  Neil D. Lawrence (eds.), *Dataset Shift in Machine Learning*** (2009,
  [MIT Press](https://doi.org/10.7551/mitpress/9780262170055.001.0001)).
  Covariate shift, label shift, and their correction by reweighting and
  by modelling. The first collected treatment of the subject.
* **Larry Wasserman and Shuheng Zhou, “A Statistical Framework for
  Differential Privacy”** (2010, [Journal of the American Statistical
  Association 105,
  375–389](https://doi.org/10.1198/jasa.2009.tm08651)). Differential
  privacy interpreted through hypothesis testing, with rates for
  private density estimation and release. The entry of differential
  privacy into statistics.
* **Shai Ben-David, John Blitzer, Koby Crammer, Alex Kulesza, Fernando
  Pereira, and Jennifer Wortman Vaughan, “A Theory of Learning from
  Different Domains”** (2010, [Machine Learning 79,
  151–175](https://doi.org/10.1007/s10994-009-5152-4)). Target-domain
  error bounded by source error, a divergence between input
  distributions, and the best combined source-and-target error within
  the hypothesis class. The basic learning-theoretic bound for domain
  adaptation.

#### More recent works

* **Cynthia Dwork and Aaron Roth, *The Algorithmic Foundations of
  Differential Privacy*** (2014, [Foundations and Trends in
  Theoretical Computer Science 9,
  211–407](https://doi.org/10.1561/0400000042)). Mechanisms,
  composition, the sparse vector technique, and lower bounds. The
  standard reference.
* **Moritz Hardt, Eric Price, and Nathan Srebro, “Equality of
  Opportunity in Supervised Learning”** (2016, [Advances in Neural
  Information Processing Systems
  29](https://proceedings.neurips.cc/paper_files/paper/2016/hash/6a9659feb1216f14f7384ba499518b38-Abstract.html);
  [author manuscript](https://arxiv.org/abs/1610.02413)). Fairness
  criteria defined by conditional independence of predictions and
  protected attributes given the outcome, with optimal post-processing.
  A foundational paper of statistical fairness criteria.
* **John C. Duchi, Michael I. Jordan, and Martin J. Wainwright, “Minimax
  Optimal Procedures for Locally Private Estimation”** (2018, [Journal
  of the American Statistical Association 113,
  182–201](https://doi.org/10.1080/01621459.2017.1389735), with
  discussion). Minimax rates under local differential privacy, with
  the information-theoretic lower bounds. The statistical cost of
  privatizing each observation.
* **T. Tony Cai, Yichen Wang, and Linjun Zhang, “The Cost of Privacy:
  Optimal Rates of Convergence for Parameter Estimation with
  Differential Privacy”** (2021, [Annals of Statistics 49,
  2825–2850](https://doi.org/10.1214/21-AOS2058)). Minimax rates for
  mean estimation and linear regression under central differential
  privacy. The central-model counterpart to Duchi–Jordan–Wainwright.
* **Solon Barocas, Moritz Hardt, and Arvind Narayanan, *Fairness and
  Machine Learning: Limitations and Opportunities*** (2023, [MIT
  Press](https://mitpress.mit.edu/9780262048613/fairness-and-machine-learning/);
  [authors' site](https://fairmlbook.org/)). Classification criteria,
  their incompatibilities, causal views of discrimination, and the
  data-collection process. The graduate text on fairness.

---

<a id="cks-114"></a>

## 114. Optimization and Numerical Algorithms for Data Science

The algorithms used to fit models and compress large data matrices,
with convergence rates, numerical stability, and computational cost.
Subdivision 114A collects optimization on Euclidean and manifold
parameter spaces; 114B covers matrix computation and low-dimensional
models. Statistical guarantees for fitted models remain in Section
107; stochastic approximation and sampling dynamics are in Section 112.

<a id="cks-114a"></a>

### 114A. Convex, Stochastic, and Riemannian Optimization

Duality, first-order and proximal algorithms, stochastic gradients,
online learning, automatic differentiation, and optimization under
geometric constraints. Convex analysis as mathematics is in Section 12.

#### Foundational works

* **Arkadi S. Nemirovski and David B. Yudin, *Problem Complexity and
  Method Efficiency in Optimization*** (1983, Wiley; Russian original
  1979). Oracle complexity, lower bounds for first-order methods, and
  mirror descent. The origin of the complexity theory that the later
  texts in this subdivision develop.
* **Aharon Ben-Tal and Arkadi Nemirovski, *Lectures on Modern Convex
  Optimization: Analysis, Algorithms, and Engineering Applications***
  (2001, [SIAM](https://doi.org/10.1137/1.9780898718829)). Conic,
  second-order cone, and semidefinite programming, with
  interior-point methods and robust optimization. The graduate text on
  conic modelling.
* **Yurii Nesterov, *Lectures on Convex Optimization***. Listed in full
  in Section 12. Complexity bounds, accelerated gradient methods, and
  smoothing.
* **Stephen Boyd and Lieven Vandenberghe, *Convex Optimization***
  (2004, [Cambridge University
  Press](https://doi.org/10.1017/CBO9780511804441)). Convex sets
  and functions, duality, constrained optimization, and numerical
  methods, with statistical estimation among the applications.
  The standard modelling and computational foundation.
* **Jorge Nocedal and Stephen J. Wright, *Numerical Optimization***
  (2nd ed., 2006, [Springer](https://doi.org/10.1007/978-0-387-40065-5);
  first ed. 1999). Line search and trust-region methods,
  quasi-Newton and limited-memory methods, least squares, and
  constrained optimization. The standard reference for smooth
  numerical optimization.
* **Andreas Griewank and Andrea Walther, *Evaluating Derivatives:
  Principles and Techniques of Algorithmic Differentiation*** (2nd
  ed., 2008, [SIAM](https://doi.org/10.1137/1.9780898717761); first
  ed., Griewank alone, 2000). Forward and reverse modes, their cost,
  checkpointing, and higher derivatives. The reference for the
  algorithm behind backpropagation.
* **Arkadi Nemirovski, Anatoli Juditsky, Guanghui Lan, and Alexander
  Shapiro, “Robust Stochastic Approximation Approach to Stochastic
  Programming”** (2009, [SIAM Journal on Optimization 19,
  1574–1609](https://doi.org/10.1137/070704277)). Stochastic mirror
  descent with iterate averaging and its non-asymptotic rates. The
  complexity analysis of stochastic gradient methods used in
  learning.
* **Amir Beck and Marc Teboulle, “A Fast Iterative
  Shrinkage-Thresholding Algorithm for Linear Inverse Problems”**
  (2009, [SIAM Journal on Imaging Sciences 2,
  183–202](https://doi.org/10.1137/080716542)). FISTA: accelerated
  proximal gradient for composite objectives, with the optimal rate.
  The standard algorithm for lasso-type problems.
* **Heinz H. Bauschke and Patrick L. Combettes, *Convex Analysis and
  Monotone Operator Theory in Hilbert Spaces***. Listed in full in
  Section 12. Proximal operators, monotone operators, and splitting
  algorithms, the theory behind proximal methods and ADMM.
* **Pierre-Antoine Absil, Robert Mahony, and Rodolphe Sepulchre,
  *Optimization Algorithms on Matrix Manifolds*** (2008, [Princeton
  University Press](https://doi.org/10.1515/9781400830244); [author's
  site](https://sites.uclouvain.be/absil/amsbook/)). Riemannian
  gradients, Newton and trust-region methods, especially on Stiefel and
  Grassmann manifolds, used to fit geometric models in 110A. The recent
  graduate text is Boumal, below.

#### More recent works

* **Stephen Boyd, Neal Parikh, Eric Chu, Borja Peleato, and Jonathan
  Eckstein, “Distributed Optimization and Statistical Learning via the
  Alternating Direction Method of Multipliers”** (2011, [Foundations
  and Trends in Machine Learning 3,
  1–122](https://doi.org/10.1561/2200000016)). ADMM, its convergence,
  and its use for distributed and regularized estimation. The
  standard account of the method in statistics and learning.
* **John Duchi, Elad Hazan, and Yoram Singer, “Adaptive Subgradient
  Methods for Online Learning and Stochastic Optimization”** (2011,
  [Journal of Machine Learning Research 12,
  2121–2159](https://www.jmlr.org/papers/v12/duchi11a.html)).
  AdaGrad: coordinate-wise step sizes adapted to past gradients, with
  regret bounds. The origin of the adaptive methods used to train
  networks.
* **Neal Parikh and Stephen Boyd, “Proximal Algorithms”** (2014,
  [Foundations and Trends in Optimization 1,
  127–239](https://doi.org/10.1561/2400000003)). Proximal operators,
  their calculus, and the algorithms built from them. A concise
  reference for nonsmooth composite optimization.
* **Diederik P. Kingma and Jimmy Ba, “Adam: A Method for Stochastic
  Optimization”** (2015, ICLR; [author
  manuscript](https://arxiv.org/abs/1412.6980)). Adaptive moment
  estimation with bias correction. The default optimizer for deep
  learning; its convergence theory is more delicate than the original
  analysis suggested.
* **Amir Beck, *First-Order Methods in Optimization***. Listed in full
  in Section 12. Proximal, mirror, and primal–dual methods, with
  complete proofs.
* **Sébastien Bubeck, *Convex Optimization: Algorithms and Complexity***
  (2015, [Foundations and Trends in Machine Learning 8,
  231–357](https://doi.org/10.1561/2200000050); [author
  manuscript](https://arxiv.org/abs/1405.4980)). Oracle complexity,
  accelerated gradients, mirror descent, conditional gradients, proximal
  methods, and stochastic optimization. A concise theoretical account of
  the rates behind algorithms used in learning.
* **Prateek Jain and Purushottam Kar, “Non-convex Optimization for
  Machine Learning”** (2017, [Foundations and Trends in Machine
  Learning 10, 142–363](https://doi.org/10.1561/2200000058)).
  Projected gradient, alternating minimization, and expectation
  maximization for sparse recovery, low-rank problems, and robust
  regression, with guarantees from restricted strong convexity. An
  account of when non-convex learning problems are tractable.
* **Guanghui Lan, *First-order and Stochastic Optimization Methods for
  Machine Learning*** (2020,
  [Springer](https://doi.org/10.1007/978-3-030-39568-1)). Deterministic
  and stochastic first-order methods, variance reduction, distributed
  and nonconvex optimization, and projection-free methods. A
  research-level text on the methods of this subdivision.
* **Alexander Shapiro, Darinka Dentcheva, and Andrzej Ruszczyński,
  *Lectures on Stochastic Programming: Modeling and Theory*** (3rd
  ed., 2021, [SIAM](https://doi.org/10.1137/1.9781611976595); first ed.
  2009). Sample average approximation and its asymptotics, risk
  measures, and distributionally robust optimization. The
  stochastic-programming view of empirical risk minimization.
* **Elad Hazan, *Introduction to Online Convex Optimization*** (2nd ed.,
  2022, MIT Press; first ed. 2016, [Foundations and Trends in
  Optimization](https://doi.org/10.1561/2400000013)). Regret
  minimization by online gradient descent,
  follow-the-regularized-leader, and mirror descent, with applications
  to bandits and boosting. The standard text on online learning as
  optimization.
* **Léon Bottou, Frank E. Curtis, and Jorge Nocedal, “Optimization
  Methods for Large-Scale Machine Learning”** (2018, [SIAM Review
  60, 223–311](https://doi.org/10.1137/16M1080173)).
  Empirical-risk minimization, stochastic gradients, variance
  reduction, and second-order methods. A substantial survey
  connecting optimization analysis to the computational demands
  of learning.
* **Stephen J. Wright and Benjamin Recht, *Optimization for Data
  Analysis*** (2022, [Cambridge University
  Press](https://doi.org/10.1017/9781009004282)). Gradient and
  accelerated methods, stochastic and coordinate descent,
  constrained and nonsmooth problems, duality, and backpropagation.
  A graduate course organized around the optimization problems
  encountered in data analysis.
* **Nicolas Boumal, *An Introduction to Optimization on Smooth
  Manifolds*** (2023, [Cambridge University
  Press](https://doi.org/10.1017/9781009166164)). Riemannian gradients,
  Hessians, retractions, and trust-region methods, from first
  principles through convergence and complexity bounds. A graduate
  introduction alongside the matrix-manifold monograph of
  Absil–Mahony–Sepulchre.

<a id="cks-114b"></a>

### 114B. Numerical Linear Algebra, Randomization, and Low-Rank Models

Stable matrix factorizations, approximate singular subspaces, and
structured models that reduce the dimension and cost of computation.
Matrix analysis as mathematics is in Section 13.

#### Foundational works

* **Carl Eckart and Gale Young, “The Approximation of One Matrix by
  Another of Lower Rank”** (1936, [Psychometrika 1,
  211–218](https://doi.org/10.1007/BF02288367)). Truncated singular
  value decomposition as the best low-rank approximation. The theorem
  behind principal components and every low-rank method below.
* **Lloyd N. Trefethen and David Bau III, *Numerical Linear Algebra***
  (1997, [SIAM](https://doi.org/10.1137/1.9780898719574)). QR, SVD,
  least squares, conditioning, stability, and Krylov methods in forty
  lectures. The standard graduate course.
* **Daniel D. Lee and H. Sebastian Seung, “Learning the Parts of
  Objects by Non-negative Matrix Factorization”** (1999, [Nature 401,
  788–791](https://doi.org/10.1038/44565)). Nonnegative low-rank
  factorizations giving parts-based representations. The paper that
  made nonnegative factorization a standard tool.
* **Nicholas J. Higham, *Accuracy and Stability of Numerical
  Algorithms*** (2nd ed., 2002,
  [SIAM](https://doi.org/10.1137/1.9780898718027); first ed. 1996).
  Floating-point arithmetic, backward error analysis, and the
  stability of the basic matrix algorithms. The reference for the
  numerical reliability of computations on data.
* **Yousef Saad, *Iterative Methods for Sparse Linear Systems*** (2nd
  ed., 2003, [SIAM](https://doi.org/10.1137/1.9780898718003); first
  ed. 1996). Krylov subspace methods and preconditioning for large
  sparse problems. The reference for the iterative solvers used on
  large sparse data matrices and graph Laplacians.
* **Gene H. Golub and Charles F. Van Loan, *Matrix Computations***
  (4th ed., 2013, [Johns Hopkins University
  Press](https://doi.org/10.56021/9781421407944); first ed. 1983).
  Least squares, QR and singular value decompositions, eigenvalue
  problems, conditioning, and numerical stability. The reference
  for the matrix algorithms underlying principal components,
  regression, and spectral methods.
* **Roger A. Horn and Charles R. Johnson, *Matrix Analysis***. Listed
  in full in Section 13. Norms, eigenvalue inequalities, and
  perturbation theory used throughout this subdivision.

* **Rajendra Bhatia, *Matrix Analysis***. Listed in full in Section
  13. Eigenvalue and singular-value perturbation, including the
  Davis–Kahan theorems used by spectral methods.

#### More recent works

* **Emmanuel J. Candès and Benjamin Recht, “Exact Matrix Completion via
  Convex Optimization”** (2009, [Foundations of Computational
  Mathematics 9, 717–772](https://doi.org/10.1007/s10208-009-9045-5)).
  Recovery of a low-rank matrix from few entries by nuclear-norm
  minimization, under incoherence. The foundational matrix-completion
  result.
* **Tamara G. Kolda and Brett W. Bader, “Tensor Decompositions and
  Applications”** (2009, [SIAM Review 51,
  455–500](https://doi.org/10.1137/07070111X)). CP and Tucker
  decompositions, their computation, and their uses in data analysis.
  The standard survey of tensor methods.
* **Michael W. Mahoney, “Randomized Algorithms for Matrices and
  Data”** (2011, [Foundations and Trends in Machine Learning 3,
  123–224](https://doi.org/10.1561/2200000035)). Random sampling and
  projection for least squares and low-rank approximation, with
  leverage scores. The data-analytic survey of randomized linear
  algebra.
* **Emmanuel J. Candès, Xiaodong Li, Yi Ma, and John Wright, “Robust
  Principal Component Analysis?”** (2011, [Journal of the ACM 58,
  article 11](https://doi.org/10.1145/1970392.1970395)). Exact
  separation of a low-rank matrix from sparse corruptions by convex
  programming. The robust counterpart of principal components.
* **Nathan Halko, Per-Gunnar Martinsson, and Joel A. Tropp, “Finding
  Structure with Randomness: Probabilistic Algorithms for Constructing
  Approximate Matrix Decompositions”** (2011, [SIAM Review 53,
  217–288](https://doi.org/10.1137/090771806)).
  Randomized range finding, low-rank approximation, error bounds,
  and algorithms that reduce passes over large matrices.
  A foundational survey of randomized matrix computation for
  principal components and data compression.
* **David P. Woodruff, “Sketching as a Tool for Numerical Linear
  Algebra”** (2014, [Foundations and Trends in Theoretical Computer
  Science 10, 1–157](https://doi.org/10.1561/0400000060)). Subspace
  embeddings and sketches for regression, low-rank approximation, and
  streaming. The theoretical-computer-science account of sketching.
* **Lars Eldén, *Matrix Methods in Data Mining and Pattern
  Recognition*** (2nd ed., 2019,
  [SIAM](https://doi.org/10.1137/1.9781611975864); first ed. 2007).
  Least squares, SVD, clustering, nonnegative factorization, tensors,
  and page ranking as matrix computations. A short course connecting
  numerical linear algebra to data analysis.
* **Madeleine Udell and Alex Townsend, “Why Are Big Data Matrices
  Approximately Low Rank?”** (2019, [SIAM Journal on Mathematics of
  Data Science 1, 144–160](https://doi.org/10.1137/18M1183480)).
  Matrices generated from bounded latent variables by a piecewise
  analytic function admit low-rank approximations with controlled
  entrywise error. A mathematical explanation for the success of
  low-rank models under these assumptions.
* **Per-Gunnar Martinsson and Joel A. Tropp, “Randomized Numerical
  Linear Algebra: Foundations and Algorithms”** (2020, [Acta Numerica
  29, 403–572](https://doi.org/10.1017/S0962492920000021)). Random
  embeddings, randomized range finders, Nyström approximation,
  trace estimation, and Krylov methods with random starts. The
  current comprehensive survey.
* **Nicolas Gillis, *Nonnegative Matrix Factorization*** (2020,
  [SIAM](https://doi.org/10.1137/1.9781611976410)). Identifiability,
  separability, complexity, and algorithms for nonnegative
  factorization. The research monograph.
* **Yuxin Chen, Yuejie Chi, Jianqing Fan, and Cong Ma, “Spectral
  Methods for Data Science: A Statistical Perspective”** (2021,
  [Foundations and Trends in Machine Learning 14,
  566–806](https://doi.org/10.1561/2200000079)). Matrix perturbation
  theory, ℓ∞ and ℓ2,∞ eigenvector bounds, and their use in
  clustering, ranking, matrix completion, and phase retrieval. The
  statistical theory of the spectral methods in 110A and 113C.
* **John Wright and Yi Ma, *High-Dimensional Data Analysis with
  Low-Dimensional Models: Principles, Computation, and Applications***
  (2022, [Cambridge University
  Press](https://doi.org/10.1017/9781108779302)). Sparse, low-rank, and
  related low-dimensional models, in convex and non-convex
  formulations, with algorithms and applications. The geometric
  models complement 110A. The statistical theory of sparsity is in
  Section 107, and compressive sensing is in Section 29.
