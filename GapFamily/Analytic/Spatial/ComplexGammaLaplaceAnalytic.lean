import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import GapFamily.Analytic.Foundation.AnalyticDominatedIntegral

/-!
# Ordinary complex-rate Gamma-Laplace analyticity

On the positive energy axis the norm of the complex power depends only on
the real part of its exponent. A disk of radius `Re r / 2` around a positive
real-part rate has one ordinary Gamma majorant. This proves integrability
and analytic dependence on the rate by dominated integration.
-/

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open Set Filter MeasureTheory
open DominatedAnalytic

/-- The literal Gamma-Laplace integrand with complex exponent and rate. -/
def gammaLaplaceIntegrand (s r : ℂ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ (s - 1) * Complex.exp (-r * (t : ℂ))

/-- Exact norm on the positive integration axis. -/
theorem norm_gammaLaplaceIntegrand (s r : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖gammaLaplaceIntegrand s r t‖ =
      t ^ (s.re - 1) * Real.exp (-r.re * t) := by
  rw [gammaLaplaceIntegrand, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_exp]
  simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.neg_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

/-- Energy continuity requires no condition on the complex parameters. -/
theorem continuousOn_gammaLaplaceIntegrand (s r : ℂ) :
    ContinuousOn (gammaLaplaceIntegrand s r) (Ioi 0) := by
  apply ContinuousOn.mul
  · exact Complex.continuous_ofReal.continuousOn.cpow_const (fun t ht => Or.inl ht)
  · fun_prop

private theorem integrableOn_gammaRealMajorant {σ δ : ℝ} (hσ : 0 < σ) (hδ : 0 < δ) :
    IntegrableOn (fun t : ℝ => t ^ (σ - 1) * Real.exp (-δ * t)) (Ioi 0) := by
  simpa only [Real.rpow_one] using
    (integrableOn_rpow_mul_exp_neg_mul_rpow (s := σ - 1) (p := 1) (b := δ)
      (by linarith) zero_lt_one hδ)

/-- Ordinary absolute integrability for every exponent and rate with positive real part. -/
theorem integrableOn_gammaLaplaceIntegrand {s r : ℂ}
    (hs : 0 < s.re) (hr : 0 < r.re) :
    IntegrableOn (gammaLaplaceIntegrand s r) (Ioi 0) := by
  apply (integrableOn_gammaRealMajorant hs hr).mono'
  · exact (continuousOn_gammaLaplaceIntegrand s r).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (norm_gammaLaplaceIntegrand s r ht).le

/-- The ordinary Gamma-Laplace integral is analytic in its complex rate on
its full right half-plane of absolute convergence. -/
theorem analyticAt_gammaLaplaceIntegral {s r : ℂ} (hs : 0 < s.re) (hr : 0 < r.re) :
    AnalyticAt ℂ (fun z : ℂ => ∫ t : ℝ in Ioi 0, gammaLaplaceIntegrand s z t) r := by
  apply analyticAt_integral_of_dominated (r := r.re / 2)
    (bound := fun t : ℝ => t ^ (s.re - 1) * Real.exp (-(r.re / 2) * t)) (half_pos hr)
  · intro z hz
    exact (continuousOn_gammaLaplaceIntegrand s z).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [] with t
    intro z hz
    unfold gammaLaplaceIntegrand
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro z hz
    have hdist : ‖z - r‖ < r.re / 2 := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hz
    have hle : |z.re - r.re| ≤ ‖z - r‖ := by
      simpa only [Complex.sub_re] using Complex.abs_re_le_norm (z - r)
    have habs : |z.re - r.re| < r.re / 2 := hle.trans_lt hdist
    have hre : r.re / 2 ≤ z.re := by
      have hh := (abs_lt.mp habs).1
      linarith
    rw [norm_gammaLaplaceIntegrand s z ht]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (le_of_lt ht) _)
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hre) (le_of_lt ht))
  · exact integrableOn_gammaRealMajorant hs (half_pos hr)

end GapFamily.Analytic.SpatialPoint
