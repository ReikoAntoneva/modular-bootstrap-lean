import GapFamily.Analytic.Spatial.ComplexGammaLaplaceAnalytic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Convex

/-!
# Gamma-Laplace transform with a complex rate

The ordinary integral is analytic in the rate on its right half-plane. Its
values for positive real rates are Mathlib's real-substitution Gamma formula;
the analytic identity theorem proves the complex-rate formula on that whole
connected domain. No transform axiom is used.
-/

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open Set MeasureTheory Filter Complex
open scoped Topology

private theorem gammaLaplace_rate_identity (s : ℂ) (F : ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F {r : ℂ | 0 < r.re})
    (hreal : ∀ x : ℝ, 0 < x → F x = (x : ℂ) ^ (-s) * Complex.Gamma s)
    {r : ℂ} (hr : 0 < r.re) : F r = r ^ (-s) * Complex.Gamma s := by
  have hG : AnalyticOnNhd ℂ (fun z : ℂ => z ^ (-s) * Complex.Gamma s)
      {r : ℂ | 0 < r.re} := by
    apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
    intro z hz
    exact ((differentiableAt_id.cpow_const (Complex.mem_slitPlane_iff.mpr (Or.inl hz))).mul
      (differentiableAt_const (Complex.Gamma s))).differentiableWithinAt
  have hcast : Tendsto ((↑) : ℝ → ℂ) (𝓝[≠] 1) (𝓝[≠] 1) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · exact tendsto_nhdsWithin_of_tendsto_nhds Complex.continuous_ofReal.continuousAt
    · exact eventually_nhdsWithin_iff.mpr (Eventually.of_forall fun t ht =>
        Complex.ofReal_ne_one.mpr ht)
  have hfreq : ∃ᶠ z in 𝓝[≠] (1 : ℂ), F z = z ^ (-s) * Complex.Gamma s := by
    apply hcast.frequently
    apply ((Eventually.filter_mono nhdsWithin_le_nhds) ?_).frequently
    exact (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)).mono fun x hx => hreal x hx
  exact hF.eqOn_of_preconnected_of_frequently_eq hG
    (convex_halfSpace_re_gt (0 : ℝ)).isPreconnected (by simp) hfreq hr

private theorem gammaLaplace_positive_real {s : ℂ} (hs : 0 < s.re) {r : ℝ} (hr : 0 < r) :
    (∫ t : ℝ in Ioi 0, (t : ℂ) ^ (s - 1) * Complex.exp (-(r : ℂ) * (t : ℂ))) =
      (r : ℂ) ^ (-s) * Complex.Gamma s := by
  have h := Complex.integral_cpow_mul_exp_neg_mul_Ioi hs hr
  rw [one_div, Complex.inv_cpow_ofReal_nonneg hr.le, ← Complex.cpow_neg] at h
  simpa only [Complex.ofReal_mul, Complex.ofReal_neg, neg_mul] using h

/-- The ordinary Gamma-Laplace integral with a complex rate, throughout its
full half-plane of absolute convergence. The power uses the principal complex
branch, which is analytic because the rate has positive real part. -/
theorem integral_gammaLaplaceIntegrand {s r : ℂ} (hs : 0 < s.re) (hr : 0 < r.re) :
    (∫ t : ℝ in Ioi 0, (t : ℂ) ^ (s - 1) * Complex.exp (-r * (t : ℂ))) =
      r ^ (-s) * Complex.Gamma s := by
  apply gammaLaplace_rate_identity s
    (fun z => ∫ t : ℝ in Ioi 0, (t : ℂ) ^ (s - 1) * Complex.exp (-z * (t : ℂ)))
    (fun z hz => analyticAt_gammaLaplaceIntegral hs hz)
    (fun x hx => gammaLaplace_positive_real hs hx) hr

end GapFamily.Analytic.SpatialPoint
