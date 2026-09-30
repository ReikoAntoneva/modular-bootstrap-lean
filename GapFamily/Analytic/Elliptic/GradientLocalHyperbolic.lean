import GapFamily.Analytic.Elliptic.GradientLocalIBP
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Local hyperbolic gradient integration by parts

The test vector `y η` cancels the hyperbolic volume density `1/y²` against
the gradient component `y ∂f`. The resulting formal-divergence test is
`-y² ∂η`, with actual integrability inherited from local compact support.
-/

noncomputable section

namespace GapFamily.Analytic.Dirichlet

open Set MeasureTheory

/-- Hyperbolic area in complex coordinates restricted to a local open region. -/
def localHyperbolicMeasure (U : Set ℂ) : Measure ℂ :=
  (volume.restrict U).withDensity (fun z => ENNReal.ofReal (1 / z.im ^ 2))

theorem localHyperbolic_integral_im_sq_mul {U : Set ℂ} (hU : MeasurableSet U)
    (hupper : ∀ z ∈ U, 0 < z.im) (h : ℂ → ℂ) :
    (∫ z, (z.im : ℂ) ^ 2 * h z ∂localHyperbolicMeasure U) = ∫ z in U, h z := by
  rw [localHyperbolicMeasure, integral_withDensity_eq_integral_toReal_smul
    (by fun_prop : Measurable (fun z : ℂ => ENNReal.ofReal (1 / z.im ^ 2)))
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hU] with z hz
  rw [ENNReal.toReal_ofReal (by positivity), Complex.real_smul]
  have hn : (z.im : ℂ) ≠ 0 := by exact_mod_cast (hupper z hz).ne'
  push_cast
  field_simp

theorem localHyperbolic_integrable_im_sq_mul_iff {U : Set ℂ} (hU : MeasurableSet U)
    (hupper : ∀ z ∈ U, 0 < z.im) (h : ℂ → ℂ) :
    Integrable (fun z => (z.im : ℂ) ^ 2 * h z) (localHyperbolicMeasure U) ↔
      IntegrableOn h U := by
  rw [localHyperbolicMeasure, integrable_withDensity_iff_integrable_smul'
    (by fun_prop : Measurable (fun z : ℂ => ENNReal.ofReal (1 / z.im ^ 2)))
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integrable_congr
  filter_upwards [ae_restrict_mem hU] with z hz
  rw [ENNReal.toReal_ofReal (by positivity), Complex.real_smul]
  have hn : (z.im : ℂ) ≠ 0 := by exact_mod_cast (hupper z hz).ne'
  push_cast
  field_simp

/-- Both sides of the local hyperbolic gradient identity are ordinary integrable functions. -/
theorem local_hyperbolic_gradient_test_integrable {U : Set ℂ} {f g : ℂ → ℂ}
    (hU : IsOpen U) (hupper : ∀ z ∈ U, 0 < z.im)
    (hf : ContDiffOn ℝ 1 f U) (hg : ContDiff ℝ 1 g)
    (hc : HasCompactSupport g) (hs : tsupport g ⊆ U) (v : ℂ) :
    Integrable (fun z => ((z.im : ℂ) * fderiv ℝ f z v) * ((z.im : ℂ) * g z))
      (localHyperbolicMeasure U) ∧
    Integrable (fun z => f z * ((z.im : ℂ) ^ 2 * fderiv ℝ g z v))
      (localHyperbolicMeasure U) := by
  have hleft := (localHyperbolic_integrable_im_sq_mul_iff hU.measurableSet hupper
    (fun z => fderiv ℝ f z v * g z)).mpr
      ((local_fderiv_mul_test_integrable hU hf hg.continuous hc hs v).integrableOn)
  have hright := (localHyperbolic_integrable_im_sq_mul_iff hU.measurableSet hupper
    (fun z => f z * fderiv ℝ g z v)).mpr
      ((local_mul_fderiv_test_integrable hf.continuousOn hg hc hs v).integrableOn)
  constructor
  · convert hleft using 1
    ext z
    ring
  · convert hright using 1
    ext z
    ring

/-- Integration by parts for the actual `y ∂` gradient and hyperbolic area.
Choosing `v = 1` or `v = I` gives the horizontal or vertical coordinate. -/
theorem local_hyperbolic_gradient_test_identity {U : Set ℂ} {f g : ℂ → ℂ}
    (hU : IsOpen U) (hupper : ∀ z ∈ U, 0 < z.im)
    (hf : ContDiffOn ℝ 1 f U) (hg : ContDiff ℝ 1 g)
    (hc : HasCompactSupport g) (hs : tsupport g ⊆ U) (v : ℂ) :
    (∫ z, ((z.im : ℂ) * fderiv ℝ f z v) * ((z.im : ℂ) * g z)
      ∂localHyperbolicMeasure U) =
      -(∫ z, f z * ((z.im : ℂ) ^ 2 * fderiv ℝ g z v) ∂localHyperbolicMeasure U) := by
  have hleft : (fun z : ℂ => ((z.im : ℂ) * fderiv ℝ f z v) * ((z.im : ℂ) * g z)) =
      fun z => (z.im : ℂ) ^ 2 * (fderiv ℝ f z v * g z) := by
    ext z
    ring
  have hright : (fun z : ℂ => f z * ((z.im : ℂ) ^ 2 * fderiv ℝ g z v)) =
      fun z => (z.im : ℂ) ^ 2 * (f z * fderiv ℝ g z v) := by
    ext z
    ring
  rw [hleft, hright, localHyperbolic_integral_im_sq_mul hU.measurableSet hupper,
    localHyperbolic_integral_im_sq_mul hU.measurableSet hupper]
  exact local_setIntegral_fderiv_mul_eq_neg hU hf hg hc hs v

end GapFamily.Analytic.Dirichlet
