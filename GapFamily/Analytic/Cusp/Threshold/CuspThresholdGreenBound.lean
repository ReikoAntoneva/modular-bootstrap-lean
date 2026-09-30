import GapFamily.Analytic.Cusp.Threshold.CuspThresholdGreenProfile
import GapFamily.Analytic.Cusp.Profile.CuspWeightedFirstMoment

/-! A bound uniform over all observed logarithmic heights for the actual threshold response. -/
noncomputable section
namespace GapFamily.Analytic.CuspThresholdGreenProfile
open Set Filter MeasureTheory CuspHalfLineLaplace CuspWeightedFirstMoment

/-- The actual removable min-kernel is bounded by the source coordinate on the positive half-line. -/
theorem greenProfile_integrand_norm_le {α t u : ℝ} (ht : 0 ≤ t) (hu : 0 ≤ u)
    (f : HalfLineL2) :
    ‖cuspGreen 0 t u 0 * Complex.exp (-(α : ℂ) * u) * f u‖ ≤
      u * Real.exp (-α * u) * ‖f u‖ := by
  rw [cuspGreen_zero, sub_zero, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (le_min ht hu), Complex.norm_exp]
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
    Complex.ofReal_im, mul_zero, sub_zero]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (min_le_right t u) (Real.exp_nonneg _)) (norm_nonneg _)

/-- Ordinary first-moment domination gives a bound independent of the observed height. -/
theorem greenProfile_norm_le {α t : ℝ} (hα : 0 < α) (ht : 0 ≤ t) (f : HalfLineL2) :
    ‖greenProfile α f t‖ ≤
      ((2 / α) * ‖exponential ((α / 2 : ℝ) : ℂ)‖) * ‖f‖ := by
  calc
    _ ≤ ∫ u : ℝ in Ioi 0,
        ‖cuspGreen 0 t u 0 * Complex.exp (-(α : ℂ) * u) * f u‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ u : ℝ in Ioi 0, u * Real.exp (-α * u) * ‖f u‖ := by
      apply integral_mono_ae (greenProfile_integrable hα f t).norm
        (firstMoment_integrable hα f)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact greenProfile_integrand_norm_le ht hu.le f
    _ ≤ _ := firstMoment_integral_le hα f

/-- The actual continuous-collar Green operators have one bound for every output window. -/
theorem greenLocal_norm_le {α L T : ℝ} (hα : 0 < α) (hT : 0 ≤ T)
    (hLT : L ≤ T) (f : HalfLineL2) :
    ‖cuspGreenWeightedLocalOperator α hα.le L T 0 f‖ ≤
      ((2 / α) * ‖exponential ((α / 2 : ℝ) : ℂ)‖) * ‖f‖ := by
  apply ContinuousMap.norm_le _ (by positivity) |>.mpr
  intro t
  rw [← greenProfile_eq_local hα hT hLT f t]
  exact greenProfile_norm_le hα t.property.1 f

/-- The physical square-root lift of the actual Green profile has uniform cusp growth. -/
theorem greenProfile_lift_norm_le {α y : ℝ} (hα : 0 < α) (hy : 1 ≤ y)
    (f : HalfLineL2) :
    ‖Real.sqrt y • greenProfile α f (Real.log y)‖ ≤
      (((2 / α) * ‖exponential ((α / 2 : ℝ) : ℂ)‖) * ‖f‖) * Real.sqrt y := by
  rw [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg y)]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left
    (greenProfile_norm_le hα (Real.log_nonneg hy) f) (Real.sqrt_nonneg y)

/-- At the actual residual source weight one quarter, the uniform constant is exactly sixteen. -/
theorem greenProfile_quarter_constant :
    ((2 / (1 / 4 : ℝ)) * ‖exponential ((((1 / 4 : ℝ) / 2) : ℝ) : ℂ)‖) = 16 := by
  have hs := exponential_norm_sq (β := (1 / 8 : ℂ)) (by norm_num)
  norm_num at hs
  have hn : ‖exponential (1 / 8 : ℂ)‖ = 2 := by
    nlinarith [norm_nonneg (exponential (1 / 8 : ℂ))]
  norm_num [show (((1 / 4 : ℝ) / 2 : ℝ) : ℂ) = (1 / 8 : ℂ) by norm_num, hn]

theorem greenProfile_quarter_norm_le {t : ℝ} (ht : 0 ≤ t) (f : HalfLineL2) :
    ‖greenProfile (1 / 4) f t‖ ≤ 16 * ‖f‖ := by
  simpa only [greenProfile_quarter_constant] using
    greenProfile_norm_le (by norm_num : (0 : ℝ) < 1 / 4) ht f

end GapFamily.Analytic.CuspThresholdGreenProfile
