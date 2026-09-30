import GapFamily.Analytic.Elliptic.LocalSobolevCompactAverage

/-!
# Actual normalized mollifier approximation

The normalized smooth bump gives a literal probability measure, and its ordinary
convolution has squared L² error at most radius squared times derivative energy.
-/

noncomputable section

namespace GapFamily.Analytic.LocalSobolev

open Set MeasureTheory ContinuousLinearMap
open scoped ContDiff Convolution

/-- The actual probability measure of a normalized smooth bump. -/
def bumpMeasure (ρ : ContDiffBump (0 : ℂ)) : Measure ℂ :=
  volume.withDensity (fun h => ENNReal.ofReal (ρ.normed volume h))

instance bumpMeasure_probability (ρ : ContDiffBump (0 : ℂ)) :
    IsProbabilityMeasure (bumpMeasure ρ) where
  measure_univ := by
    rw [bumpMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal (ρ.integrable_normed (μ := volume))
        (Filter.Eventually.of_forall (ρ.nonneg_normed (μ := volume))), ρ.integral_normed (μ := volume)]
    simp

theorem bumpMeasure_ae_norm_le (ρ : ContDiffBump (0 : ℂ)) :
    ∀ᵐ h ∂bumpMeasure ρ, ‖h‖ ≤ ρ.rOut := by
  rw [bumpMeasure, ae_withDensity_iff
    (show Measurable (fun h : ℂ => ENNReal.ofReal (ρ.normed volume h)) from
      ENNReal.measurable_ofReal.comp (ρ.continuous_normed (μ := volume)).measurable)]
  exact Filter.Eventually.of_forall fun h hh => by
    have hs : h ∈ Function.support (ρ.normed volume) := by
      intro hz
      exact hh (by simp [hz])
    rw [ρ.support_normed_eq] at hs
    exact (by simpa only [Metric.mem_ball, dist_zero_right] using hs : ‖h‖ < ρ.rOut).le

/-- The genuine ordinary convolution by the normalized smooth bump. -/
def mollify (ρ : ContDiffBump (0 : ℂ)) (f : ℂ → ℂ) : ℂ → ℂ :=
  ρ.normed volume ⋆[lsmul ℝ ℝ, volume] f

theorem mollify_eq_translationAverage (ρ : ContDiffBump (0 : ℂ))
    (f : ℂ → ℂ) (z : ℂ) :
    mollify ρ f z = translationAverage (bumpMeasure ρ) f z := by
  rw [translationAverage, bumpMeasure, integral_withDensity_eq_integral_toReal_smul
    (show Measurable (fun h : ℂ => ENNReal.ofReal (ρ.normed volume h)) from
      ENNReal.measurable_ofReal.comp (ρ.continuous_normed (μ := volume)).measurable)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (ρ.nonneg_normed _)]
  change (∫ h : ℂ, ρ.normed volume h • f (z - h)) =
    ∫ h : ℂ, ρ.normed volume h • f (z + h)
  rw [← integral_neg_eq_self (fun h : ℂ => ρ.normed volume h • f (z + h))]
  simp only [ρ.normed_neg, sub_eq_add_neg]

theorem integrable_mollify_error_sq (ρ : ContDiffBump (0 : ℂ)) (f : ℂ → ℂ)
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    Integrable (fun z => ‖mollify ρ f z - f z‖ ^ 2) := by
  simp_rw [mollify_eq_translationAverage]
  exact integrable_translationAverage_error_sq (bumpMeasure ρ) f hf hc
    ρ.rOut_pos.le (bumpMeasure_ae_norm_le ρ)

/-- Actual mollifier approximation with a quantitative derivative-energy bound. -/
theorem integral_mollify_error_sq_le (ρ : ContDiffBump (0 : ℂ)) (f : ℂ → ℂ)
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    (∫ z : ℂ, ‖mollify ρ f z - f z‖ ^ 2) ≤
      ρ.rOut ^ 2 * ∫ z : ℂ, ‖fderiv ℝ f z‖ ^ 2 := by
  simp_rw [mollify_eq_translationAverage]
  exact integral_translationAverage_error_sq_le (bumpMeasure ρ) f hf hc
    ρ.rOut_pos.le (bumpMeasure_ae_norm_le ρ)

end GapFamily.Analytic.LocalSobolev
