import GapFamily.Analytic.Elliptic.LocalSobolevCompactTranslation
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Quantitative local averaging approximation

Actual averages of translations by a probability measure supported in a radius-r
ball approximate a C¹ compactly supported function with squared L² error at most
r² times its Euclidean derivative energy. Integrability and Fubini are proved.
-/

noncomputable section

namespace GapFamily.Analytic.LocalSobolev

open Set MeasureTheory
open scoped ContDiff

/-- An actual ordinary average of translated values. -/
def translationAverage (ν : Measure ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∫ h, f (z + h) ∂ν

private theorem integrable_shift (ν : Measure ℂ) [IsProbabilityMeasure ν]
    (f : ℂ → ℂ) (hf : Continuous f) (hc : HasCompactSupport f) (z : ℂ) :
    MemLp (fun h => f (z + h)) 2 ν :=
  (hf.comp (continuous_const.add continuous_id)).memLp_of_hasCompactSupport
    (hc.comp_homeomorph (Homeomorph.addLeft z))

theorem translationAverage_sub (ν : Measure ℂ) [IsProbabilityMeasure ν]
    (f : ℂ → ℂ) (hf : Continuous f) (hc : HasCompactSupport f) (z : ℂ) :
    translationAverage ν f z - f z = ∫ h, f (z + h) - f z ∂ν := by
  rw [integral_sub ((integrable_shift ν f hf hc z).integrable (by norm_num)) (integrable_const _)]
  simp [translationAverage]

theorem translationAverage_error_sq_le (ν : Measure ℂ) [IsProbabilityMeasure ν]
    (f : ℂ → ℂ) (hf : Continuous f) (hc : HasCompactSupport f) (z : ℂ) :
    ‖translationAverage ν f z - f z‖ ^ 2 ≤ ∫ h, ‖f (z + h) - f z‖ ^ 2 ∂ν := by
  rw [translationAverage_sub ν f hf hc z]
  have hp : MemLp (fun h => f (z + h) - f z) 2 ν :=
    (integrable_shift ν f hf hc z).sub (memLp_const _)
  exact norm_integral_sq_le_integral_norm_sq (hp.integrable (by norm_num))
    ((memLp_two_iff_integrable_sq_norm hp.aestronglyMeasurable).mp hp)

theorem integrable_translationAverage_error_joint (ν : Measure ℂ) [IsProbabilityMeasure ν]
    (f : ℂ → ℂ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    {r : ℝ} (_hr : 0 ≤ r) (hν : ∀ᵐ h ∂ν, ‖h‖ ≤ r) :
    Integrable (fun p : ℂ × ℂ => ‖f (p.2 + p.1) - f p.2‖ ^ 2) (ν.prod volume) := by
  have hmeas : AEStronglyMeasurable
      (fun p : ℂ × ℂ => ‖f (p.2 + p.1) - f p.2‖ ^ 2) (ν.prod volume) :=
    (show Continuous (fun p : ℂ × ℂ => ‖f (p.2 + p.1) - f p.2‖ ^ 2) by fun_prop).aestronglyMeasurable
  have he := integrable_fderiv_energy f hf hc
  apply (integrable_prod_iff hmeas).mpr
  constructor
  · exact Filter.Eventually.of_forall fun h => integrable_translation_error_sq f hf he h
  · apply (integrable_const (r ^ 2 * ∫ z : ℂ, ‖fderiv ℝ f z‖ ^ 2)).mono'
    · exact hmeas.norm.integral_prod_right'
    · filter_upwards [hν] with h hh
      have hnonneg : 0 ≤ ∫ z : ℂ, ‖f (z + h) - f z‖ ^ 2 :=
        integral_nonneg fun _ => sq_nonneg _
      simp only [Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg hnonneg]
      refine (integral_translation_error_sq_le f hf he h).trans ?_
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hh 2)
        (integral_nonneg fun _ => sq_nonneg _)

theorem integrable_translationAverage_error_sq (ν : Measure ℂ) [IsProbabilityMeasure ν]
    (f : ℂ → ℂ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    {r : ℝ} (hr : 0 ≤ r) (hν : ∀ᵐ h ∂ν, ‖h‖ ≤ r) :
    Integrable (fun z => ‖translationAverage ν f z - f z‖ ^ 2) := by
  have hjoint := integrable_translationAverage_error_joint ν f hf hc hr hν
  apply hjoint.integral_prod_right.mono'
  · have hmeas : AEStronglyMeasurable
        (fun p : ℂ × ℂ => f (p.1 + p.2) - f p.1) (volume.prod ν) :=
      (show Continuous (fun p : ℂ × ℂ => f (p.1 + p.2) - f p.1) by fun_prop).aestronglyMeasurable
    apply (hmeas.integral_prod_right'.norm.pow 2).congr
    filter_upwards with z
    simp only [Pi.pow_apply, translationAverage_sub ν f hf.continuous hc]
  · exact Filter.Eventually.of_forall fun z => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact translationAverage_error_sq_le ν f hf.continuous hc z

/-- A quantitative actual averaging approximation, uniform over an energy-bounded family. -/
theorem integral_translationAverage_error_sq_le (ν : Measure ℂ) [IsProbabilityMeasure ν]
    (f : ℂ → ℂ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    {r : ℝ} (hr : 0 ≤ r) (hν : ∀ᵐ h ∂ν, ‖h‖ ≤ r) :
    (∫ z : ℂ, ‖translationAverage ν f z - f z‖ ^ 2) ≤
      r ^ 2 * ∫ z : ℂ, ‖fderiv ℝ f z‖ ^ 2 := by
  have hjoint := integrable_translationAverage_error_joint ν f hf hc hr hν
  have he := integrable_fderiv_energy f hf hc
  calc
    _ ≤ ∫ z : ℂ, ∫ h, ‖f (z + h) - f z‖ ^ 2 ∂ν := by
      apply integral_mono (integrable_translationAverage_error_sq ν f hf hc hr hν)
        hjoint.integral_prod_right
      exact fun z => translationAverage_error_sq_le ν f hf.continuous hc z
    _ = ∫ h, (∫ z : ℂ, ‖f (z + h) - f z‖ ^ 2) ∂ν :=
      (integral_integral_swap (f := fun h z => ‖f (z + h) - f z‖ ^ 2) hjoint).symm
    _ ≤ ∫ _h : ℂ, (r ^ 2 * ∫ z : ℂ, ‖fderiv ℝ f z‖ ^ 2) ∂ν := by
      apply integral_mono_ae hjoint.integral_prod_left (integrable_const _)
      filter_upwards [hν] with h hh
      refine (integral_translation_error_sq_le f hf he h).trans ?_
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hh 2)
        (integral_nonneg fun _ => sq_nonneg _)
    _ = _ := by simp

end GapFamily.Analytic.LocalSobolev
