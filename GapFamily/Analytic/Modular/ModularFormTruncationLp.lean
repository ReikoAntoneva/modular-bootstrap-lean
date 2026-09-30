import GapFamily.Analytic.Modular.ModularFormTruncationCore
import GapFamily.Analytic.Foundation.FormTruncationLp

noncomputable section
namespace GapFamily.Analytic.FormTruncation
open MeasureTheory UpperHalfPlane ModularGradient Filter
open scoped Topology

private theorem norm_lowProfile_mul_sub_le (n : ℕ) (y : ℝ) (a : ℂ) :
    ‖lowProfile n y * a - a‖ ≤ 2 * ‖a‖ := by
  calc
    _ ≤ ‖lowProfile n y * a‖ + ‖a‖ := norm_sub_le _ _
    _ ≤ 1 * ‖a‖ + ‖a‖ := by
      rw [norm_mul]
      exact add_le_add
        (mul_le_mul_of_nonneg_right (norm_lowProfile_le_one n y) (norm_nonneg a)) le_rfl
    _ = _ := by ring

/-- Explicit finite-height truncation converges in the actual value L² norm. -/
theorem value_truncatedCore_tendsto (F : smoothCore) :
    Tendsto (fun n => value (truncatedCore n F)) atTop (𝓝 (value F)) := by
  apply tendsto_L2_of_eventuallyEq_and_bound _ _ (fun τ : UpperHalfPlane => 2 * ‖F.val τ‖)
  · exact (F.property.2.2.1.norm.const_mul 2).integrable_sq
  · intro n
    filter_upwards [truncatedCore_value_ae n F, value_ae F] with τ htr hF
    rw [htr, hF]
    exact norm_lowProfile_mul_sub_le n τ.im (F.val τ)
  · have hall : ∀ᵐ τ ∂modularMeasure, ∀ n : ℕ,
        value (truncatedCore n F) τ = lowProfile n τ.im * F.val τ :=
      ae_all_iff.mpr (fun n => truncatedCore_value_ae n F)
    filter_upwards [hall, value_ae F] with τ htr hF
    filter_upwards [lowProfile_eventually_value_high_deriv τ.im] with n hn
    rw [htr n, hF, hn.1, one_mul]

/-- Explicit finite-height truncation converges in the actual horizontal gradient L² norm. -/
theorem xComponent_truncatedCore_tendsto (F : smoothCore) :
    Tendsto (fun n => xComponent (truncatedCore n F)) atTop (𝓝 (xComponent F)) := by
  have hFae : xComponent F =ᵐ[modularMeasure] directional F.val 1 :=
    component_ae 1 (fun G => G.property.2.2.2.1) F
  apply tendsto_L2_of_eventuallyEq_and_bound _ _
    (fun τ : UpperHalfPlane => 2 * ‖directional F.val 1 τ‖)
  · exact (F.property.2.2.2.1.norm.const_mul 2).integrable_sq
  · intro n
    filter_upwards [truncatedCore_xComponent_ae n F, hFae] with τ htr hF
    rw [htr, hF]
    exact norm_lowProfile_mul_sub_le n τ.im (directional F.val 1 τ)
  · have hall : ∀ᵐ τ ∂modularMeasure, ∀ n : ℕ,
        xComponent (truncatedCore n F) τ = lowProfile n τ.im * directional F.val 1 τ :=
      ae_all_iff.mpr (fun n => truncatedCore_xComponent_ae n F)
    filter_upwards [hall, hFae] with τ htr hF
    filter_upwards [lowProfile_eventually_value_high_deriv τ.im] with n hn
    rw [htr n, hF, hn.1, one_mul]

/-- The vertical correction is uniformly L² dominated and eventually vanishes at every height. -/
theorem yComponent_truncatedCore_tendsto (F : smoothCore) :
    Tendsto (fun n => yComponent (truncatedCore n F)) atTop (𝓝 (yComponent F)) := by
  obtain ⟨C, hC, hderiv⟩ := highProfile_weighted_deriv_bound
  have hFae : yComponent F =ᵐ[modularMeasure] directional F.val Complex.I :=
    component_ae Complex.I (fun G => G.property.2.2.2.2) F
  apply tendsto_L2_of_eventuallyEq_and_bound _ _
    (fun τ : UpperHalfPlane => 2 * ‖directional F.val Complex.I τ‖ + C * ‖F.val τ‖)
  · exact ((F.property.2.2.2.2.norm.const_mul 2).add
      (F.property.2.2.1.norm.const_mul C)).integrable_sq
  · intro n
    filter_upwards [truncatedCore_yComponent_ae n F, hFae] with τ htr hF
    rw [htr, hF]
    calc
      _ = ‖(lowProfile n τ.im * directional F.val Complex.I τ - directional F.val Complex.I τ) -
          ((τ.im : ℂ) * deriv (highProfile n) τ.im) * F.val τ‖ := by congr 1; ring
      _ ≤ ‖lowProfile n τ.im * directional F.val Complex.I τ - directional F.val Complex.I τ‖ +
          ‖((τ.im : ℂ) * deriv (highProfile n) τ.im) * F.val τ‖ := norm_sub_le _ _
      _ ≤ 2 * ‖directional F.val Complex.I τ‖ + C * ‖F.val τ‖ := by
        rw [norm_mul]
        exact add_le_add (norm_lowProfile_mul_sub_le n τ.im _)
          (mul_le_mul_of_nonneg_right (hderiv n τ.im τ.im_pos) (norm_nonneg _))
  · have hall : ∀ᵐ τ ∂modularMeasure, ∀ n : ℕ,
        yComponent (truncatedCore n F) τ = lowProfile n τ.im * directional F.val Complex.I τ -
          ((τ.im : ℂ) * deriv (highProfile n) τ.im) * F.val τ :=
      ae_all_iff.mpr (fun n => truncatedCore_yComponent_ae n F)
    filter_upwards [hall, hFae] with τ htr hF
    filter_upwards [lowProfile_eventually_value_high_deriv τ.im] with n hn
    rw [htr n, hF, hn.1, hn.2, one_mul, mul_zero, zero_mul, sub_zero]

end GapFamily.Analytic.FormTruncation
