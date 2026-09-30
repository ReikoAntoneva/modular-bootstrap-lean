import GapFamily.Analytic.Elliptic.C1ModularTruncation

noncomputable section
namespace GapFamily.Analytic.C1ModularForm
open Set Filter MeasureTheory UpperHalfPlane ModularGradient FormTruncation
open scoped Topology ContDiff

/-- Actual invariant C1 truncations converge in the modular value L² norm. -/
theorem truncateC1_value_tendsto {F : ℂ → ℂ} (hF : ContDiffOn ℝ 1 F upperHalfPlaneSet)
    (hf : MemLp (fun τ : UpperHalfPlane => F τ) 2 modularMeasure) :
    Tendsto (fun n : ℕ => (truncateC1_memLp_value hF hf n).toLp
      (fun τ : UpperHalfPlane => truncateC1 n F τ)) atTop (𝓝 (hf.toLp (fun τ : UpperHalfPlane => F τ))) := by
  let fn := fun n => (truncateC1_memLp_value hF hf n).toLp (fun τ : UpperHalfPlane => truncateC1 n F τ)
  let f := hf.toLp (fun τ : UpperHalfPlane => F τ)
  have hn (n : ℕ) : fn n =ᵐ[modularMeasure] fun τ : UpperHalfPlane => lowProfile n τ.im * F τ :=
    (MemLp.coeFn_toLp _).trans (truncateC1_value_ae n F)
  have hfa : f =ᵐ[modularMeasure] fun τ : UpperHalfPlane => F τ := MemLp.coeFn_toLp _
  apply tendsto_L2_of_eventuallyEq_and_bound fn f (fun τ : UpperHalfPlane => 2 * ‖F τ‖)
  · exact (hf.norm.const_mul 2).integrable_sq
  · intro n
    filter_upwards [hn n, hfa] with τ hτ ha
    rw [hτ, ha]
    calc
      _ ≤ ‖lowProfile n τ.im * F τ‖ + ‖F τ‖ := norm_sub_le _ _
      _ ≤ 2 * ‖F τ‖ := by
        rw [norm_mul]
        have hb := mul_le_mul_of_nonneg_right (norm_lowProfile_le_one n τ.im) (norm_nonneg (F τ))
        nlinarith
  · have hall : ∀ᵐ τ ∂modularMeasure, ∀ n : ℕ, fn n τ = lowProfile n τ.im * F τ := ae_all_iff.mpr hn
    filter_upwards [hall, hfa] with τ hτ ha
    filter_upwards [lowProfile_eventually_value_high_deriv τ.im] with n hn
    rw [hτ n, ha, hn.1, one_mul]

/-- Every actual frame direction of the C1 truncations converges in L². -/
theorem truncateC1_directional_tendsto {F : ℂ → ℂ} (hF : ContDiffOn ℝ 1 F upperHalfPlaneSet)
    (hf : MemLp (fun τ : UpperHalfPlane => F τ) 2 modularMeasure) (v : ℂ)
    (hd : MemLp (directional F v) 2 modularMeasure) :
    Tendsto (fun n : ℕ => (truncateC1_memLp_directional hF hf v hd n).toLp (directional (truncateC1 n F) v))
      atTop (𝓝 (hd.toLp (directional F v))) := by
  let fn := fun n => (truncateC1_memLp_directional hF hf v hd n).toLp (directional (truncateC1 n F) v)
  let f := hd.toLp (directional F v)
  have hn (n : ℕ) : fn n =ᵐ[modularMeasure] directional (truncateC1 n F) v := MemLp.coeFn_toLp _
  have hfa : f =ᵐ[modularMeasure] directional F v := MemLp.coeFn_toLp _
  obtain ⟨C, hC, hb⟩ := truncateC1_directional_bound hF v
  apply tendsto_L2_of_eventuallyEq_and_bound fn f
    (fun τ : UpperHalfPlane => 2 * ‖directional F v τ‖ + C * ‖F τ‖)
  · exact ((hd.norm.const_mul 2).add (hf.norm.const_mul C)).integrable_sq
  · intro n
    filter_upwards [hn n, hfa, hb n] with τ ha hf' hbound
    rw [ha, hf']
    exact hbound.2
  · have hall : ∀ᵐ τ ∂modularMeasure, ∀ n : ℕ,
        fn n τ = lowProfile n τ.im * directional F v τ -
          (τ.im : ℂ) * (v.im • deriv (highProfile n) τ.im) * F τ :=
      ae_all_iff.mpr (fun n => (hn n).trans (truncateC1_directional_ae hF n v))
    filter_upwards [hall, hfa] with τ ha hf'
    filter_upwards [lowProfile_eventually_value_high_deriv τ.im] with n hn'
    rw [ha n, hf', hn'.1, hn'.2, one_mul, smul_zero, mul_zero, zero_mul, sub_zero]

end GapFamily.Analytic.C1ModularForm
