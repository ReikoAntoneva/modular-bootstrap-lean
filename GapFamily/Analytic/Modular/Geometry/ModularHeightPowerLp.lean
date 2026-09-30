import GapFamily.Analytic.Cusp.Profile.CuspHalfLineSourceMeasure
import GapFamily.Analytic.Modular.ModularHilbert
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
Actual modular L² membership of positive cusp-height powers below the critical
exponent one half, and multiplication by an actually bounded measurable function.
-/

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open Set Filter MeasureTheory UpperHalfPlane
open scoped ENNReal

private theorem memLp_modularHeightPower_high (α : ℝ) (hhalf : α < 1 / 2) :
    MemLp (fun τ : UpperHalfPlane =>
      if 1 < τ.im then ((τ.im ^ α : ℝ) : ℂ) else 0) 2 modularMeasure := by
  have hb : Measurable (fun y : ℝ => ((y ^ α : ℝ) : ℂ)) := by fun_prop
  have hm : Measurable (fun τ : UpperHalfPlane =>
      if 1 < τ.im then ((τ.im ^ α : ℝ) : ℂ) else 0) :=
    (hb.comp UpperHalfPlane.continuous_im.measurable).ite
      (measurableSet_highCusp 1) measurable_const
  rw [memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable,
    ← lintegral_ofReal_ne_top_iff_integrable (hm.norm.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun _ => sq_nonneg _),
    CuspHalfLineSource.lintegral_clippedProfile_norm_sq _ hb]
  have hi : IntegrableOn (fun y : ℝ => y ^ (2 * α - 2)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  have heq : (∫⁻ y : ℝ in Ioi 1,
      ENNReal.ofReal (‖((y ^ α : ℝ) : ℂ)‖ ^ 2 / y ^ 2)) =
      ∫⁻ y : ℝ in Ioi 1, ENNReal.ofReal (y ^ (2 * α - 2)) := by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro y hy
    dsimp only
    congr 1
    have hy0 : 0 < y := zero_lt_one.trans hy
    have hsquare : (y ^ α) ^ (2 : ℕ) = y ^ (2 * α) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hy0.le]
      congr 1
      ring
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, hsquare,
      ← Real.rpow_sub_natCast hy0.ne']
    norm_num
  rw [heq]
  apply (lintegral_ofReal_ne_top_iff_integrable hi.aestronglyMeasurable ?_).mpr hi
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  exact Real.rpow_nonneg (zero_lt_one.trans hy).le _

/-- The literal height power is genuinely square integrable for 0≤α<1/2. -/
theorem memLp_modularHeightPower (α : ℝ) (hα : 0 ≤ α) (hhalf : α < 1 / 2) :
    MemLp (fun τ : UpperHalfPlane => ((τ.im ^ α : ℝ) : ℂ)) 2 modularMeasure := by
  have hlo : MemLp (fun τ : UpperHalfPlane =>
      if 1 < τ.im then (0 : ℂ) else ((τ.im ^ α : ℝ) : ℂ)) 2 modularMeasure := by
    have hm : Measurable (fun τ : UpperHalfPlane =>
        if 1 < τ.im then (0 : ℂ) else ((τ.im ^ α : ℝ) : ℂ)) :=
      measurable_const.ite (measurableSet_highCusp 1) (by fun_prop)
    apply MemLp.of_bound hm.aestronglyMeasurable 1
    apply Eventually.of_forall
    intro τ
    by_cases hy : 1 < τ.im
    · simp only [ite_eq_left hy, norm_zero]
      norm_num
    · rw [ite_eq_right hy, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg τ.im_pos.le _)]
      exact Real.rpow_le_one τ.im_pos.le (le_of_not_gt hy) hα
  have hsum := (memLp_modularHeightPower_high α hhalf).add hlo
  convert hsum using 1
  ext τ
  by_cases hy : 1 < τ.im <;> simp [hy]

/-- Multiplication by an actual bounded measurable function preserves this weighted L² membership. -/
theorem memLp_modularHeightPower_mul_of_bound (α : ℝ) (hα : 0 ≤ α)
    (hhalf : α < 1 / 2) {f : UpperHalfPlane → ℂ} {C : ℝ}
    (hf : AEStronglyMeasurable f modularMeasure)
    (hbound : ∀ᵐ τ ∂modularMeasure, ‖f τ‖ ≤ C) :
    MemLp (fun τ => ((τ.im ^ α : ℝ) : ℂ) * f τ) 2 modularMeasure := by
  have hp := memLp_modularHeightPower α hα hhalf
  apply hp.of_le_mul (c := C) (hp.aestronglyMeasurable.mul hf)
  filter_upwards [hbound] with τ hτ
  change ‖((τ.im ^ α : ℝ) : ℂ) * f τ‖ ≤ C * ‖((τ.im ^ α : ℝ) : ℂ)‖
  rw [norm_mul, mul_comm C]
  exact mul_le_mul_of_nonneg_left hτ (norm_nonneg _)

end GapFamily.Analytic.SpatialPoint
