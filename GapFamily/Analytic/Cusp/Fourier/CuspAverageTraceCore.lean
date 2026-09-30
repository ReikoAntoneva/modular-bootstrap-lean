import GapFamily.Analytic.Cusp.Fourier.CuspAverageTraceSlice
import GapFamily.Analytic.Cusp.Fourier.CuspAverageTraceIntegral
import GapFamily.Analytic.Cusp.Profile.CuspCollarIntegral
import GapFamily.Analytic.Cusp.Fourier.CuspHorizontalHilbert
import GapFamily.Analytic.Modular.Elliptic.ModularInteriorCompactCore

/-!
# The actual smooth cusp-average boundary trace

The value at height one is the ordinary width-one horizontal integral. Local
vertical trace estimates and genuine collar energy bounds prove its continuity
in the actual mass-plus-gradient norm. A shrinking-collar mean approximates
this trace with an explicit gradient-energy error.
-/

noncomputable section
namespace GapFamily.Analytic

open Set MeasureTheory ModularGradient UpperHalfPlane

/-- The literal horizontal boundary average on genuine smooth automorphic
core functions. -/
def cuspAverageTraceCore : smoothCore →ₗ[ℂ] ℂ where
  toFun F := cuspHorizontalAverage F.val 1
  map_add' F G := cuspHorizontalAverage_core_add F G zero_lt_one
  map_smul' c F := cuspHorizontalAverage_core_smul c F 1

@[simp] theorem cuspAverageTraceCore_apply (F : smoothCore) :
    cuspAverageTraceCore F = cuspHorizontalAverage F.val 1 := rfl

theorem cuspAverageTraceCore_norm_sq_le (F : smoothCore) :
    ‖cuspAverageTraceCore F‖^2 ≤ 8 * ‖value F‖^2 + 2 * ‖coreGradient F‖^2 := by
  have hval : Continuous (fun x : ℝ =>
      ∫ y in (1 : ℝ)..(1 + 1), ‖F.val (Complex.mk x y)‖^2) :=
    continuous_cuspVerticalIntegral (F.property.1.continuousOn.norm.pow 2) zero_le_one
  have hder : ContinuousOn (fun z => ‖fderiv ℝ F.val z Complex.I‖^2)
      upperHalfPlaneSet :=
    ((F.property.1.continuousOn_fderiv_of_isOpen isOpen_upperHalfPlaneSet (by simp)).clm_apply
      continuousOn_const).norm.pow 2
  have hderi := continuous_cuspVerticalIntegral hder zero_le_one
  have hrow := (contDiff_cuspHorizontalSlice F.property.1 zero_lt_one).continuous
  have hm := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (-1/2 : ℝ) ≤ 1/2)
    ((hrow.norm.pow 2).intervalIntegrable (-1/2) (1/2))
    (((hval.const_mul 2).add (hderi.const_mul 2)).intervalIntegrable (-1/2) (1/2))
    (fun x _ => by simpa [cuspHorizontalSlice] using
      cusp_vertical_trace_sq_le F x (show (0 : ℝ) < 1 from zero_lt_one))
  simp only [Pi.add_apply, Pi.pow_apply] at hm
  rw [intervalIntegral.integral_add (μ := volume)
      ((hval.const_mul 2).intervalIntegrable _ _) ((hderi.const_mul 2).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hm
  have hv := cuspCollar_iterated_value_energy_le F zero_le_one le_rfl
  have hd := cuspCollar_iterated_vertical_energy_le F zero_le_one
  have hj := cuspHorizontalAverage_row_jensen F zero_lt_one
  change ‖cuspAverageTraceCore F‖^2 ≤ _ at hj
  linarith

/-- A convenient rational norm bound for extension to the actual completed
form domain. -/
theorem cuspAverageTraceCore_norm_le (F : smoothCore) :
    ‖cuspAverageTraceCore F‖ ≤ 4 * ‖coreForm F‖ := by
  have h := cuspAverageTraceCore_norm_sq_le F
  have heq := coreForm_norm_sq F
  nlinarith [sq_nonneg ‖value F‖, sq_nonneg ‖coreGradient F‖,
    norm_nonneg (cuspAverageTraceCore F), norm_nonneg (coreForm F)]

/-- The actual trace is approximated by the ordinary mean of the actual
horizontal averages over a shrinking positive collar. -/
theorem cuspAverageTraceCore_mean_error_sq_le (F : smoothCore) {ε : ℝ} (hε : 0 < ε) :
    ‖cuspAverageTraceCore F - ε⁻¹ •
      (∫ y in (1 : ℝ)..(1 + ε), cuspHorizontalAverage F.val y)‖^2 ≤
        ε * ‖coreGradient F‖^2 := by
  let e : ℝ → ℂ := fun x => F.val (Complex.mk x 1) -
    ε⁻¹ • (∫ y in (1 : ℝ)..(1 + ε), F.val (Complex.mk x y))
  have hval := continuous_cuspVerticalIntegral F.property.1.continuousOn hε.le
  have hrow : Continuous (fun x : ℝ => F.val (Complex.mk x 1)) :=
    (contDiff_cuspHorizontalSlice F.property.1 zero_lt_one).continuous
  have he : Continuous e := hrow.sub (hval.const_smul ε⁻¹)
  have hder : ContinuousOn (fun z => ‖fderiv ℝ F.val z Complex.I‖^2)
      upperHalfPlaneSet :=
    ((F.property.1.continuousOn_fderiv_of_isOpen isOpen_upperHalfPlaneSet (by simp)).clm_apply
      continuousOn_const).norm.pow 2
  have hderi := continuous_cuspVerticalIntegral hder hε.le
  have hm := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (-1/2 : ℝ) ≤ 1/2)
    ((he.norm.pow 2).intervalIntegrable (-1/2) (1/2))
    ((hderi.const_mul ε).intervalIntegrable (-1/2) (1/2))
    (fun x _ => cusp_vertical_mean_error_sq_le F x hε)
  rw [intervalIntegral.integral_const_mul] at hm
  have hj := cusp_horizontal_integral_sq_le he
  have heq : (∫ x in (-1/2 : ℝ)..(1/2), e x) =
      cuspAverageTraceCore F - ε⁻¹ •
        (∫ y in (1 : ℝ)..(1 + ε), cuspHorizontalAverage F.val y) := by
    have hi : IntervalIntegrable (fun x : ℝ => ε⁻¹ •
        (∫ y in (1 : ℝ)..(1 + ε), F.val (Complex.mk x y))) volume (-1/2) (1/2) :=
      (hval.const_smul ε⁻¹).intervalIntegrable _ _
    change (∫ x in (-1/2 : ℝ)..(1/2), F.val (Complex.mk x 1) -
      ε⁻¹ • (∫ y in (1 : ℝ)..(1 + ε), F.val (Complex.mk x y))) = _
    rw [intervalIntegral.integral_sub (hrow.intervalIntegrable _ _) hi,
      intervalIntegral.integral_smul,
      cuspCollar_integral_swap F.val F.property.1.continuousOn hε.le]
    rfl
  rw [heq] at hj
  exact hj.trans (hm.trans (mul_le_mul_of_nonneg_left
    (cuspCollar_iterated_vertical_energy_le F hε.le) hε.le))

end GapFamily.Analytic
