import BTZEntropy.Analytic.ComplexDeterminant
import BTZEntropy.Analytic.ContourKernel
import BTZEntropy.Analytic.SaddleContour
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# A uniform integrable bound for the actual BTZ contour amplitude

Two vacuum null factors in the modular expression supply inverse-square
decay. The remaining Euler product is uniformly bounded on a closed subdisc.
-/

noncomputable section

open MeasureTheory

namespace BTZEntropy

theorem norm_complexDualTemperature (z : ℂ) :
    ‖complexDualTemperature z‖ = 4 * Real.pi ^ 2 / ‖z‖ := by
  simp [complexDualTemperature, norm_pow,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos]

theorem complexDualTemperature_re_nonneg {z : ℂ} (hz : 0 ≤ z.re) :
    0 ≤ (complexDualTemperature z).re := by
  have hform : complexDualTemperature z = ((4 * Real.pi ^ 2 : ℝ) : ℂ) / z := by
    simp [complexDualTemperature]
  rw [hform, Complex.div_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_div, add_zero]
  exact div_nonneg (mul_nonneg (by positivity) hz) (Complex.normSq_nonneg z)

theorem norm_one_sub_exp_neg_le (z : ℂ) :
    ‖1 - Complex.exp (-z)‖ ≤ ‖z‖ * Real.exp ‖z‖ := by
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp (-z) 1
  simpa [norm_sub_rev, norm_neg] using h

theorem complexDualBoundaryGravitonFactor_contour_bound {βmin βmax : ℝ}
    (hmin : 0 < βmin) :
    ∃ C > 0, ∀ β ∈ Set.Icc βmin βmax, ∀ t : ℝ,
      ‖complexDualBoundaryGravitonFactor (saddleContour β t)‖ ≤
        C * (βmin ^ 2 + t ^ 2)⁻¹ := by
  obtain ⟨D, hD, hDb⟩ := complexEulerProduct_inv_sq_bounded
    (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hmin))
  let A := 4 * Real.pi ^ 2
  let E := Real.exp (A / βmin)
  let F := Real.exp (βmax / 12)
  let C := A ^ 2 * E ^ 2 * (2 * Real.pi / βmin) * F * D
  have hA : 0 < A := by dsimp [A]; positivity
  have hE : 0 < E := Real.exp_pos _
  have hF : 0 < F := Real.exp_pos _
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro β hβ t
  let z := saddleContour β t
  have hzre : z.re = β := saddleContour_re β t
  have hz0 : z ≠ 0 := saddleContour_ne_zero (ne_of_gt (hmin.trans_le hβ.1)) t
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hnβ : βmin ≤ ‖z‖ := hβ.1.trans (by
    rw [← hzre]
    exact Complex.re_le_norm z)
  have hnormdual : ‖complexDualTemperature z‖ = A / ‖z‖ := norm_complexDualTemperature z
  have hdual : ‖complexDualTemperature z‖ ≤ A / βmin := by
    rw [hnormdual]
    exact div_le_div_of_nonneg_left hA.le hmin hnβ
  rw [hnormdual] at hdual
  have hnull : ‖1 - Complex.exp (-complexDualTemperature z)‖ ≤ A / ‖z‖ * E := by
    calc
      _ ≤ ‖complexDualTemperature z‖ * Real.exp ‖complexDualTemperature z‖ :=
        norm_one_sub_exp_neg_le _
      _ ≤ A / ‖z‖ * E := by
        rw [hnormdual]
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hdual) (by positivity)
  have hrat : ‖2 * (Real.pi : ℂ) / z‖ ≤ 2 * Real.pi / βmin := by
    norm_num only [norm_div, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_ofNat]
    exact div_le_div_of_nonneg_left (by positivity) hmin hnβ
  have hmod : ‖Complex.exp ((z - complexDualTemperature z) / 12)‖ ≤ F := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hdualre := complexDualTemperature_re_nonneg (z := z) (by rw [hzre]; linarith [hβ.1])
    simp only [Complex.div_ofNat_re, Complex.sub_re, hzre]
    linarith [hβ.2]
  have heuler : ‖(complexEulerProduct (Complex.exp (-z)))⁻¹ ^ 2‖ ≤ D := by
    apply hDb
    rw [Complex.norm_exp, Complex.neg_re, hzre]
    exact Real.exp_le_exp.mpr (neg_le_neg hβ.1)
  have hsq : ‖z‖ ^ 2 = β ^ 2 + t ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    exact saddleContour_normSq β t
  have hden : 0 < βmin ^ 2 + t ^ 2 := by positivity
  have hdenle : βmin ^ 2 + t ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [hsq]
    nlinarith [hβ.1]
  calc
    ‖complexDualBoundaryGravitonFactor z‖ =
        ‖1 - Complex.exp (-complexDualTemperature z)‖ ^ 2 *
          ‖2 * (Real.pi : ℂ) / z‖ *
          ‖Complex.exp ((z - complexDualTemperature z) / 12)‖ *
          ‖(complexEulerProduct (Complex.exp (-z)))⁻¹ ^ 2‖ := by
      simp only [complexDualBoundaryGravitonFactor, norm_mul, norm_pow]
    _ ≤ (A / ‖z‖ * E) ^ 2 * (2 * Real.pi / βmin) * F * D := by
      gcongr
    _ = C / ‖z‖ ^ 2 := by dsimp [C]; ring
    _ ≤ C / (βmin ^ 2 + t ^ 2) := div_le_div_of_nonneg_left hC.le hden hdenle
    _ = C * (βmin ^ 2 + t ^ 2)⁻¹ := div_eq_mul_inv _ _

theorem continuous_complexAmplitude_contour (φ : SmoothKernel) {β : ℝ} (hβ : 0 < β) :
    Continuous (fun t : ℝ => complexAmplitude φ (saddleContour β t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply (analyticAt_complexAmplitude φ (by simpa using hβ)).continuousAt.comp
  unfold saddleContour
  fun_prop

theorem complexAmplitude_contour_bound (φ : SmoothKernel) {βmin βmax : ℝ}
    (hmin : 0 < βmin) :
    ∃ C > 0, ∀ β ∈ Set.Icc βmin βmax, ∀ t : ℝ,
      ‖complexAmplitude φ (saddleContour β t)‖ ≤ C * (βmin ^ 2 + t ^ 2)⁻¹ := by
  obtain ⟨D, hD, hbD⟩ := complexDualBoundaryGravitonFactor_contour_bound
    (βmax := βmax) hmin
  obtain ⟨K, hK, hbK⟩ := complexKernelTransform_contour_bounded φ βmin βmax
  refine ⟨K * D, mul_pos hK hD, ?_⟩
  intro β hβ t
  rw [complexAmplitude, norm_mul]
  calc
    _ ≤ K * (D * (βmin ^ 2 + t ^ 2)⁻¹) :=
      mul_le_mul (hbK β hβ t) (hbD β hβ t) (norm_nonneg _) hK.le
    _ = _ := (mul_assoc _ _ _).symm

theorem integrable_complexAmplitude_contour (φ : SmoothKernel) {β : ℝ} (hβ : 0 < β) :
    Integrable (fun t : ℝ => complexAmplitude φ (saddleContour β t)) := by
  obtain ⟨C, hC, hb⟩ := complexAmplitude_contour_bound φ (βmax := β) hβ
  exact ((integrable_contour_majorant hβ).const_mul C).mono'
    (continuous_complexAmplitude_contour φ hβ).aestronglyMeasurable
    (Filter.Eventually.of_forall (hb β ⟨le_rfl, le_rfl⟩))

theorem complexAmplitude_contour_integral_bounded (φ : SmoothKernel) {βmin βmax : ℝ}
    (hmin : 0 < βmin) :
    ∃ M > 0, ∀ β ∈ Set.Icc βmin βmax,
      (∫ t : ℝ, ‖complexAmplitude φ (saddleContour β t)‖) ≤ M := by
  obtain ⟨C, hC, hb⟩ := complexAmplitude_contour_bound φ (βmax := βmax) hmin
  have hI : 0 ≤ ∫ t : ℝ, (βmin ^ 2 + t ^ 2)⁻¹ :=
    integral_nonneg (fun t => inv_nonneg.mpr (by positivity))
  refine ⟨C * (∫ t : ℝ, (βmin ^ 2 + t ^ 2)⁻¹) + 1, by positivity, ?_⟩
  intro β hβ
  calc
    _ ≤ ∫ t : ℝ, C * (βmin ^ 2 + t ^ 2)⁻¹ :=
      integral_mono_ae (integrable_complexAmplitude_contour φ (hmin.trans_le hβ.1)).norm
        ((integrable_contour_majorant hmin).const_mul C)
        (Filter.Eventually.of_forall (hb β hβ))
    _ = C * (∫ t : ℝ, (βmin ^ 2 + t ^ 2)⁻¹) := integral_const_mul _ _
    _ ≤ _ := le_add_of_nonneg_right zero_le_one

/-- The actual nonlocal contour contributes less than every prescribed inverse
power, uniformly over a positive compact interval of energy ratios. -/
theorem actualContour_tail_uniform (φ : SmoothKernel) {L U ε : ℝ}
    (hL : 0 < L) (hLU : L ≤ U) (hε : 0 < ε) (N : ℕ) :
    ∃ C > 0, ∀ x ∈ Set.Icc L U, ∀ c : ℝ, 0 < c →
      ‖∫ t in {t : ℝ | ε ≤ |t|},
        complexAmplitude φ (saddleContour (saddleBeta x) t) *
          normalizedSaddleExponential x c t‖ ≤ C / c ^ N := by
  have hU : 0 < U := hL.trans_le hLU
  obtain ⟨M, hM, hbM⟩ := complexAmplitude_contour_integral_bounded φ
    (βmax := saddleBeta L) (saddleBeta_pos hU)
  have hη := contourLoss_pos hL hε
  let C := ((N.factorial : ℝ) / contourLoss L ε ^ N) * M
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro x hx c hc
  calc
    _ ≤ ((N.factorial : ℝ) / contourLoss L ε ^ N) *
        (∫ t : ℝ, ‖complexAmplitude φ (saddleContour (saddleBeta x) t)‖) / c ^ N :=
      norm_integral_mul_normalizedSaddleExponential_outside_pow hL hx hc hε
        (integrable_complexAmplitude_contour φ (saddleBeta_pos (hL.trans_le hx.1))) N
    _ ≤ C / c ^ N := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg hc.le N)
      exact mul_le_mul_of_nonneg_left (hbM _ (saddleBeta_mem_Icc hL hx)) (by positivity)

end BTZEntropy
