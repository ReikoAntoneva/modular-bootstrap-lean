import GapFamily.Analytic.Spatial.SpatialOrbitSummable
import GapFamily.Analytic.Poincare.Fourier.PoincareFourierIntegral
import Mathlib.Analysis.Fourier.PoissonSummation

/-! Ordinary horizontal periodization of the actual point kernel on `Re s > 1`.
The translation series converges normally on compact horizontal intervals and
its integer Fourier coefficient is the ordinary real-line Fourier transform.
-/

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open Set MeasureTheory PoincareFourier UpperHalfPlane Matrix TopologicalSpace
open scoped MatrixGroups FourierTransform

def pointHorizontalKernel (s : ℂ) (y : ℝ) (hy : 0 < y) (w : UpperHalfPlane) : C(ℝ, ℂ) :=
  ⟨fun x => pointKernel s (rowPoint y hy x) w,
    (continuous_pointKernel_left s w).comp (continuous_rowPoint y hy)⟩

private theorem T_zpow_injective : Function.Injective (fun n : ℤ => ModularGroup.T ^ n) := by
  intro n m h
  have he := congrArg (fun g : SL(2, ℤ) => g 0 1) h
  simpa [ModularGroup.coe_T_zpow] using he

theorem summable_norm_pointHorizontalKernel (s : ℂ) (hs : 1 < s.re)
    (y : ℝ) (hy : 0 < y) (w : UpperHalfPlane) :
    Summable (fun n : ℤ => ‖pointHorizontalKernel s y hy w n‖) := by
  have hf := (summable_norm_spatialOrbit s hs w (rowPoint y hy 0)).comp_injective
    T_zpow_injective
  have he (n : ℤ) : ModularGroup.T ^ n • rowPoint y hy 0 = rowPoint y hy n := by
    apply UpperHalfPlane.ext
    rw [ModularGroup.coe_T_zpow_smul_eq]
    apply Complex.ext <;> simp [rowPoint]
  simpa only [Function.comp_def, he, pointKernel_symm, pointHorizontalKernel,
    ContinuousMap.coe_mk] using hf

private theorem pointParameter_horizontal (y : ℝ) (hy : 0 < y)
    (w : UpperHalfPlane) (x : ℝ) :
    pointParameter (rowPoint y hy x) w =
      ((x - w.re) ^ 2 + (y + w.im) ^ 2) / (4 * y * w.im) := by
  rw [pointParameter_eq_normSq_sub_conj (rowPoint y hy x).im_pos w.im_pos]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.conj_re,
    Complex.conj_im, sub_neg_eq_add]
  change ((x - w.re) * (x - w.re) + (y + w.im) * (y + w.im)) / (4 * y * w.im) = _
  ring

private theorem pointParameter_horizontal_shift_le (y : ℝ) (hy : 0 < y)
    (w : UpperHalfPlane) (R x a : ℝ) (hx : |x| ≤ R) :
    pointParameter (rowPoint y hy a) w ≤
      (2 + 2 * R ^ 2 / (y + w.im) ^ 2) *
        pointParameter (rowPoint y hy (x + a)) w := by
  rw [pointParameter_horizontal, pointParameter_horizontal, ← mul_div_assoc]
  apply (div_le_div_iff_of_pos_right (by positivity : 0 < 4 * y * w.im)).mpr
  have hb : 0 < (y + w.im) ^ 2 := sq_pos_of_pos (by positivity)
  have hx2 : x ^ 2 ≤ R ^ 2 := by nlinarith [sq_abs x, abs_nonneg x]
  have hc : 0 ≤ 2 * R ^ 2 / (y + w.im) ^ 2 := by positivity
  have hbase : (a - w.re) ^ 2 ≤ 2 * (x + a - w.re) ^ 2 + 2 * R ^ 2 := by
    nlinarith [sq_nonneg (a - w.re + 2 * x)]
  have hid : (2 * R ^ 2 / (y + w.im) ^ 2) * (y + w.im) ^ 2 = 2 * R ^ 2 :=
    div_mul_cancel₀ _ hb.ne'
  nlinarith [mul_nonneg hc (sq_nonneg (x + a - w.re))]

private theorem pointKernel_norm_le_of_parameter_le (s : ℂ) (hs : 0 ≤ s.re)
    (z z' w : UpperHalfPlane) (C : ℝ) (hC : 0 < C)
    (hp : pointParameter z w ≤ C * pointParameter z' w) :
    ‖pointKernel s z' w‖ ≤ C ^ s.re * ‖pointKernel s z w‖ := by
  simp only [norm_pointKernel_eq_realPart s, norm_pointKernel_real_exponent]
  have hq : pointParameter z w / C ≤ pointParameter z' w :=
    (div_le_iff₀ hC).mpr (by simpa only [mul_comm] using hp)
  have hr := Real.rpow_le_rpow_of_nonpos
    (div_pos (pointParameter_pos z.im_pos w.im_pos) hC) hq (neg_nonpos.mpr hs)
  rw [Real.div_rpow (pointParameter_pos z.im_pos w.im_pos).le hC.le,
    Real.rpow_neg hC.le s.re, div_inv_eq_mul] at hr
  calc
    _ ≤ (1 / 4 : ℝ) * (pointParameter z w ^ (-s.re) * C ^ s.re) :=
      mul_le_mul_of_nonneg_left hr (by norm_num)
    _ = _ := by ring

/-- Horizontal source motion has a bound independent of the other point.
This uniformity permits subsequent summation over every cusp coset. -/
theorem pointKernel_horizontal_shift_norm_le (s : ℂ) (hs : 0 ≤ s.re)
    (y : ℝ) (hy : 0 < y) (w : UpperHalfPlane) (R x a : ℝ) (hx : |x| ≤ R) :
    ‖pointKernel s (rowPoint y hy (x + a)) w‖ ≤
      (2 + 2 * R ^ 2 / y ^ 2) ^ s.re * ‖pointKernel s (rowPoint y hy a) w‖ := by
  have hC : 0 < 2 + 2 * R ^ 2 / y ^ 2 := by positivity
  apply pointKernel_norm_le_of_parameter_le s hs _ _ _ _ hC
  apply (pointParameter_horizontal_shift_le y hy w R x a hx).trans
  apply mul_le_mul_of_nonneg_right _ (pointParameter_pos (rowPoint y hy (x + a)).im_pos w.im_pos).le
  apply add_le_add le_rfl
  apply div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hy)
  nlinarith [w.im_pos]

/-- The integer translation series has a summable compact-supremum majorant.
The comparison constant is explicit and independent of the translation index.
-/
theorem summable_norm_pointHorizontalKernel_restrict (s : ℂ) (hs : 1 < s.re)
    (y : ℝ) (hy : 0 < y) (w : UpperHalfPlane) (K : Compacts ℝ) :
    Summable (fun n : ℤ =>
      ‖((pointHorizontalKernel s y hy w).comp (ContinuousMap.addRight n)).restrict K‖) := by
  obtain ⟨R, hR⟩ := K.isCompact.isBounded.subset_closedBall 0
  let C : ℝ := 2 + 2 * R ^ 2 / (y + w.im) ^ 2
  have hC : 0 < C := by dsimp [C]; positivity
  apply ((summable_norm_pointHorizontalKernel s hs y hy w).mul_left (C ^ s.re)).of_nonneg_of_le
    (fun n => norm_nonneg _)
  intro n
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro x
  have hx : |(x : ℝ)| ≤ R := by
    simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero] using hR x.property
  exact pointKernel_norm_le_of_parameter_le s (by linarith) (rowPoint y hy n)
    (rowPoint y hy ((x : ℝ) + n)) w C hC
    (pointParameter_horizontal_shift_le y hy w R x n hx)

/-- The point kernel along a complete horizontal line is ordinarily integrable
in the original convergence half-plane. -/
theorem integrable_pointHorizontalKernel (s : ℂ) (hs : 1 < s.re)
    (y : ℝ) (hy : 0 < y) (w : UpperHalfPlane) :
    Integrable (pointHorizontalKernel s y hy w : ℝ → ℂ) :=
  Real.integrable_of_summable_norm_Icc
    (summable_norm_pointHorizontalKernel_restrict s hs y hy w ⟨Icc 0 1, isCompact_Icc⟩)

/-- Horizontal integer Fourier projection of the actual normally convergent
translation sum unfolds to the ordinary point-kernel Fourier integral. -/
theorem fourierCoeff_pointHorizontalKernel_periodization (s : ℂ) (hs : 1 < s.re)
    (y : ℝ) (hy : 0 < y) (w : UpperHalfPlane) (J : ℤ) :
    fourierCoeff (Function.Periodic.lift
      ((pointHorizontalKernel s y hy w).periodic_tsum_comp_add_zsmul 1)) J =
      𝓕 (pointHorizontalKernel s y hy w : ℝ → ℂ) J :=
  Real.fourierCoeff_tsum_comp_add
    (summable_norm_pointHorizontalKernel_restrict s hs y hy w) J

theorem pointHorizontalKernel_periodization_fourier_integral (s : ℂ) (hs : 1 < s.re)
    (y : ℝ) (hy : 0 < y) (w : UpperHalfPlane) (J : ℤ) :
    (∫ x : ℝ in 0..1, cuspFourierMode (-J) x *
      ∑' n : ℤ, pointKernel s (rowPoint y hy (x + n)) w) =
      ∫ x : ℝ, cuspFourierMode (-J) x * pointKernel s (rowPoint y hy x) w := by
  let f := pointHorizontalKernel s y hy w
  have hnorm := summable_norm_pointHorizontalKernel_restrict s hs y hy w
  have hsum := ContinuousMap.summable_of_locally_summable_norm hnorm
  have hf := fourierCoeff_pointHorizontalKernel_periodization s hs y hy w J
  rw [fourierCoeff_eq_intervalIntegral _ J 0] at hf
  simp only [one_div, inv_one, one_smul, zero_add, smul_eq_mul] at hf
  have hchar (m : ℤ) (x : ℝ) : fourier m (x : UnitAddCircle) = cuspFourierMode m x := by
    rw [fourier_coe_apply]
    simp [cuspFourierMode]
  have hlift (x : ℝ) :
      (f.periodic_tsum_comp_add_zsmul 1).lift (x : UnitAddCircle) =
        ∑' n : ℤ, pointKernel s (rowPoint y hy (x + n)) w := by
    rw [Function.Periodic.lift_coe]
    simp only [zsmul_one]
    rw [← ContinuousMap.tsum_apply hsum]
    rfl
  simp_rw [hchar, hlift] at hf
  rw [hf, Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    simp only [smul_eq_mul, pointHorizontalKernel, ContinuousMap.coe_mk, cuspFourierMode]
    congr 2
    push_cast
    ring

theorem pointKernel_translation_periodization_swap (s : ℂ) (z : UpperHalfPlane)
    (y : ℝ) (hy : 0 < y) (x : ℝ) :
    (∑' n : ℤ, pointKernel s (ModularGroup.T ^ n • z : UpperHalfPlane) (rowPoint y hy x)) =
      ∑' n : ℤ, pointKernel s (rowPoint y hy (x + n)) z := by
  have ht (n : ℤ) : ModularGroup.T ^ n • rowPoint y hy x = rowPoint y hy (x + n) := by
    apply UpperHalfPlane.ext
    rw [ModularGroup.coe_T_zpow_smul_eq]
    apply Complex.ext <;> simp [rowPoint]
  calc
    _ = ∑' n : ℤ, pointKernel s (ModularGroup.T ^ (-n) • rowPoint y hy x : UpperHalfPlane) z := by
      apply tsum_congr
      intro n
      rw [pointKernel_modular_move, ← _root_.zpow_neg, pointKernel_symm]
    _ = ∑' n : ℤ, pointKernel s (ModularGroup.T ^ n • rowPoint y hy x : UpperHalfPlane) z :=
      (Equiv.neg ℤ).tsum_eq (fun n : ℤ =>
        pointKernel s (ModularGroup.T ^ n • rowPoint y hy x : UpperHalfPlane) z)
    _ = _ := by simp_rw [ht]

/-- Fourier projection in the source coordinate has the positive phase needed
for the actual Poincaré input spin after cusp regrouping. -/
theorem pointKernel_translation_source_fourier_integral (s : ℂ) (hs : 1 < s.re)
    (z : UpperHalfPlane) (y : ℝ) (hy : 0 < y) (J : ℤ) :
    (∫ x : ℝ in 0..1, cuspFourierMode J x *
      ∑' n : ℤ, pointKernel s (ModularGroup.T ^ n • z : UpperHalfPlane) (rowPoint y hy x)) =
      ∫ x : ℝ, cuspFourierMode J x * pointKernel s (rowPoint y hy x) z := by
  simp_rw [pointKernel_translation_periodization_swap]
  simpa only [neg_neg] using
    pointHorizontalKernel_periodization_fourier_integral s hs y hy z (-J)

end GapFamily.Analytic.SpatialPoint
