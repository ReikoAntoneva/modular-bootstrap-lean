import BTZEntropy.Comparison.SpinComplexPhase
import Mathlib.Analysis.Complex.SqrtDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Holomorphic spin image

The normalized modular image extends to the right half-plane using the
principal square root of `z²+n²`. That argument never meets the square-root
branch cut there. On the positive real axis this is the actual vacuum image
divided by `sqrt y`.
-/

noncomputable section

namespace BTZEntropy

/-- The holomorphic extension of the normalized denominator-one vacuum image. -/
def complexSpinImage (a : ℝ) (z : ℂ) (n : ℤ) : ℂ :=
  (Complex.sqrt (z ^ 2 + (n : ℂ) ^ 2))⁻¹ *
    Complex.exp ((2 * (Real.pi : ℂ) * (a : ℂ)) * (z / (z ^ 2 + (n : ℂ) ^ 2))) *
    (1 - Complex.exp (-2 * (Real.pi : ℂ) * (z + (n : ℂ) * Complex.I) /
      (z ^ 2 + (n : ℂ) ^ 2))) *
    (1 - Complex.exp (-2 * (Real.pi : ℂ) * (z - (n : ℂ) * Complex.I) /
      (z ^ 2 + (n : ℂ) ^ 2)))

theorem spinComplexDenominator_mem_slitPlane {z : ℂ} (hz : 0 < z.re) (n : ℤ) :
    z ^ 2 + (n : ℂ) ^ 2 ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_cases him : z.im = 0
  · left
    simp only [Complex.add_re, pow_two, Complex.mul_re, Complex.intCast_re,
      Complex.intCast_im, him, mul_zero, sub_zero]
    nlinarith [sq_nonneg (n : ℝ)]
  · right
    simp only [Complex.add_im, pow_two, Complex.mul_im, Complex.intCast_re,
      Complex.intCast_im, mul_zero, zero_mul, add_zero]
    intro he
    apply mul_ne_zero (ne_of_gt hz) him
    nlinarith

theorem spinComplexDenominator_ne_zero {z : ℂ} (hz : 0 < z.re) (n : ℤ) :
    z ^ 2 + (n : ℂ) ^ 2 ≠ 0 :=
  Complex.slitPlane_ne_zero (spinComplexDenominator_mem_slitPlane hz n)

theorem spinComplexShift_ne_zero {z : ℂ} (hz : 0 < z.re) (n : ℤ) :
    z + (n : ℂ) * Complex.I ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp at hre
  linarith

theorem analyticAt_complexSpinImage (a : ℝ) {z : ℂ} (hz : 0 < z.re) (n : ℤ) :
    AnalyticAt ℂ (fun w => complexSpinImage a w n) z := by
  have hd : AnalyticAt ℂ (fun w : ℂ => w ^ 2 + (n : ℂ) ^ 2) z := by fun_prop
  have hdn := spinComplexDenominator_ne_zero hz n
  have hs : AnalyticAt ℂ (fun w : ℂ => Complex.sqrt (w ^ 2 + (n : ℂ) ^ 2)) z :=
    hd.cpow analyticAt_const (spinComplexDenominator_mem_slitPlane hz n)
  have hsn : Complex.sqrt (z ^ 2 + (n : ℂ) ^ 2) ≠ 0 := by
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl hdn)
  unfold complexSpinImage
  exact (((hs.inv hsn).mul
    ((analyticAt_const.mul (analyticAt_id.div hd hdn)).cexp)).mul
      (analyticAt_const.sub
        ((analyticAt_const.mul (analyticAt_id.add analyticAt_const)).div hd hdn).cexp)).mul
    (analyticAt_const.sub
      ((analyticAt_const.mul (analyticAt_id.sub analyticAt_const)).div hd hdn).cexp)

theorem analyticOnNhd_complexSpinImage (a : ℝ) (n : ℤ) :
    AnalyticOnNhd ℂ (fun z => complexSpinImage a z n) {z : ℂ | 0 < z.re} :=
  fun _ hz => analyticAt_complexSpinImage a hz n

/-- The partial-fraction form exposes the two shifted chiral denominators. -/
theorem complexSpinImage_eq_reciprocal (a : ℝ) {z : ℂ} (hz : 0 < z.re) (n : ℤ) :
    complexSpinImage a z n =
      (Complex.sqrt (z ^ 2 + (n : ℂ) ^ 2))⁻¹ *
        Complex.exp ((Real.pi : ℂ) * (a : ℂ) *
          ((z + (n : ℂ) * Complex.I)⁻¹ + (z - (n : ℂ) * Complex.I)⁻¹)) *
        (1 - Complex.exp (-2 * (Real.pi : ℂ) / (z - (n : ℂ) * Complex.I))) *
        (1 - Complex.exp (-2 * (Real.pi : ℂ) / (z + (n : ℂ) * Complex.I))) := by
  have hp := spinComplexShift_ne_zero hz n
  have hm : z - (n : ℂ) * Complex.I ≠ 0 := by
    simpa only [Int.cast_neg, neg_mul, sub_eq_add_neg] using spinComplexShift_ne_zero hz (-n)
  have hprod : (z + (n : ℂ) * Complex.I) * (z - (n : ℂ) * Complex.I) =
      z ^ 2 + (n : ℂ) ^ 2 := by
    calc
      _ = z ^ 2 - (n : ℂ) ^ 2 * Complex.I ^ 2 := by ring
      _ = _ := by rw [Complex.I_sq]; ring
  have hphase := spinComplexPhase_partialFraction z (n : ℝ) hz
  simp only [Complex.ofReal_intCast] at hphase
  unfold complexSpinImage
  rw [hphase]
  congr 1
  · congr 1
    · congr 1
      congr 1
      ring
    · congr 1
      rw [← hprod]
      field_simp
  · congr 1
    rw [← hprod]
    field_simp

theorem complexSpinImage_ofReal {y : ℝ} (hy : 0 < y) (a : ℝ) (n : ℤ) :
    complexSpinImage a (y : ℂ) n = spinImageKernel a y (n : ℝ) / (Real.sqrt y : ℂ) := by
  have hs : Complex.sqrt ((y : ℂ) ^ 2 + (n : ℂ) ^ 2) =
      (Real.sqrt ((n : ℝ) ^ 2 + y ^ 2) : ℂ) := by
    have hp : 0 ≤ (n : ℝ) ^ 2 + y ^ 2 := by positivity
    have h := (Complex.ofReal_cpow hp (1 / 2 : ℝ)).symm
    simpa only [Complex.sqrt, Real.sqrt_eq_rpow, Complex.ofReal_add, Complex.ofReal_pow,
      Complex.ofReal_intCast, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat,
      one_div, add_comm, Complex.ofReal_inv] using h
  have hyne : (Real.sqrt y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr hy))
  rw [spinImageKernel_eq_exp hy]
  unfold complexSpinImage
  rw [hs]
  push_cast
  have hd : (y : ℂ) ^ 2 + (n : ℂ) ^ 2 = (n : ℂ) ^ 2 + (y : ℂ) ^ 2 := add_comm _ _
  rw [hd]
  have he : (2 * (Real.pi : ℂ) * (a : ℂ)) *
      ((y : ℂ) / ((n : ℂ) ^ 2 + (y : ℂ) ^ 2)) =
      2 * (Real.pi : ℂ) * (a : ℂ) * (y : ℂ) / ((n : ℂ) ^ 2 + (y : ℂ) ^ 2) := by ring
  rw [he]
  field_simp

/-- The central image has precisely the vacuum BTZ exponential and null square. -/
theorem complexSpinImage_zero (a : ℝ) {z : ℂ} (hz : 0 < z.re) :
    complexSpinImage a z 0 = z⁻¹ *
      Complex.exp (2 * (Real.pi : ℂ) * (a : ℂ) / z) *
        (1 - Complex.exp (-2 * (Real.pi : ℂ) / z)) ^ 2 := by
  have hzne : z ≠ 0 := by intro h; simp [h] at hz
  have hs : Complex.sqrt (z ^ 2) = z := Complex.sq_cpow_two_inv hz
  have harg : (2 * (Real.pi : ℂ) * (a : ℂ)) * (z / z ^ 2) =
      2 * (Real.pi : ℂ) * (a : ℂ) / z := by field_simp
  have hnull : -2 * (Real.pi : ℂ) * z / z ^ 2 = -2 * (Real.pi : ℂ) / z := by
    field_simp
  simp only [complexSpinImage, Int.cast_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
    add_zero, zero_mul, sub_zero, hs, harg, hnull]
  ring

theorem norm_sqrt_spinComplexDenominator (z : ℂ) (n : ℤ) :
    ‖Complex.sqrt (z ^ 2 + (n : ℂ) ^ 2)‖ = Real.sqrt ‖z ^ 2 + (n : ℂ) ^ 2‖ := by
  simpa only [Complex.sqrt, Real.sqrt_eq_rpow, one_div, Nat.cast_ofNat] using
    Complex.norm_cpow_inv_nat (z ^ 2 + (n : ℂ) ^ 2) 2

theorem norm_complexSpinImage (a : ℝ) (z : ℂ) (n : ℤ) :
    ‖complexSpinImage a z n‖ =
      (Real.sqrt ‖z ^ 2 + (n : ℂ) ^ 2‖)⁻¹ *
        Real.exp (2 * Real.pi * a * (z / (z ^ 2 + (n : ℂ) ^ 2)).re) *
        ‖1 - Complex.exp (-2 * (Real.pi : ℂ) * (z + (n : ℂ) * Complex.I) /
          (z ^ 2 + (n : ℂ) ^ 2))‖ *
        ‖1 - Complex.exp (-2 * (Real.pi : ℂ) * (z - (n : ℂ) * Complex.I) /
          (z ^ 2 + (n : ℂ) ^ 2))‖ := by
  norm_num only [complexSpinImage, norm_mul, norm_inv, norm_sqrt_spinComplexDenominator,
    Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.re_ofNat, Complex.im_ofNat, mul_zero, sub_zero, Complex.mul_im,
    zero_mul, add_zero]

end BTZEntropy
