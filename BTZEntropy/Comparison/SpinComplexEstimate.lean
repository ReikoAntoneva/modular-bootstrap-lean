import BTZEntropy.Comparison.SpinComplexPoisson
import BTZEntropy.Analytic.ContourAmplitude

/-! Uniform exponential loss for the actual noncentral complex spin sum. -/

noncomputable section

open MeasureTheory

namespace BTZEntropy

/-- A convergent lattice constant; the harmless extra one makes positivity immediate. -/
def spinComplexBoundConstant (ε : ℝ) : ℝ :=
  spinNullBound ε ^ 2 * ε ^ (-(3 / 2 : ℝ)) *
    (1 + ∑' n : ℤ, |(n : ℝ)| ^ (-(3 / 2 : ℝ)))

theorem spinComplexBoundConstant_pos {ε : ℝ} (hε : 0 < ε) :
    0 < spinComplexBoundConstant ε := by
  have hs : 0 ≤ ∑' n : ℤ, |(n : ℝ)| ^ (-(3 / 2 : ℝ)) :=
    tsum_nonneg (fun _ => Real.rpow_nonneg (abs_nonneg _) _)
  unfold spinComplexBoundConstant
  exact mul_pos (mul_pos (pow_pos (spinNullBound_pos _) _) (Real.rpow_pos_of_pos hε _))
    (by linarith)

theorem norm_complexSpinTailSum_le_uniform {a ε Y : ℝ} (ha : 0 ≤ a) (hε : 0 < ε)
    {z : ℂ} (hlo : ε ≤ z.re) (hhi : z.re ≤ Y) :
    ‖complexSpinTailSum a z‖ ≤ spinComplexBoundConstant ε *
      (Real.exp (2 * Real.pi * a / z.re) * Real.exp (-(spinImageDecayRate Y / 2) * a)) := by
  let A := spinNullBound ε ^ 2 * ε ^ (-(3 / 2 : ℝ))
  let B := Real.exp (2 * Real.pi * a / z.re) * Real.exp (-(spinImageDecayRate Y / 2) * a)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hs := Real.summable_abs_int_rpow (by norm_num : (1 : ℝ) < 3 / 2)
  have hmaj : Summable (fun n : ℤ => A * |(n : ℝ)| ^ (-(3 / 2 : ℝ)) * B) :=
    (hs.mul_left A).mul_right B
  have hterm (n : ℤ) : ‖complexSpinTail a z n‖ ≤ A * |(n : ℝ)| ^ (-(3 / 2 : ℝ)) * B := by
    by_cases hn : n = 0
    · simp [complexSpinTail, hn, A, B]
    · simpa only [complexSpinTail, ite_eq_right hn] using
        norm_complexSpinImage_le_uniform ha hε hlo hhi hn
  calc
    _ ≤ ∑' n : ℤ, ‖complexSpinTail a z n‖ :=
      norm_tsum_le_tsum_norm (summable_norm_complexSpinTail ha (hε.trans_le hlo))
    _ ≤ ∑' n : ℤ, A * |(n : ℝ)| ^ (-(3 / 2 : ℝ)) * B :=
      Summable.tsum_le_tsum hterm (summable_norm_complexSpinTail ha (hε.trans_le hlo)) hmaj
    _ = A * (∑' n : ℤ, |(n : ℝ)| ^ (-(3 / 2 : ℝ))) * B := by
      rw [tsum_mul_right, tsum_mul_left]
    _ ≤ spinComplexBoundConstant ε * B := by
      unfold spinComplexBoundConstant
      gcongr
      exact le_add_of_nonneg_left zero_le_one

/-- The physical inverse-temperature convention has a fixed gap on every compact strip. -/
theorem norm_integerSpinPrimaryComplexTransform_sub_reference_le {a βmin βmax : ℝ}
    (ha : 2 ≤ a) (hmin : 0 < βmin) {z : ℂ}
    (hlo : βmin ≤ z.re) (hhi : z.re ≤ βmax) :
    ‖integerSpinPrimaryComplexTransform a z - complexReferencePrimaryTransform a z‖ ≤
      spinComplexBoundConstant (βmin / (2 * Real.pi)) *
        (Real.exp (4 * Real.pi ^ 2 * a / z.re) *
          Real.exp (-(spinImageDecayRate (βmax / (2 * Real.pi)) / 2) * a)) := by
  have hp : 0 < 2 * Real.pi := by positivity
  have hz : 0 < z.re := hmin.trans_le hlo
  rw [integerSpinPrimaryComplexTransform_sub_reference ha hz]
  have hre : (z / (2 * (Real.pi : ℂ))).re = z.re / (2 * Real.pi) := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using Complex.div_ofReal_re z (2 * Real.pi)
  have h := norm_complexSpinTailSum_le_uniform (by linarith : 0 ≤ a)
    (div_pos hmin hp) (z := z / (2 * (Real.pi : ℂ)))
    (by rw [hre]; exact div_le_div_of_nonneg_right hlo hp.le)
    (Y := βmax / (2 * Real.pi))
    (by rw [hre]; exact div_le_div_of_nonneg_right hhi hp.le)
  convert h using 1
  rw [hre]
  congr 3
  field_simp
  ring

/-- Both descendant towers preserve the strict exponential loss of the spin correction. -/
theorem fullSpinCorrection_uniform_bound {βmin βmax : ℝ}
    (hmin : 0 < βmin) (hmax : βmin ≤ βmax) :
    ∃ C d : ℝ, 0 < C ∧ 0 < d ∧ ∀ a : ℝ, 2 ≤ a →
      ∀ β ∈ Set.Icc βmin βmax, ∀ t : ℝ,
        ‖Complex.exp (saddleContour β t / 12) *
            (complexEulerProduct (Complex.exp (-saddleContour β t)))⁻¹ ^ 2 *
              (integerSpinPrimaryComplexTransform a (saddleContour β t) -
                complexReferencePrimaryTransform a (saddleContour β t))‖ ≤
          C * Real.exp (4 * Real.pi ^ 2 * a / β) * Real.exp (-d * a) := by
  obtain ⟨D, hD, hDb⟩ := complexEulerProduct_inv_sq_bounded
    (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hmin))
  let S := spinComplexBoundConstant (βmin / (2 * Real.pi))
  let d := spinImageDecayRate (βmax / (2 * Real.pi)) / 2
  have hS : 0 < S := spinComplexBoundConstant_pos (by positivity)
  have hd : 0 < d := by
    apply div_pos _ (by norm_num)
    apply spinImageDecayRate_pos
    exact div_pos (hmin.trans_le hmax) (by positivity)
  refine ⟨Real.exp (βmax / 12) * D * S, d, by positivity, hd, ?_⟩
  intro a ha β hβ t
  have hprimary := norm_integerSpinPrimaryComplexTransform_sub_reference_le ha hmin
    (z := saddleContour β t) (by simpa using hβ.1) (by simpa using hβ.2)
  have heuler : ‖(complexEulerProduct (Complex.exp (-saddleContour β t)))⁻¹ ^ 2‖ ≤ D := by
    apply hDb
    rw [Complex.norm_exp, Complex.neg_re, saddleContour_re]
    exact Real.exp_le_exp.mpr (neg_le_neg hβ.1)
  have hshift : ‖Complex.exp (saddleContour β t / 12)‖ ≤ Real.exp (βmax / 12) := by
    rw [Complex.norm_exp, Complex.div_ofNat_re, saddleContour_re]
    exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hβ.2 (by norm_num))
  calc
    _ = ‖Complex.exp (saddleContour β t / 12)‖ *
        ‖(complexEulerProduct (Complex.exp (-saddleContour β t)))⁻¹ ^ 2‖ *
        ‖integerSpinPrimaryComplexTransform a (saddleContour β t) -
          complexReferencePrimaryTransform a (saddleContour β t)‖ := by rw [norm_mul, norm_mul]
    _ ≤ Real.exp (βmax / 12) * D *
        (S * (Real.exp (4 * Real.pi ^ 2 * a / β) * Real.exp (-d * a))) := by
      gcongr
      simpa only [saddleContour_re] using hprimary
    _ = _ := by ring

end BTZEntropy
