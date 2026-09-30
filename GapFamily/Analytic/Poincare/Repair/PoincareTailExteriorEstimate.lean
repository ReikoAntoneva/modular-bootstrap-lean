import GapFamily.Analytic.Poincare.Repair.PoincareExteriorEstimate
import GapFamily.Analytic.Poincare.Repair.PoincareExteriorCellBound
import GapFamily.Analytic.Foundation.GeometricMomentDecay

/-! The actual short-cell exterior estimate. A unit complex radius applies
to every physical cell of length at most one, at arbitrary energy. Its
uniform dyadic gain is independent of the later small charge ratio.
-/

noncomputable section

open Set MeasureTheory Real

namespace GapFamily.Analytic

def canonicalRepairCellCoefficient : ℝ := centralKernelBound + 96 * π ^ 2 + 25

theorem canonicalRepairCellCoefficient_pos : 0 < canonicalRepairCellCoefficient := by
  have := centralKernelBound_pos
  unfold canonicalRepairCellCoefficient
  positivity

/-- C2's actual short-cell estimate, with fixed polynomial degree two and
the explicit output growth constant `4π`, at every unbounded exterior energy. -/
theorem norm_signedIntegral_canonicalRepairKernelEnergy_shortCell
    (B : ℝ) (hB : 1 ≤ B) (j jin : ℤ) (e : ℝ)
    (he : |(j : ℝ)| ≤ e) (hBe : B ≤ e)
    (ν : SignedMeasure ℝ) (L V : ℝ) (k : ℕ)
    (hL : |(jin : ℝ)| ≤ L) (hLV : L ≤ V) (hVB : V ≤ B) (hshort : V - L ≤ 1)
    (hν : ∀ᵐ E ∂ν.variation, E ∈ Icc L V)
    (hm : ∀ n ≤ k, (∫ᵛ x : ℝ, x ^ n ∂<•signedSqrtCoordinate jin ν) = 0) :
    ‖∫ᵛ E, canonicalRepairKernelEnergy B hB j jin e E ∂<•ν‖ ≤
      canonicalRepairCellCoefficient * ν.totalVariation.real univ * (1 + B + e) ^ 2 *
        exp (canonicalRepairKernelExponent * B + 4 * π * sqrt e - (k : ℝ) * log 2) := by
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have he0 : 0 ≤ e := hB0.trans hBe
  have hθ := sqrtInputWidth_half_mem_Icc jin L V hL hLV hshort
  have hgeom := geometricMomentRemainder_le_exp
    (sqrtInputWidth jin L V / 2) hθ.1 hθ.2 k
  have hpoly := inputColumnStripPolynomial_sqrtInputCenter_le B hB jin L V hL hLV hVB
  have hp0 := (inputColumnStripPolynomial_pos jin (|sqrtInputCenter jin L V| + 1)
    (by positivity)).le
  have hC0 := canonicalRepairCellCoefficient_pos.le
  have hbase := norm_signedIntegral_canonicalRepairKernelEnergy_le_exp B hB j jin e he hBe
    ν L V 1 k hL hLV (by norm_num)
    (by simpa only [mul_one] using hθ.2.trans_lt (by norm_num : (1 / 2 : ℝ) < 1)) hν hm
  simp only [mul_one] at hbase
  calc
    _ ≤ ν.totalVariation.real univ * e *
        inputColumnStripPolynomial jin (|sqrtInputCenter jin L V| + 1) *
          exp (canonicalRepairKernelExponent * B + 4 * π * sqrt e) *
            ((sqrtInputWidth jin L V / 2) ^ (k + 1) /
              (1 - sqrtInputWidth jin L V / 2)) := by
      simpa only [mul_div_assoc] using hbase
    _ ≤ (ν.totalVariation.real univ * e * (canonicalRepairCellCoefficient * B) *
        exp (canonicalRepairKernelExponent * B + 4 * π * sqrt e)) *
          exp (-(k : ℝ) * log 2) := by
      have hcoeff : ν.totalVariation.real univ * e *
          inputColumnStripPolynomial jin (|sqrtInputCenter jin L V| + 1) *
            exp (canonicalRepairKernelExponent * B + 4 * π * sqrt e) ≤
          ν.totalVariation.real univ * e * (canonicalRepairCellCoefficient * B) *
            exp (canonicalRepairKernelExponent * B + 4 * π * sqrt e) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpoly (by positivity)) (exp_nonneg _)
      exact mul_le_mul hcoeff hgeom
        (div_nonneg (pow_nonneg hθ.1 _) (by linarith [hθ.2])) (by positivity)
    _ = (canonicalRepairCellCoefficient * ν.totalVariation.real univ) * (B * e) *
        exp (canonicalRepairKernelExponent * B + 4 * π * sqrt e - (k : ℝ) * log 2) := by
      simp only [sub_eq_add_neg, exp_add, neg_mul]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (exp_nonneg _)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith [sq_nonneg (B - e)]

end GapFamily.Analytic
