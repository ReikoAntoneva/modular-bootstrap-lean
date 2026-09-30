import GapFamily.Analytic.Poincare.Repair.PoincareExteriorMoment
import GapFamily.Analytic.Poincare.Repair.PoincareExteriorKernelBound

/-! Quantitative cancellation for actual compact signed inputs. The fixed
canonical inverse and anchor contribute only a universal exponential in B;
the imaginary input radius keeps the sharp factor `4πr√e`.
-/

noncomputable section

open Set MeasureTheory Real

namespace GapFamily.Analytic

/-- The actual signed energy kernel obeys the full quantitative Cauchy bound,
uniformly over all physical output spins and exterior energies. -/
theorem norm_signedIntegral_canonicalRepairKernelEnergy_le_exp
    (B : ℝ) (hB : 1 ≤ B) (j jin : ℤ) (e : ℝ)
    (he : |(j : ℝ)| ≤ e) (hBe : B ≤ e)
    (ν : SignedMeasure ℝ) (L V r : ℝ) (k : ℕ)
    (hL : |(jin : ℝ)| ≤ L) (hLV : L ≤ V) (hr : 0 < r)
    (hdr : sqrtInputWidth jin L V / (2 * r) < 1)
    (hν : ∀ᵐ E ∂ν.variation, E ∈ Icc L V)
    (hm : ∀ n ≤ k, (∫ᵛ x : ℝ, x ^ n ∂<•signedSqrtCoordinate jin ν) = 0) :
    ‖∫ᵛ E, canonicalRepairKernelEnergy B hB j jin e E ∂<•ν‖ ≤
      ν.totalVariation.real univ * e *
        inputColumnStripPolynomial jin (|sqrtInputCenter jin L V| + r) *
          exp (canonicalRepairKernelExponent * B + 4 * π * r * sqrt e) *
            (sqrtInputWidth jin L V / (2 * r)) ^ (k + 1) /
              (1 - sqrtInputWidth jin L V / (2 * r)) := by
  have hsize := canonicalRepairKernelStripSize_le_exp B hB j jin e
    (|sqrtInputCenter jin L V| + r) r he hBe (by positivity) hr.le
  have hθ : 0 ≤ sqrtInputWidth jin L V / (2 * r) :=
    div_nonneg (sqrtInputWidth_nonneg jin L V hLV) (by positivity)
  apply (norm_signedIntegral_canonicalRepairKernelEnergy_le B hB j jin e he
    ν L V r k hL hLV hr hdr hν hm).trans
  calc
    _ ≤ (ν.totalVariation.real univ *
        (e * inputColumnStripPolynomial jin (|sqrtInputCenter jin L V| + r) *
          exp (canonicalRepairKernelExponent * B + 4 * π * r * sqrt e))) *
            (sqrtInputWidth jin L V / (2 * r)) ^ (k + 1) /
              (1 - sqrtInputWidth jin L V / (2 * r)) := by
      apply div_le_div_of_nonneg_right _ (sub_nonneg.mpr hdr.le)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsize (measureReal_nonneg)) (pow_nonneg hθ _)
    _ = _ := by ring

end GapFamily.Analytic
