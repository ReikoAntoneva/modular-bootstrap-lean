import GapFamily.Analytic.Poincare.Repair.PoincareExteriorEstimate
import GapFamily.Analytic.Foundation.GeometricMomentDecay

/-! The initial-cell exterior estimate uses radius `η * sqrt a / 2`.
The actual coordinate width supplies the moment-decay ratio; the exponential
retains the exact initial-radius coefficient `2 * π * η * sqrt (a * e)`.
-/

noncomputable section

namespace GapFamily.Analytic

open Set MeasureTheory Real

/-- Actual signed moment cancellation at the initial-cell radius. Compact
physical input and ordinary moments supply every integrability hypothesis.
The estimate also applies before imposing the later cutoff condition `V < B`.
-/
theorem norm_signedIntegral_canonicalRepairKernelEnergy_initial_le
    (B : ℝ) (hB : 1 ≤ B) (j jin : ℤ) (e : ℝ)
    (he : |(j : ℝ)| ≤ e) (hBe : B ≤ e)
    (ν : SignedMeasure ℝ) (L V a η : ℝ) (k : ℕ)
    (hL : |(jin : ℝ)| ≤ L) (hLV : L ≤ V) (ha : 0 < a) (hη : 0 < η)
    (hwidth : sqrtInputWidth jin L V / (η * sqrt a) ≤ 1 / 2)
    (hν : ∀ᵐ E ∂ν.variation, E ∈ Icc L V)
    (hm : ∀ n ≤ k, (∫ᵛ x : ℝ, x ^ n ∂<•signedSqrtCoordinate jin ν) = 0) :
    ‖∫ᵛ E, canonicalRepairKernelEnergy B hB j jin e E ∂<•ν‖ ≤
      ν.totalVariation.real univ * e *
        inputColumnStripPolynomial jin (|sqrtInputCenter jin L V| + η * sqrt a / 2) *
          exp (canonicalRepairKernelExponent * B + 2 * π * η * sqrt (a * e)) *
            (sqrtInputWidth jin L V / (η * sqrt a)) ^ k := by
  have hsqrta : 0 < sqrt a := sqrt_pos.mpr ha
  have hr : 0 < η * sqrt a / 2 := by positivity
  have hdenom : 2 * (η * sqrt a / 2) = η * sqrt a := by ring
  have hratio : sqrtInputWidth jin L V / (2 * (η * sqrt a / 2)) < 1 := by
    rw [hdenom]
    linarith
  have hθ : 0 ≤ sqrtInputWidth jin L V / (η * sqrt a) :=
    div_nonneg (sqrtInputWidth_nonneg jin L V hLV) (by positivity)
  have hexponent : 4 * π * (η * sqrt a / 2) * sqrt e =
      2 * π * η * sqrt (a * e) := by
    rw [sqrt_mul ha.le]
    ring
  have h := norm_signedIntegral_canonicalRepairKernelEnergy_le_exp
    B hB j jin e he hBe ν L V (η * sqrt a / 2) k hL hLV hr hratio hν hm
  rw [hdenom, hexponent] at h
  apply h.trans
  rw [mul_div_assoc]
  have he0 : 0 ≤ e := (zero_le_one.trans hB).trans hBe
  have hP := (inputColumnStripPolynomial_pos jin
    (|sqrtInputCenter jin L V| + η * sqrt a / 2) (by positivity)).le
  exact mul_le_mul_of_nonneg_left
    (geometricMomentRemainder_le_pow _ hθ hwidth k) (by positivity)

end GapFamily.Analytic
