import GapFamily.Analytic.Foundation.SignedMomentIntegral

/-! Compact physical support is preserved by signed linear combinations.
Every support condition is stated for the actual variation measure.
-/

namespace GapFamily.Analytic

open MeasureTheory

/-- Adding signed inputs preserves a common compact physical support. -/
theorem signedPhysicalSupport_add (ν μ : SignedMeasure ℝ) (J : ℤ) (M : ℝ)
    (hν : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ M)
    (hμ : ∀ᵐ E ∂μ.variation, |(J : ℝ)| ≤ E ∧ E ≤ M) :
    ∀ᵐ E ∂(ν + μ).variation, |(J : ℝ)| ≤ E ∧ E ≤ M := by
  exact (ae_add_measure_iff.mpr ⟨hν, hμ⟩).filter_mono
    (ae_mono VectorMeasure.variation_add_le)

/-- Negating a signed input leaves its physical support unchanged. -/
theorem signedPhysicalSupport_neg (ν : SignedMeasure ℝ) (J : ℤ) (M : ℝ)
    (hν : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ M) :
    ∀ᵐ E ∂(-ν).variation, |(J : ℝ)| ≤ E ∧ E ≤ M := by
  simpa only [VectorMeasure.variation_neg] using hν

/-- Subtracting signed inputs preserves a common compact physical support. -/
theorem signedPhysicalSupport_sub (ν μ : SignedMeasure ℝ) (J : ℤ) (M : ℝ)
    (hν : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ M)
    (hμ : ∀ᵐ E ∂μ.variation, |(J : ℝ)| ≤ E ∧ E ≤ M) :
    ∀ᵐ E ∂(ν - μ).variation, |(J : ℝ)| ≤ E ∧ E ≤ M := by
  simpa only [sub_eq_add_neg] using
    signedPhysicalSupport_add ν (-μ) J M hν (signedPhysicalSupport_neg μ J M hμ)

/-- Real scaling preserves the physical support, including a zero scale. -/
theorem signedPhysicalSupport_smul (ν : SignedMeasure ℝ) (J : ℤ) (M c : ℝ)
    (hν : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ M) :
    ∀ᵐ E ∂(c • ν).variation, |(J : ℝ)| ≤ E ∧ E ≤ M := by
  rw [VectorMeasure.variation_smul]
  exact Measure.ae_smul_measure hν ‖c‖₊

end GapFamily.Analytic
