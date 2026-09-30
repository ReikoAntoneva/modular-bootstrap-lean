import GapFamily.Analytic.Kernel.LowBandForm

/-!
# Pairing on nested low bands

Extension by zero from a smaller open band preserves the ordinary kernel
pairing and the identity term when these are computed on a larger open band.
These equalities hold for arbitrary functions; they do not assert integrability.
-/

noncomputable section

open MeasureTheory Real
open scoped ComplexConjugate ENNReal

namespace GapFamily.Analytic

/-- The ordinary kernel pairing is unchanged by extension by zero between
nested open low bands. -/
theorem lowBandKernelPairing_nested_zeroExtension_eq (j J : ℤ) {b B : ℝ}
    (hbB : b ≤ B) (K : ℝ × ℝ → ℂ) (f g : ℝ → ℂ) :
    lowBandKernelPairing j J B K ((Set.Ioo |(j : ℝ)| b).indicator f)
      ((Set.Ioo |(J : ℝ)| b).indicator g) =
      lowBandKernelPairing j J b K f g := by
  unfold lowBandKernelPairing
  rw [weakKernelIntegrand_lowBand_zeroExtension,
    integral_indicator (measurableSet_Ioo.prod measurableSet_Ioo),
    Measure.prod_restrict, Measure.prod_restrict,
    Measure.restrict_restrict_of_subset]
  intro p hp
  exact ⟨⟨hp.1.1, hp.1.2.trans_le hbB⟩, ⟨hp.2.1, hp.2.2.trans_le hbB⟩⟩

/-- The ordinary squared-norm integral is unchanged by extension by zero
between nested open low bands. -/
theorem integral_norm_sq_nested_lowBand_zeroExtension_eq (j : ℤ) {b B : ℝ}
    (hbB : b ≤ B) (f : ℝ → ℂ) :
    (∫ E, ‖(Set.Ioo |(j : ℝ)| b).indicator f E‖ ^ 2
      ∂(referenceMeasure j).restrict (Set.Ioo |(j : ℝ)| B)) =
      ∫ E, ‖f E‖ ^ 2 ∂(referenceMeasure j).restrict (Set.Ioo |(j : ℝ)| b) := by
  have heq : (fun E => ‖(Set.Ioo |(j : ℝ)| b).indicator f E‖ ^ 2) =
      (Set.Ioo |(j : ℝ)| b).indicator (fun E => ‖f E‖ ^ 2) := by
    funext E
    by_cases hE : E ∈ Set.Ioo |(j : ℝ)| b <;> simp [Set.indicator, hE]
  rw [heq, integral_indicator measurableSet_Ioo, Measure.restrict_restrict_of_subset]
  intro E hE
  exact ⟨hE.1, hE.2.trans_le hbB⟩

end GapFamily.Analytic
