import GapFamily.Analytic.Foundation.SignedMomentIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Continuous linear maps and signed integration

The signed Bochner integral commutes with continuous real-linear maps.  Both
integrability and the identity use the actual variation measure and Jordan
decomposition, so this applies to maps between arbitrary real Banach spaces.
-/

noncomputable section

namespace GapFamily.Analytic

open MeasureTheory

variable {α E F : Type*} [MeasurableSpace α]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem signedIntegral_eq_jordan_on {ν : SignedMeasure α} {f : α → E}
    (hf : ν.Integrable f) :
    (∫ᵛ x, f x ∂<•ν) =
      (∫ x, f x ∂ν.toJordanDecomposition.posPart) -
        ∫ x, f x ∂ν.toJordanDecomposition.negPart := by
  have hi : Integrable f
      (ν.toJordanDecomposition.posPart + ν.toJordanDecomposition.negPart) := by
    simpa only [VectorMeasure.Integrable, ← SignedMeasure.totalVariation_eq_variation,
      SignedMeasure.totalVariation] using hf
  have hp : ν.toJordanDecomposition.posPart.toSignedMeasure.Integrable f := by
    simpa only [VectorMeasure.Integrable, Measure.variation_toSignedMeasure]
      using hi.left_of_add_measure
  have hn : ν.toJordanDecomposition.negPart.toSignedMeasure.Integrable f := by
    simpa only [VectorMeasure.Integrable, Measure.variation_toSignedMeasure]
      using hi.right_of_add_measure
  conv_lhs => rw [← ν.toSignedMeasure_toJordanDecomposition]
  rw [JordanDecomposition.toSignedMeasure,
    VectorMeasure.integral_sub_vectorMeasure hp hn]
  simp only [VectorMeasure.integral_toSignedMeasure]

/-- Composition by a continuous real-linear map preserves signed integrability. -/
theorem signedIntegrable_continuousLinearMap (T : E →L[ℝ] F)
    {ν : SignedMeasure α} {f : α → E} (hf : ν.Integrable f) :
    ν.Integrable (fun x => T (f x)) :=
  T.integrable_comp hf

/-- A continuous real-linear map commutes with the actual signed integral. -/
theorem continuousLinearMap_signedIntegral [CompleteSpace E] [CompleteSpace F]
    (T : E →L[ℝ] F) {ν : SignedMeasure α} {f : α → E}
    (hf : ν.Integrable f) :
    T (∫ᵛ x, f x ∂<•ν) = ∫ᵛ x, T (f x) ∂<•ν := by
  have hi : Integrable f
      (ν.toJordanDecomposition.posPart + ν.toJordanDecomposition.negPart) := by
    simpa only [VectorMeasure.Integrable, ← SignedMeasure.totalVariation_eq_variation,
      SignedMeasure.totalVariation] using hf
  rw [signedIntegral_eq_jordan_on hf,
    signedIntegral_eq_jordan_on (signedIntegrable_continuousLinearMap T hf),
    map_sub, T.integral_comp_comm hi.left_of_add_measure,
    T.integral_comp_comm hi.right_of_add_measure]

/-- Complex-linear maps commute with signed integration after restricting
scalars to the real field of the signed measure. -/
theorem complexContinuousLinearMap_signedIntegral
    [NormedSpace ℂ E] [NormedSpace ℂ F]
    [IsScalarTower ℝ ℂ E] [IsScalarTower ℝ ℂ F]
    [CompleteSpace E] [CompleteSpace F]
    (T : E →L[ℂ] F) {ν : SignedMeasure α} {f : α → E}
    (hf : ν.Integrable f) :
    T (∫ᵛ x, f x ∂<•ν) = ∫ᵛ x, T (f x) ∂<•ν :=
  continuousLinearMap_signedIntegral (T.restrictScalars ℝ) hf

/-- Taking the real part commutes with a genuinely integrable complex signed
integral. -/
theorem signedIntegral_re {ν : SignedMeasure α} {f : α → ℂ}
    (hf : ν.Integrable f) :
    (∫ᵛ x, f x ∂<•ν).re = ∫ᵛ x, (f x).re ∂<•ν :=
  continuousLinearMap_signedIntegral Complex.reCLM hf

end GapFamily.Analytic
