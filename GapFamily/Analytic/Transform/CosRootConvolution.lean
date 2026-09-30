import GapFamily.Analytic.Transform.CosRootHalfFourier
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.Inversion

/-! The genuine regularized convolution of two damped cosRoot half-line profiles. -/
noncomputable section
namespace GapFamily.Analytic.CosRootLaplace
open Set MeasureTheory
open scoped Convolution FourierTransform

/-- The regularized convolution keeps the subtraction inside its integrable summands. -/
def cosRootConvolution (a : ℝ) (A B : ℂ) : ℝ → ℂ :=
  (fun x => regularHalfProfile a A (-x)) ⋆[ContinuousLinearMap.mul ℂ ℂ] halfProfile a B +
    (fun x => halfProfile a 0 (-x)) ⋆[ContinuousLinearMap.mul ℂ ℂ] regularHalfProfile a B

/-- Both summands are actual integrable functions of the convolution variable. -/
theorem integrable_cosRootConvolution {a : ℝ} (ha : 0 < a) (A B : ℂ) :
    Integrable (cosRootConvolution a A B) := by
  exact ((integrable_regularHalfProfile ha A).comp_neg.integrable_convolution
    (ContinuousLinearMap.mul ℂ ℂ) (integrable_halfProfile ha B)).add
    ((integrable_halfProfile ha 0).comp_neg.integrable_convolution
      (ContinuousLinearMap.mul ℂ ℂ) (integrable_regularHalfProfile ha B))

/-- The cancellation at the half-line endpoint makes the actual convolution continuous. -/
theorem continuous_cosRootConvolution {a : ℝ} (ha : 0 < a) (A B : ℂ) :
    Continuous (cosRootConvolution a A B) := by
  have hb : BddAbove (range fun x : ℝ => ‖regularHalfProfile a A (-x)‖) :=
    (bddAbove_regularHalfProfile ha A).mono (by rintro _ ⟨x, rfl⟩; exact ⟨-x, rfl⟩)
  exact (hb.continuous_convolution_left_of_integrable (ContinuousLinearMap.mul ℂ ℂ)
    ((continuous_regularHalfProfile a A).comp continuous_neg)
    (integrable_halfProfile ha B)).add
    ((bddAbove_regularHalfProfile ha B).continuous_convolution_right_of_integrable
      (ContinuousLinearMap.mul ℂ ℂ) (integrable_halfProfile ha 0).comp_neg
      (continuous_regularHalfProfile a B))

/-- The second summand has an ordinary integrable integrand at every point. -/
theorem cosRootConvolution_right_exists {a : ℝ} (ha : 0 < a) (B : ℂ) (x : ℝ) :
    ConvolutionExistsAt (fun t : ℝ => halfProfile a 0 (-t))
      (regularHalfProfile a B) x (ContinuousLinearMap.mul ℂ ℂ) volume := by
  apply BddAbove.convolutionExistsAt (ContinuousLinearMap.mul ℂ ℂ)
    (s := univ)
  · simpa using bddAbove_regularHalfProfile ha B
  · exact MeasurableSet.univ
  · exact subset_univ _
  · simpa using (integrable_halfProfile ha 0).comp_neg
  · exact (continuous_regularHalfProfile a B).aestronglyMeasurable

/-- The first summand also has an ordinary integrable integrand at every point. -/
theorem cosRootConvolution_left_exists {a : ℝ} (ha : 0 < a) (A B : ℂ) (x : ℝ) :
    ConvolutionExistsAt (fun t : ℝ => regularHalfProfile a A (-t))
      (halfProfile a B) x (ContinuousLinearMap.mul ℂ ℂ) volume := by
  apply convolutionExistsAt_flip.mp
  apply BddAbove.convolutionExistsAt (ContinuousLinearMap.mul ℂ ℂ).flip
    (s := univ)
  · simp only [preimage_univ, image_univ]
    exact (bddAbove_regularHalfProfile ha A).mono
      (by rintro _ ⟨t, rfl⟩; exact ⟨-t, rfl⟩)
  · exact MeasurableSet.univ
  · exact subset_univ _
  · simpa using integrable_halfProfile ha B
  · exact ((continuous_regularHalfProfile a A).comp continuous_neg).aestronglyMeasurable

/-- The Fourier transform is the literal product difference, without a formal divergent subtraction. -/
theorem fourier_cosRootConvolution {a : ℝ} (ha : 0 < a) (A B : ℂ) (t : ℝ) :
    𝓕 (cosRootConvolution a A B) t =
      halfFourierValue a A (-t) * halfFourierValue a B t -
        halfFourierValue a 0 (-t) * halfFourierValue a 0 t := by
  have h₁ := (integrable_regularHalfProfile ha A).comp_neg.integrable_convolution
    (ContinuousLinearMap.mul ℂ ℂ) (integrable_halfProfile ha B)
  have h₂ := (integrable_halfProfile ha 0).comp_neg.integrable_convolution
    (ContinuousLinearMap.mul ℂ ℂ) (integrable_regularHalfProfile ha B)
  have hadd : 𝓕 (cosRootConvolution a A B) t =
      𝓕 ((fun x => regularHalfProfile a A (-x)) ⋆[ContinuousLinearMap.mul ℂ ℂ]
        halfProfile a B) t +
      𝓕 ((fun x => halfProfile a 0 (-x)) ⋆[ContinuousLinearMap.mul ℂ ℂ]
        regularHalfProfile a B) t := by
    simp only [Real.fourier_eq, cosRootConvolution, Pi.add_apply, smul_add]
    exact integral_add ((Real.fourierIntegral_convergent_iff t).mpr h₁)
      ((Real.fourierIntegral_convergent_iff t).mpr h₂)
  rw [hadd, Real.fourier_mul_convolution_eq (integrable_regularHalfProfile ha A).comp_neg
      (integrable_halfProfile ha B),
    Real.fourier_mul_convolution_eq (integrable_halfProfile ha 0).comp_neg
      (integrable_regularHalfProfile ha B),
    fourier_regularHalfProfile_reflect ha, fourier_halfProfile ha,
    fourier_halfProfile_reflect ha, fourier_regularHalfProfile ha]
  ring

end GapFamily.Analytic.CosRootLaplace
