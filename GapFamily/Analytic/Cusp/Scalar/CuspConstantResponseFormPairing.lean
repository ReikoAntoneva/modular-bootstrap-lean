import GapFamily.Analytic.Cusp.Scalar.CuspConstantResponseForm
import GapFamily.Analytic.Cusp.Scalar.CuspConstantResponseMass
import GapFamily.Analytic.Cusp.Fourier.CuspHorizontalProjectionPairingMeasure

/-!
# Ordinary constant pairing of the actual scalar cusp form

The true embedded form representative is integrated over the modular high cusp.
The width-one product strip gives precisely the scalar inverse-square pairing;
ordinary integrability comes from its actual modular Hilbert-space membership.
-/

noncomputable section
namespace GapFamily.Analytic
open Set MeasureTheory UpperHalfPlane ModularGradient

private theorem profile_pairing_row (b : ℝ → ℂ) (y : ℝ) :
    (∫ _x : ℝ in Ioo (-1/2) (1/2), (1 / y ^ 2 : ℝ) • b y) =
      b y / (y : ℂ) ^ 2 := by
  rw [integral_const]
  norm_num [Measure.real, Real.volume_Ioo, Complex.real_smul, div_eq_mul_inv, mul_comm]

private theorem integral_profile_indicator (b : ℝ → ℂ)
    (hi : Integrable (fun τ : UpperHalfPlane =>
      if 1 < τ.im then b τ.im else 0) modularMeasure) :
    (∫ τ : UpperHalfPlane, (if 1 < τ.im then b τ.im else 0) ∂modularMeasure) =
      ∫ y : ℝ in Ioi 1, b y / (y : ℂ) ^ 2 := by
  have hS : MeasurableSet {τ : UpperHalfPlane | 1 < τ.im} :=
    (isOpen_lt continuous_const UpperHalfPlane.continuous_im).measurableSet
  have hhigh : IntegrableOn (fun τ : UpperHalfPlane => b τ.im)
      {τ | 1 < τ.im} modularMeasure := by
    apply hi.restrict.congr
    filter_upwards [ae_restrict_mem (μ := modularMeasure) hS] with τ hτ
    simp only [ite_eq_left hτ]
  have htransport := integral_modular_highCusp_of_integrable
    (fun z : ℂ => b z.im) le_rfl hhigh
  simp only [coe_im, profile_pairing_row] at htransport
  have hzero : ∀ τ : UpperHalfPlane, τ ∉ {τ | 1 < τ.im} →
      (if 1 < τ.im then b τ.im else 0) = 0 := by
    intro τ hτ
    exact ite_eq_right hτ
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  trans ∫ τ : UpperHalfPlane in {τ | 1 < τ.im}, b τ.im ∂modularMeasure
  · apply setIntegral_congr_fun hS
    intro τ hτ
    exact ite_eq_left hτ
  · exact htransport

/-- Pairing the actual modular constant with the actual embedded cusp form
has the scalar normalization from the ordinary high-cusp integral. -/
theorem cuspConstantForm_pairing {κ : ℂ} (hκ : 0 < κ.re) :
    inner ℂ modularConstant (formEmbedding (cuspConstantForm hκ)) =
      1 / (κ + 1 / 2) ^ 2 := by
  have hi : Integrable (fun τ : UpperHalfPlane =>
      if 1 < τ.im then cuspConstantPhysicalResponse κ τ.im else 0) modularMeasure :=
    (integrable_modularHilbert (formEmbedding (cuspConstantForm hκ))).congr
      (cuspConstantForm_embedding_ae hκ)
  rw [modularConstant_inner, integral_congr_ae (cuspConstantForm_embedding_ae hκ),
    integral_profile_indicator _ hi]
  exact cuspConstantPhysicalResponse_pairing (by linarith)

/-- The same actual pairing, expressed with the constructed vector in the
closed scalar form subspace. -/
theorem cuspConstantScalarForm_pairing {κ : ℂ} (hκ : 0 < κ.re) :
    inner ℂ modularConstant (formEmbedding (cuspConstantScalarForm hκ)) =
      1 / (κ + 1 / 2) ^ 2 :=
  cuspConstantForm_pairing hκ

/-- At the removable physical parameter, the actual form pairs to one. -/
theorem cuspConstantForm_half_pairing :
    inner ℂ modularConstant
      (formEmbedding (cuspConstantForm (κ := (1 / 2 : ℂ)) (by norm_num))) = 1 := by
  have h := cuspConstantForm_pairing (κ := (1 / 2 : ℂ)) (by norm_num)
  norm_num at h ⊢
  exact h

end GapFamily.Analytic
