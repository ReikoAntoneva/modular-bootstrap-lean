import GapFamily.Analytic.Cusp.Fourier.CuspHorizontalProjectionPairingMeasure

/-!
# Norm integration for a profile clipped at height one

The actual modular integrability premise transports through the high-cusp
product measure. No continuity or separation of support from height one is
needed, so this identity also applies to representatives obtained by graph
closure.
-/

noncomputable section

namespace GapFamily.Analytic

open Set MeasureTheory UpperHalfPlane

private theorem cuspProfile_indicator_norm_row (b : ℝ → ℂ) (y : ℝ) :
    (∫ _x : ℝ in Ioo (-1/2) (1/2),
      (1 / y ^ 2 : ℝ) • ((‖b y‖ ^ 2 : ℝ) : ℂ)) =
      ((‖b y‖ ^ 2 / y ^ 2 : ℝ) : ℂ) := by
  rw [integral_const]
  norm_num [Measure.real, Real.volume_Ioo, Complex.real_smul, div_eq_mul_inv, mul_comm]

/-- Actual modular norm transport for a profile clipped to the high cusp.
The scalar integrability conclusion follows from the modular integrability
premise through the literal inverse-square weighted product measure. -/
theorem cuspProfile_indicator_norm_integral (b : ℝ → ℂ)
    (hi : Integrable (fun τ : UpperHalfPlane =>
      ‖if 1 < τ.im then b τ.im else 0‖ ^ 2) modularMeasure) :
    IntegrableOn (fun y : ℝ => ‖b y‖ ^ 2 / y ^ 2) (Ioi 1) ∧
      (∫ τ : UpperHalfPlane, ‖if 1 < τ.im then b τ.im else 0‖ ^ 2 ∂modularMeasure) =
        ∫ y : ℝ in Ioi 1, ‖b y‖ ^ 2 / y ^ 2 := by
  have hS : MeasurableSet {τ : UpperHalfPlane | 1 < τ.im} :=
    (isOpen_lt continuous_const UpperHalfPlane.continuous_im).measurableSet
  have hrealhigh : IntegrableOn (fun τ : UpperHalfPlane => ‖b τ.im‖ ^ 2)
      {τ | 1 < τ.im} modularMeasure := by
    apply hi.restrict.congr
    filter_upwards [ae_restrict_mem (μ := modularMeasure) hS] with τ hτ
    simp only [ite_eq_left hτ]
  have hhigh : IntegrableOn
      (fun τ : UpperHalfPlane => ((‖b (τ : ℂ).im‖ ^ 2 : ℝ) : ℂ))
      {τ | 1 < τ.im} modularMeasure := by
    simpa only [IntegrableOn, coe_im, RCLike.ofReal_eq_complex_ofReal] using
      (hrealhigh.ofReal (𝕜 := ℂ))
  have hprod := integrableOn_modular_highCusp_weight
    (fun z : ℂ => ((‖b z.im‖ ^ 2 : ℝ) : ℂ)) le_rfl hhigh
  rw [IntegrableOn, ← Measure.prod_restrict] at hprod
  have hrowIntegral : Integrable
      (fun y : ℝ => ((‖b y‖ ^ 2 / y ^ 2 : ℝ) : ℂ)) (volume.restrict (Ioi 1)) := by
    simpa only [cuspProfile_indicator_norm_row] using hprod.integral_prod_right
  have hscalar : IntegrableOn (fun y : ℝ => ‖b y‖ ^ 2 / y ^ 2) (Ioi 1) := by
    simpa only [IntegrableOn, RCLike.re_eq_complex_re, Complex.ofReal_re] using
      hrowIntegral.re
  refine ⟨hscalar, ?_⟩
  have htransport := integral_modular_highCusp_of_integrable
    (fun z : ℂ => ((‖b z.im‖ ^ 2 : ℝ) : ℂ)) le_rfl hhigh
  simp only [coe_im, cuspProfile_indicator_norm_row, integral_complex_ofReal] at htransport
  have hreal : (∫ τ : UpperHalfPlane in {τ | 1 < τ.im},
      ‖b τ.im‖ ^ 2 ∂modularMeasure) = ∫ y : ℝ in Ioi 1, ‖b y‖ ^ 2 / y ^ 2 :=
    Complex.ofReal_injective htransport
  have hzero : ∀ τ : UpperHalfPlane, τ ∉ {τ | 1 < τ.im} →
      ‖if 1 < τ.im then b τ.im else 0‖ ^ 2 = 0 := by
    intro τ hτ
    change ¬ 1 < τ.im at hτ
    simp only [ite_eq_right hτ, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  trans ∫ τ : UpperHalfPlane in {τ | 1 < τ.im}, ‖b τ.im‖ ^ 2 ∂modularMeasure
  · apply setIntegral_congr_fun hS
    intro τ hτ
    change 1 < τ.im at hτ
    simp only [ite_eq_left hτ]
  · exact hreal

end GapFamily.Analytic
