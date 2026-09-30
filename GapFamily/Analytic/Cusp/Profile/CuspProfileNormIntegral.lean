import GapFamily.Analytic.Cusp.Fourier.CuspHorizontalProjectionPairingMeasure

/-!
# Scalar profile norm integration in the actual cusp

Ordinary integrability for the modular measure transports to the literal
inverse-square weighted product strip. Its horizontal width is one. A profile
supported above height one therefore has the stated one-dimensional norm
integral, including genuine integrability of that scalar integral.
-/

noncomputable section

namespace GapFamily.Analytic

open Set MeasureTheory UpperHalfPlane

private theorem cuspProfile_norm_row (b : ℝ → ℂ) (y : ℝ) :
    (∫ _x : ℝ in Ioo (-1/2) (1/2),
      (1 / y ^ 2 : ℝ) • ((‖b y‖ ^ 2 : ℝ) : ℂ)) =
      ((‖b y‖ ^ 2 / y ^ 2 : ℝ) : ℂ) := by
  rw [integral_const]
  norm_num [Measure.real, Real.volume_Ioo, Complex.real_smul, div_eq_mul_inv, mul_comm]

/-- The norm profile has an ordinary weighted integral, obtained from actual
modular integrability and the literal high-cusp coordinate transport. -/
theorem cuspProfile_scalar_norm_integral (b : ℝ → ℂ) (_hb : Continuous b)
    (hs : tsupport b ⊆ Ioi 1)
    (hi : Integrable (fun τ : UpperHalfPlane => ‖b τ.im‖ ^ 2) modularMeasure) :
    IntegrableOn (fun y : ℝ => ‖b y‖ ^ 2 / y ^ 2) (Ioi 1) ∧
      (∫ τ : UpperHalfPlane, ‖b τ.im‖ ^ 2 ∂modularMeasure) =
        ∫ y : ℝ in Ioi 1, ‖b y‖ ^ 2 / y ^ 2 := by
  have hhigh : IntegrableOn
      (fun τ : UpperHalfPlane => ((‖b (τ : ℂ).im‖ ^ 2 : ℝ) : ℂ))
      {τ | 1 < τ.im} modularMeasure := by
    simpa only [IntegrableOn, coe_im, RCLike.ofReal_eq_complex_ofReal] using
      (hi.ofReal (𝕜 := ℂ)).restrict
  have hprod := integrableOn_modular_highCusp_weight
    (fun z : ℂ => ((‖b z.im‖ ^ 2 : ℝ) : ℂ)) le_rfl hhigh
  rw [IntegrableOn, ← Measure.prod_restrict] at hprod
  have hrowIntegral : Integrable
      (fun y : ℝ => ((‖b y‖ ^ 2 / y ^ 2 : ℝ) : ℂ)) (volume.restrict (Ioi 1)) := by
    simpa only [cuspProfile_norm_row] using hprod.integral_prod_right
  have hscalar : IntegrableOn (fun y : ℝ => ‖b y‖ ^ 2 / y ^ 2) (Ioi 1) := by
    simpa only [IntegrableOn, RCLike.re_eq_complex_re, Complex.ofReal_re] using
      hrowIntegral.re
  refine ⟨hscalar, ?_⟩
  have htransport := integral_modular_highCusp_of_integrable
    (fun z : ℂ => ((‖b z.im‖ ^ 2 : ℝ) : ℂ)) le_rfl hhigh
  simp only [coe_im, cuspProfile_norm_row, integral_complex_ofReal] at htransport
  have hreal : (∫ τ : UpperHalfPlane in {τ | 1 < τ.im},
      ‖b τ.im‖ ^ 2 ∂modularMeasure) = ∫ y : ℝ in Ioi 1, ‖b y‖ ^ 2 / y ^ 2 :=
    Complex.ofReal_injective htransport
  have hzero : ∀ τ : UpperHalfPlane, τ ∉ {τ | 1 < τ.im} → ‖b τ.im‖ ^ 2 = 0 := by
    intro τ hτ
    have hb0 : b τ.im = 0 := by
      by_contra hne
      exact hτ (hs (subset_tsupport b hne))
    simp only [hb0, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  exact hreal

end GapFamily.Analytic
