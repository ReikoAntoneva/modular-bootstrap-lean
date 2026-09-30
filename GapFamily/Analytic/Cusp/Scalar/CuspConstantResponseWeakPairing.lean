import GapFamily.Analytic.Cusp.Scalar.CuspConstantResponseFormPairing
import GapFamily.Analytic.Cusp.Profile.CuspProfileLaplacian

/-! Actual compact scalar test pairings with the constant-source form response. -/

noncomputable section
namespace GapFamily.Analytic

open Set MeasureTheory UpperHalfPlane ModularGradient
open scoped ContDiff

private theorem cuspProfileCore_scalar_inner_ae
    (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b)
    (hs : tsupport b ⊆ Ioi (1 : ℝ)) (F : ModularHilbert) (q : ℝ → ℂ)
    (hF : ∀ᵐ τ ∂modularMeasure, 1 < τ.im → F τ = q τ.im) :
    (fun τ => inner ℂ ((value (cuspProfileCore b hb hc hs)) τ) (F τ)) =ᵐ[modularMeasure]
      (fun τ => star (b τ.im) * q τ.im) := by
  filter_upwards [cuspProfileCore_value_ae b hb hc hs, hF] with τ hbτ hFτ
  rw [hbτ]
  by_cases ht : 1 < τ.im
  · rw [hFτ ht, RCLike.inner_apply', starRingEnd_apply]
  · have hz : b τ.im = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hh => ht (hs hh))
    simp [hz]

private theorem scalar_pairing_row (b q : ℝ → ℂ) (y : ℝ) :
    (∫ _x : ℝ in Ioo (-1/2) (1/2), (1 / y ^ 2 : ℝ) • (star (b y) * q y)) =
      star (b y) * q y / (y : ℂ) ^ 2 := by
  rw [integral_const]
  norm_num [Measure.real, Real.volume_Ioo, Complex.real_smul, div_eq_mul_inv, mul_comm]

/-- Actual scalar integrability follows from the L² inner product and high-cusp Fubini. -/
theorem cuspProfileCore_scalar_pairing_integrable
    (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b)
    (hs : tsupport b ⊆ Ioi (1 : ℝ)) (F : ModularHilbert) (q : ℝ → ℂ)
    (hF : ∀ᵐ τ ∂modularMeasure, 1 < τ.im → F τ = q τ.im) :
    IntegrableOn (fun y => star (b y) * q y / (y : ℂ) ^ 2) (Ioi 1) := by
  have hi := (L2.integrable_inner (𝕜 := ℂ) (value (cuspProfileCore b hb hc hs)) F).congr
    (cuspProfileCore_scalar_inner_ae b hb hc hs F q hF)
  have hprod := integrableOn_modular_highCusp_weight
    (fun z : ℂ => star (b z.im) * q z.im) le_rfl hi.integrableOn
  rw [IntegrableOn, ← Measure.prod_restrict] at hprod
  simpa only [IntegrableOn, scalar_pairing_row] using hprod.integral_prod_right

/-- Actual compact scalar tests pair with any Hilbert target whose high-cusp
representative is the specified scalar function. -/
theorem cuspProfileCore_scalar_pairing
    (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b)
    (hs : tsupport b ⊆ Ioi (1 : ℝ)) (F : ModularHilbert) (q : ℝ → ℂ)
    (hF : ∀ᵐ τ ∂modularMeasure, 1 < τ.im → F τ = q τ.im) :
    inner ℂ (value (cuspProfileCore b hb hc hs)) F =
      ∫ y : ℝ in Ioi 1, star (b y) * q y / (y : ℂ) ^ 2 := by
  have hae := cuspProfileCore_scalar_inner_ae b hb hc hs F q hF
  have hi := (L2.integrable_inner (𝕜 := ℂ) (value (cuspProfileCore b hb hc hs)) F).congr hae
  rw [L2.inner_def, integral_congr_ae hae]
  have hzero : ∀ τ : UpperHalfPlane, τ ∉ {τ | 1 < τ.im} →
      star (b τ.im) * q τ.im = 0 := by
    intro τ hτ
    have hz : b τ.im = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hh => hτ (hs hh))
    simp [hz]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  have ht := integral_modular_highCusp_of_integrable
    (fun z : ℂ => star (b z.im) * q z.im) le_rfl hi.integrableOn
  simpa only [coe_im, scalar_pairing_row] using ht

/-- The actual compact profile response pairing in the physical coordinate. -/
theorem cuspConstantForm_test_pairing
    (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b)
    (hs : tsupport b ⊆ Ioi (1 : ℝ)) {κ : ℂ} (hκ : 0 < κ.re) :
    inner ℂ (value (cuspProfileCore b hb hc hs)) (formEmbedding (cuspConstantForm hκ)) =
      ∫ y : ℝ in Ioi 1, star (b y) * cuspConstantPhysicalResponse κ y / (y : ℂ) ^ 2 := by
  apply cuspProfileCore_scalar_pairing
  filter_upwards [cuspConstantForm_embedding_ae hκ] with τ hτ
  intro ht
  simpa only [ite_eq_left ht] using hτ

/-- The actual constant source pairing has its inverse-square measure factor. -/
theorem cuspConstantForm_test_source_pairing
    (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b)
    (hs : tsupport b ⊆ Ioi (1 : ℝ)) :
    inner ℂ (value (cuspProfileCore b hb hc hs)) modularConstant =
      ∫ y : ℝ in Ioi 1, star (b y) / (y : ℂ) ^ 2 := by
  have h := cuspProfileCore_scalar_pairing b hb hc hs modularConstant (fun _ => 1) ?_
  · simpa only [mul_one] using h
  · filter_upwards [modularConstant_ae] with τ hτ
    exact fun _ => hτ

/-- Density cancellation in the literal compact-test Laplacian pairing. -/
theorem cuspConstantForm_test_laplacian_pairing
    (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b)
    (hs : tsupport b ⊆ Ioi (1 : ℝ)) {κ : ℂ} (hκ : 0 < κ.re) :
    inner ℂ (cuspProfileLaplacianValue b hb hc hs) (formEmbedding (cuspConstantForm hκ)) =
      -(∫ y : ℝ in Ioi 1, star (deriv (deriv b) y) * cuspConstantPhysicalResponse κ y) := by
  rw [cuspProfileLaplacianValue, cuspConstantForm_test_pairing, ← integral_neg]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (zero_lt_one.trans hy))
  dsimp only
  simp only [cuspProfileSecondOrder, star_mul', star_neg, star_pow,
    Complex.star_def, Complex.conj_ofReal]
  field_simp

/-- The genuine completed-gradient pairing is the scalar compact-test second derivative. -/
theorem cuspConstantForm_test_gradient_pairing
    (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b)
    (hs : tsupport b ⊆ Ioi (1 : ℝ)) {κ : ℂ} (hκ : 0 < κ.re) :
    inner ℂ (coreGradient (cuspProfileCore b hb hc hs)) (formGradient (cuspConstantForm hκ)) =
      -(∫ y : ℝ in Ioi 1, star (deriv (deriv b) y) * cuspConstantPhysicalResponse κ y) := by
  rw [← cuspProfileCore_form_energy]
  exact cuspConstantForm_test_laplacian_pairing b hb hc hs hκ


end GapFamily.Analytic
