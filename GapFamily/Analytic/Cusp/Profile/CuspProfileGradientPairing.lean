import GapFamily.Analytic.Cusp.Profile.CuspProfileCore
import GapFamily.Analytic.Cusp.Fourier.CuspAverageDerivative
import GapFamily.Analytic.Cusp.Fourier.CuspHorizontalProjectionPairingMeasure

/-!
# Actual gradient pairing with a compact scalar cusp profile

The genuine modular L² pairing is transported before integrating in the
horizontal variable. Its inverse-square density cancels the two hyperbolic
frame factors, leaving the ordinary derivative of the actual average.
-/

noncomputable section
namespace GapFamily.Analytic
open Set MeasureTheory UpperHalfPlane ModularGradient
open scoped ContDiff

private theorem profile_gradient_cancel (y : ℝ) (hy : y ≠ 0) (c d : ℂ) :
    (1 / y ^ 2 : ℝ) • inner ℂ ((y : ℂ) * c) ((y : ℂ) * d) =
      starRingEnd ℂ c * d := by
  simp only [RCLike.inner_apply, map_mul, Complex.conj_ofReal, Complex.real_smul,
    Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_pow]
  have hyC : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy
  field_simp

private theorem profile_gradient_row (b : ℝ → ℂ) (F : smoothCore) {y : ℝ}
    (hy : 0 < y) :
    (∫ x : ℝ in Ioo (-1/2) (1/2), (1 / y ^ 2 : ℝ) •
      inner ℂ ((y : ℂ) * deriv b y)
        ((y : ℂ) * fderiv ℝ F.val (Complex.mk x y) Complex.I)) =
      starRingEnd ℂ (deriv b y) * deriv (cuspHorizontalAverage F.val) y := by
  simp_rw [profile_gradient_cancel y hy.ne']
  rw [integral_const_mul, deriv_cuspHorizontalAverage F hy]
  congr 1
  rw [intervalIntegral.integral_of_le (by norm_num : (-1/2 : ℝ) ≤ 1/2),
    restrict_Ioo_eq_restrict_Ioc]

/-- The actual full gradient pairing equals the ordinary vertical derivative
pairing, whose integrability is proved as part of the statement. -/
theorem cuspProfileCore_gradient_pairing_integrable (b : ℝ → ℂ)
    (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b)
    (hs : tsupport b ⊆ Ioi (1 : ℝ)) (F : smoothCore) :
    IntegrableOn (fun y : ℝ => starRingEnd ℂ (deriv b y) *
      deriv (cuspHorizontalAverage F.val) y) (Ioi 1) ∧
    inner ℂ (coreGradient (cuspProfileCore b hb hc hs)) (coreGradient F) =
      ∫ y : ℝ in Ioi 1, starRingEnd ℂ (deriv b y) *
        deriv (cuspHorizontalAverage F.val) y := by
  let P := cuspProfileCore b hb hc hs
  have hP0 : xComponent P = 0 := by
    apply Lp.ext
    filter_upwards [component_ae 1 (fun G => G.property.2.2.2.1) P,
      cuspProfileCore_directional_ae b hb hc hs 1,
      Lp.coeFn_zero (E := ℂ) (p := 2) (μ := modularMeasure)] with τ hx hp hz
    change xComponent P τ = _ at hx
    change directional P.val 1 τ = _ at hp
    rw [hx, hp, hz]
    simp only [Complex.one_im, zero_smul, mul_zero, Pi.zero_apply]
  have hP : yComponent P =ᵐ[modularMeasure]
      fun τ : UpperHalfPlane => (τ.im : ℂ) * deriv b τ.im := by
    exact (component_ae Complex.I (fun G => G.property.2.2.2.2) P).trans
      (by simpa only [Complex.I_im, one_smul] using
        cuspProfileCore_directional_ae b hb hc hs Complex.I)
  have hF : yComponent F =ᵐ[modularMeasure] directional F.val Complex.I :=
    component_ae Complex.I (fun G => G.property.2.2.2.2) F
  let g : ℂ → ℂ := fun z => inner ℂ ((z.im : ℂ) * deriv b z.im)
    ((z.im : ℂ) * fderiv ℝ F.val z Complex.I)
  have hg : Integrable (fun τ : UpperHalfPlane => g τ) modularMeasure := by
    apply (L2.integrable_inner (𝕜 := ℂ) (yComponent P) (yComponent F)).congr
    filter_upwards [hP, hF] with τ hp hf
    rw [hp, hf]
    rfl
  have hwhole : inner ℂ (coreGradient P) (coreGradient F) =
      ∫ τ : UpperHalfPlane, g τ ∂modularMeasure := by
    rw [WithLp.prod_inner_apply, coreGradient_fst, coreGradient_fst,
      coreGradient_snd, coreGradient_snd, hP0, inner_zero_left, zero_add, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hP, hF] with τ hp hf
    rw [hp, hf]
    rfl
  have hzero : ∀ τ : UpperHalfPlane, τ ∉ {τ : UpperHalfPlane | 1 < τ.im} → g τ = 0 := by
    intro τ hτ
    have hb0 : deriv b τ.im = 0 := deriv_of_notMem_tsupport
      (fun hm => hτ (hs hm))
    simp only [g, coe_im, hb0, mul_zero, inner_zero_left]
  have hprod := integrableOn_modular_highCusp_weight g le_rfl hg.restrict
  rw [IntegrableOn, ← Measure.prod_restrict] at hprod
  have hrow : IntegrableOn (fun y : ℝ => starRingEnd ℂ (deriv b y) *
      deriv (cuspHorizontalAverage F.val) y) (Ioi 1) := by
    apply hprod.integral_prod_right.congr
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with y hy
    exact profile_gradient_row b F (zero_lt_one.trans hy)
  refine ⟨hrow, ?_⟩
  rw [hwhole, ← setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
    integral_modular_highCusp_of_integrable g le_rfl hg.restrict]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  exact profile_gradient_row b F (zero_lt_one.trans hy)

theorem cuspProfileCore_gradient_pairing (b : ℝ → ℂ)
    (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b)
    (hs : tsupport b ⊆ Ioi (1 : ℝ)) (F : smoothCore) :
    inner ℂ (coreGradient (cuspProfileCore b hb hc hs)) (coreGradient F) =
      ∫ y : ℝ in Ioi 1, starRingEnd ℂ (deriv b y) *
        deriv (cuspHorizontalAverage F.val) y :=
  (cuspProfileCore_gradient_pairing_integrable b hb hc hs F).2

end GapFamily.Analytic
