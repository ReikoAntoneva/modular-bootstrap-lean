import GapFamily.Analytic.Cusp.Profile.CuspProfileFormMeasure
import GapFamily.Analytic.Modular.Elliptic.ModularInteriorCompactCore
import GapFamily.Analytic.Modular.Elliptic.ModularInteriorCompactWeight

/-!
# Norms of actual form-domain vectors with scalar cusp representatives

The hypotheses identify the value and the two actual closed-gradient
components of an existing form-domain vector. Their intrinsic L² membership
supplies the integrability required by cusp measure transport. The resulting
form norm is the weighted scalar mass plus the ordinary derivative energy.
-/

noncomputable section

namespace GapFamily.Analytic

open Set MeasureTheory UpperHalfPlane ModularGradient

private theorem cuspProfile_modular_norm_sq (f : ModularHilbert) :
    ‖f‖ ^ 2 = ∫ τ : UpperHalfPlane, ‖f τ‖ ^ 2 ∂modularMeasure := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

/-- The actual value representative determines the weighted scalar mass norm. -/
theorem cuspProfile_form_value_norm_sq_of_ae (u : FormDomain) (b : ℝ → ℂ)
    (hvalue : formEmbedding u =ᵐ[modularMeasure]
      (fun τ : UpperHalfPlane => if 1 < τ.im then b τ.im else 0)) :
    IntegrableOn (fun y : ℝ => ‖b y‖ ^ 2 / y ^ 2) (Ioi 1) ∧
      ‖formEmbedding u‖ ^ 2 = ∫ y : ℝ in Ioi 1, ‖b y‖ ^ 2 / y ^ 2 := by
  have hm := Lp.memLp (formEmbedding u)
  have hi := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
  have hnorm := hvalue.mono (fun τ hτ => congrArg (fun z : ℂ => ‖z‖ ^ 2) hτ)
  obtain ⟨hw, he⟩ := cuspProfile_indicator_norm_integral b (hi.congr hnorm)
  refine ⟨hw, ?_⟩
  rw [cuspProfile_modular_norm_sq]
  exact (integral_congr_ae hnorm).trans he

/-- The zero horizontal component and literal vertical representative determine
the actual gradient norm and ordinary derivative-energy integrability. -/
theorem cuspProfile_form_gradient_norm_sq_of_ae (u : FormDomain) (b : ℝ → ℂ)
    (hx : (formGradient u).ofLp.1 = 0)
    (hy : (formGradient u).ofLp.2 =ᵐ[modularMeasure]
      (fun τ : UpperHalfPlane =>
        if 1 < τ.im then (τ.im : ℂ) * deriv b τ.im else 0)) :
    IntegrableOn (fun y : ℝ => ‖deriv b y‖ ^ 2) (Ioi 1) ∧
      ‖formGradient u‖ ^ 2 = ∫ y : ℝ in Ioi 1, ‖deriv b y‖ ^ 2 := by
  let d : ℝ → ℂ := fun y => (y : ℂ) * deriv b y
  have hm := Lp.memLp (formGradient u).ofLp.2
  have hi := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
  have hnorm := hy.mono (fun τ hτ => congrArg (fun z : ℂ => ‖z‖ ^ 2) hτ)
  obtain ⟨hw, he⟩ := cuspProfile_indicator_norm_integral d (hi.congr hnorm)
  have hcancel : (fun y : ℝ => ‖d y‖ ^ 2 / y ^ 2)
      =ᵐ[volume.restrict (Ioi (1 : ℝ))] (fun y => ‖deriv b y‖ ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hyne : y ≠ 0 := ne_of_gt (zero_lt_one.trans hy)
    simp only [d, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    field_simp
  refine ⟨hw.congr hcancel, ?_⟩
  rw [WithLp.prod_norm_sq_eq_of_L2]
  change ‖(formGradient u).ofLp.1‖ ^ 2 + ‖(formGradient u).ofLp.2‖ ^ 2 = _
  rw [hx, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add,
    cuspProfile_modular_norm_sq]
  exact (integral_congr_ae hnorm).trans (he.trans (integral_congr_ae hcancel))

/-- The existing form-domain vector has exactly the weighted scalar H¹ norm.
Both ordinary scalar integrals are proved integrable from the actual L²
representatives, without a smoothness or support-gap premise. -/
theorem cuspProfile_form_norm_sq_of_ae (u : FormDomain) (b : ℝ → ℂ)
    (hvalue : formEmbedding u =ᵐ[modularMeasure]
      (fun τ : UpperHalfPlane => if 1 < τ.im then b τ.im else 0))
    (hx : (formGradient u).ofLp.1 = 0)
    (hy : (formGradient u).ofLp.2 =ᵐ[modularMeasure]
      (fun τ : UpperHalfPlane =>
        if 1 < τ.im then (τ.im : ℂ) * deriv b τ.im else 0)) :
    IntegrableOn (fun y : ℝ => ‖b y‖ ^ 2 / y ^ 2) (Ioi 1) ∧
      IntegrableOn (fun y : ℝ => ‖deriv b y‖ ^ 2) (Ioi 1) ∧
      ‖u‖ ^ 2 = (∫ y : ℝ in Ioi 1, ‖b y‖ ^ 2 / y ^ 2) +
        ∫ y : ℝ in Ioi 1, ‖deriv b y‖ ^ 2 := by
  obtain ⟨hm, hmass⟩ := cuspProfile_form_value_norm_sq_of_ae u b hvalue
  obtain ⟨he, henergy⟩ := cuspProfile_form_gradient_norm_sq_of_ae u b hx hy
  exact ⟨hm, he, by rw [formDomain_norm_sq, hmass, henergy]⟩

end GapFamily.Analytic
