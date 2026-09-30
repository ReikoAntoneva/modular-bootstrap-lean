import GapFamily.Analytic.Cusp.Profile.CuspUnboundedProfileSmooth
import GapFamily.Analytic.Foundation.FormTruncationScalar
import GapFamily.Analytic.Modular.ModularFiniteHeightCore
import GapFamily.Analytic.Cusp.Profile.CuspProfileCore

noncomputable section
namespace GapFamily.Analytic.FormTruncation
open Set MeasureTheory UpperHalfPlane ModularGradient Filter
open scoped ContDiff MatrixGroups Topology

/-- Explicit smooth invariant low-cusp cutoff. -/
def truncationMultiplier (n : ℕ) (z : ℂ) : ℂ :=
  1 - modularPeriodization (cuspProfileSeed (highProfile n)) z

theorem truncationMultiplier_contDiffOn (n : ℕ) :
    ContDiffOn ℝ ∞ (truncationMultiplier n) upperHalfPlaneSet :=
  contDiffOn_const.sub (contDiffOn_modularPeriodization_cuspProfileSeed
    (highProfile_contDiff n) (highProfile_tsupport_subset n))

theorem truncationMultiplier_invariant (n : ℕ) (γ : SL(2, ℤ)) (τ : UpperHalfPlane) :
    truncationMultiplier n (γ • τ : UpperHalfPlane) = truncationMultiplier n τ := by
  simp only [truncationMultiplier, modularPeriodization_invariant]

theorem truncationMultiplier_eq_on_fd (n : ℕ) {τ : UpperHalfPlane}
    (hτ : τ ∈ ModularGroup.fd) : truncationMultiplier n τ = lowProfile n τ.im := by
  rw [truncationMultiplier,
    modularPeriodization_cuspProfileSeed_eq_on_fd (highProfile_tsupport_subset n) hτ]
  rfl

/-- Multiplication by the explicit invariant truncation gives an actual smooth core. -/
def truncatedCore (n : ℕ) (F : smoothCore) : smoothCore := by
  refine ⟨fun z => truncationMultiplier n z * F.val z,
    mem_smoothCore_of_finite_height
      ((truncationMultiplier_contDiffOn n).mul F.property.1) ?_ (2 * scale n) ?_⟩
  · intro γ τ
    rw [truncationMultiplier_invariant, F.property.2.1]
  · intro τ hτ ht
    rw [truncationMultiplier_eq_on_fd n hτ, lowProfile_eq_zero_of_ge n ht.le, zero_mul]

theorem truncatedCore_eq_on_fd (n : ℕ) (F : smoothCore) {τ : UpperHalfPlane}
    (hτ : τ ∈ ModularGroup.fd) : (truncatedCore n F).val τ = lowProfile n τ.im * F.val τ := by
  change truncationMultiplier n τ * F.val τ = _
  rw [truncationMultiplier_eq_on_fd n hτ]

theorem truncatedCore_zero_above (n : ℕ) (F : smoothCore) (τ : UpperHalfPlane)
    (hτ : τ ∈ ModularGroup.fd) (ht : 2 * scale n ≤ τ.im) : (truncatedCore n F).val τ = 0 := by
  rw [truncatedCore_eq_on_fd n F hτ, lowProfile_eq_zero_of_ge n ht, zero_mul]

theorem truncatedCore_value_ae (n : ℕ) (F : smoothCore) :
    value (truncatedCore n F) =ᵐ[modularMeasure]
      fun τ : UpperHalfPlane => lowProfile n τ.im * F.val τ := by
  filter_upwards [value_ae (truncatedCore n F), ae_mem_fdo] with τ hv hτ
  rw [hv, truncatedCore_eq_on_fd n F (ModularGroup.fdo_subset_fd hτ)]

theorem truncatedCore_directional_ae (n : ℕ) (F : smoothCore) (v : ℂ) :
    directional (truncatedCore n F).val v =ᵐ[modularMeasure]
      fun τ : UpperHalfPlane => lowProfile n τ.im * directional F.val v τ -
        (τ.im : ℂ) * (v.im • deriv (highProfile n) τ.im) * F.val τ := by
  let G : ℂ → ℂ := fun z => lowProfile n z.im * F.val z
  have hg : ContDiffOn ℝ ∞ G upperHalfPlaneSet :=
    ((lowProfile_contDiff n).comp Complex.imCLM.contDiff).contDiffOn.mul F.property.1
  have heq : (fun τ : UpperHalfPlane => (truncatedCore n F).val τ) =ᵐ[modularMeasure]
      (fun τ : UpperHalfPlane => G τ) := by
    filter_upwards [ae_mem_fdo] with τ hτ
    exact truncatedCore_eq_on_fd n F (ModularGroup.fdo_subset_fd hτ)
  have hdir := modularDirectional_ae_eq
    ((truncatedCore n F).property.1.continuousOn.mono
      (fun _ hz => im_pos_of_mem_modularInterior hz))
    (hg.continuousOn.mono (fun _ hz => im_pos_of_mem_modularInterior hz)) heq v
  apply hdir.trans
  apply Eventually.of_forall
  intro τ
  have hl : DifferentiableAt ℝ (fun z : ℂ => lowProfile n z.im) τ :=
    (((lowProfile_contDiff n).comp Complex.imCLM.contDiff).differentiable (by simp)) τ
  have hd := (((lowProfile_contDiff n).differentiable (by simp)) τ.im).hasFDerivAt.comp
    (τ : ℂ) Complex.imCLM.hasFDerivAt
  have hdv : fderiv ℝ (fun z : ℂ => lowProfile n z.im) τ v =
      -(v.im • deriv (highProfile n) τ.im) := by
    change fderiv ℝ (lowProfile n ∘ Complex.im) τ v = _
    rw [hd.fderiv]
    change fderiv ℝ (lowProfile n) τ.im v.im = _
    rw [fderiv_eq_smul_deriv]
    have hdlo : deriv (lowProfile n) τ.im = -deriv (highProfile n) τ.im := deriv_const_sub 1
    rw [hdlo, smul_neg]
  change (τ.im : ℂ) * fderiv ℝ G τ v = _
  rw [show G = (fun z : ℂ => lowProfile n z.im) * F.val by rfl,
    fderiv_mul hl (smooth_differentiableAt F.property.1 τ)]
  simp only [add_apply, smul_apply,
    smul_eq_mul, hdv, directional, UpperHalfPlane.coe_im]
  ring

theorem truncatedCore_xComponent_ae (n : ℕ) (F : smoothCore) :
    xComponent (truncatedCore n F) =ᵐ[modularMeasure]
      fun τ : UpperHalfPlane => lowProfile n τ.im * directional F.val 1 τ := by
  have h := (component_ae 1 (fun G => G.property.2.2.2.1) (truncatedCore n F)).trans
    (truncatedCore_directional_ae n F 1)
  simpa only [xComponent, Complex.one_im, zero_smul, mul_zero, zero_mul, sub_zero] using h

theorem truncatedCore_yComponent_ae (n : ℕ) (F : smoothCore) :
    yComponent (truncatedCore n F) =ᵐ[modularMeasure]
      fun τ : UpperHalfPlane => lowProfile n τ.im * directional F.val Complex.I τ -
        ((τ.im : ℂ) * deriv (highProfile n) τ.im) * F.val τ := by
  have h := (component_ae Complex.I (fun G => G.property.2.2.2.2) (truncatedCore n F)).trans
    (truncatedCore_directional_ae n F Complex.I)
  simpa only [yComponent, Complex.I_im, one_smul] using h

end GapFamily.Analytic.FormTruncation
