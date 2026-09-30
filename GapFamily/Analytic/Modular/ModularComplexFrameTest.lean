import GapFamily.Analytic.Modular.ModularGradientWeak

/-!
# Complex compact tests for the actual closed modular gradient

Real and imaginary parts of genuine compact tests give actual complex frame
and divergence vectors. Their pairing identities retain the proved closed
modular gradient and compact interior support.
-/

noncomputable section
namespace GapFamily.Analytic.ModularGradient
open Set MeasureTheory UpperHalfPlane
open scoped ContDiff

private theorem complexTest_re_contDiff (φ : ℂ → ℂ) (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (fun z => (φ z).re) := Complex.reCLM.contDiff.comp hφ

private theorem complexTest_im_contDiff (φ : ℂ → ℂ) (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (fun z => (φ z).im) := Complex.imCLM.contDiff.comp hφ

private theorem complexTest_re_compact (φ : ℂ → ℂ) (hc : HasCompactSupport φ) :
    HasCompactSupport (fun z => (φ z).re) := hc.comp_left Complex.zero_re

private theorem complexTest_im_compact (φ : ℂ → ℂ) (hc : HasCompactSupport φ) :
    HasCompactSupport (fun z => (φ z).im) := hc.comp_left Complex.zero_im

/-- The actual complex frame test with representative `y φ`. -/
def complexFrameTest (φ : ℂ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) : ModularHilbert :=
  frameTest (fun z => (φ z).re) (complexTest_re_contDiff φ hφ) (complexTest_re_compact φ hc) +
    Complex.I • frameTest (fun z => (φ z).im) (complexTest_im_contDiff φ hφ)
      (complexTest_im_compact φ hc)

/-- The actual complex divergence test with representative `-y² ∂ᵥφ`. -/
def complexDivergenceTest (φ : ℂ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (v : ℂ) : ModularHilbert :=
  divergenceTest (fun z => (φ z).re) (complexTest_re_contDiff φ hφ)
      (complexTest_re_compact φ hc) v +
    Complex.I • divergenceTest (fun z => (φ z).im) (complexTest_im_contDiff φ hφ)
      (complexTest_im_compact φ hc) v

theorem complexFrameTest_ae (φ : ℂ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) :
    complexFrameTest φ hφ hc =ᵐ[modularMeasure]
      (fun τ : UpperHalfPlane => (τ.im : ℂ) * φ τ) := by
  let fr := frameTest (fun z => (φ z).re) (complexTest_re_contDiff φ hφ)
    (complexTest_re_compact φ hc)
  let fi := frameTest (fun z => (φ z).im) (complexTest_im_contDiff φ hφ)
    (complexTest_im_compact φ hc)
  filter_upwards [Lp.coeFn_add fr (Complex.I • fi), Lp.coeFn_smul Complex.I fi,
    frameTest_ae (fun z => (φ z).re) (complexTest_re_contDiff φ hφ)
      (complexTest_re_compact φ hc),
    frameTest_ae (fun z => (φ z).im) (complexTest_im_contDiff φ hφ)
      (complexTest_im_compact φ hc)] with τ hadd hsm hr hi
  change (fr + Complex.I • fi) τ = _
  change fr τ = _ at hr
  change fi τ = _ at hi
  simp only [Pi.add_apply] at hadd
  simp only [Pi.smul_apply, smul_eq_mul] at hsm
  rw [hadd, hsm, hr, hi]
  push_cast
  calc
    _ = (τ.im : ℂ) * (((φ τ).re : ℂ) + ((φ τ).im : ℂ) * Complex.I) := by ring
    _ = _ := by rw [Complex.re_add_im]

private theorem complexTest_fderiv_re (φ : ℂ → ℂ) (hφ : ContDiff ℝ ∞ φ) (z v : ℂ) :
    fderiv ℝ (fun w => (φ w).re) z v = (fderiv ℝ φ z v).re := by
  have h := Complex.reCLM.hasFDerivAt.comp z
    ((hφ.differentiable (by simp) z).hasFDerivAt)
  exact congrArg (fun L : ℂ →L[ℝ] ℝ => L v) h.fderiv

private theorem complexTest_fderiv_im (φ : ℂ → ℂ) (hφ : ContDiff ℝ ∞ φ) (z v : ℂ) :
    fderiv ℝ (fun w => (φ w).im) z v = (fderiv ℝ φ z v).im := by
  have h := Complex.imCLM.hasFDerivAt.comp z
    ((hφ.differentiable (by simp) z).hasFDerivAt)
  exact congrArg (fun L : ℂ →L[ℝ] ℝ => L v) h.fderiv

theorem complexDivergenceTest_ae (φ : ℂ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (v : ℂ) :
    complexDivergenceTest φ hφ hc v =ᵐ[modularMeasure]
      (fun τ : UpperHalfPlane => -((τ.im : ℂ) ^ 2) * fderiv ℝ φ τ v) := by
  let fr := divergenceTest (fun z => (φ z).re) (complexTest_re_contDiff φ hφ)
    (complexTest_re_compact φ hc) v
  let fi := divergenceTest (fun z => (φ z).im) (complexTest_im_contDiff φ hφ)
    (complexTest_im_compact φ hc) v
  filter_upwards [Lp.coeFn_add fr (Complex.I • fi), Lp.coeFn_smul Complex.I fi,
    divergenceTest_ae (fun z => (φ z).re) (complexTest_re_contDiff φ hφ)
      (complexTest_re_compact φ hc) v,
    divergenceTest_ae (fun z => (φ z).im) (complexTest_im_contDiff φ hφ)
      (complexTest_im_compact φ hc) v] with τ hadd hsm hr hi
  change (fr + Complex.I • fi) τ = _
  change fr τ = _ at hr
  change fi τ = _ at hi
  simp only [Pi.add_apply] at hadd
  simp only [Pi.smul_apply, smul_eq_mul] at hsm
  rw [hadd, hsm, hr, hi, complexTest_fderiv_re φ hφ, complexTest_fderiv_im φ hφ]
  push_cast
  calc
    _ = -((τ.im : ℂ) ^ 2) *
        (((fderiv ℝ φ τ v).re : ℂ) + ((fderiv ℝ φ τ v).im : ℂ) * Complex.I) := by ring
    _ = _ := by rw [Complex.re_add_im]

theorem complexFrameTest_closedGradient_pairing_x (φ : ℂ → ℂ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ modularInterior) (u : closedGradient.domain) :
    inner ℂ (complexFrameTest φ hφ hc) (WithLp.ofLp (closedGradient u)).1 =
      inner ℂ (complexDivergenceTest φ hφ hc 1) (u : ModularHilbert) := by
  have hr : tsupport (fun z => (φ z).re) ⊆ modularInterior :=
    (tsupport_comp_subset Complex.zero_re φ).trans hs
  have hi : tsupport (fun z => (φ z).im) ⊆ modularInterior :=
    (tsupport_comp_subset Complex.zero_im φ).trans hs
  simp only [complexFrameTest, complexDivergenceTest, inner_add_left, inner_smul_left,
    frameTest_closedGradient_pairing_x _ _ _ hr,
    frameTest_closedGradient_pairing_x _ _ _ hi]

theorem complexFrameTest_closedGradient_pairing_y (φ : ℂ → ℂ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ modularInterior) (u : closedGradient.domain) :
    inner ℂ (complexFrameTest φ hφ hc) (WithLp.ofLp (closedGradient u)).2 =
      inner ℂ (complexDivergenceTest φ hφ hc Complex.I) (u : ModularHilbert) := by
  have hr : tsupport (fun z => (φ z).re) ⊆ modularInterior :=
    (tsupport_comp_subset Complex.zero_re φ).trans hs
  have hi : tsupport (fun z => (φ z).im) ⊆ modularInterior :=
    (tsupport_comp_subset Complex.zero_im φ).trans hs
  simp only [complexFrameTest, complexDivergenceTest, inner_add_left, inner_smul_left,
    frameTest_closedGradient_pairing_y _ _ _ hr,
    frameTest_closedGradient_pairing_y _ _ _ hi]

end GapFamily.Analytic.ModularGradient
