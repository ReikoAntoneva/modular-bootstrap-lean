import GapFamily.Analytic.Poincare.Seed.PoincareSeriesWeakEquation
import GapFamily.Analytic.Poincare.Seed.PoincareSeriesSmooth
import GapFamily.Analytic.Elliptic.ContinuousWeakZero

/-! Pointwise equation deduced from the actual smooth convergent series and ordinary weak identity. -/
noncomputable section
namespace GapFamily.Analytic.PoincareWeak
open Set MeasureTheory UpperHalfPlane LaplacianCovariance
open scoped ContDiff

/-- The literal directional derivative is smooth on an open region. -/
theorem directional_contDiffOn_of_isOpen {U : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (v : ℂ) :
    ContDiffOn ℝ ∞ (fun z => fderiv ℝ f z v) U :=
  (hf.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const

/-- The actual negative hyperbolic Laplacian preserves local smoothness. -/
theorem ordinaryHyperbolicLaplacian_contDiffOn_of_isOpen {U : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) :
    ContDiffOn ℝ ∞ (ordinaryHyperbolicLaplacian f) U :=
  ((Complex.imCLM.contDiff.pow 2).neg).contDiffOn.smul
    ((directional_contDiffOn_of_isOpen hU
      (directional_contDiffOn_of_isOpen hU hf 1) 1).add
    (directional_contDiffOn_of_isOpen hU
      (directional_contDiffOn_of_isOpen hU hf Complex.I) Complex.I))

/-- The genuine smooth common-region Poincaré series satisfies its pointwise equation.
The proof uses the already convergent compact-test identity and the continuous
fundamental lemma, without differentiating an infinite second-derivative series. -/
theorem ordinaryHyperbolicLaplacian_complexPoincareSeries_zero
    (J : ℤ) {s : ℂ} (hs : 1 < s.re) (τ : UpperHalfPlane) :
    ordinaryHyperbolicLaplacian
      (fun z : ℂ => complexPoincareSeries 0 J s (ofComplex z)) τ -
      s * (1 - s) * complexPoincareSeries 0 J s τ =
      (2 * (Real.pi : ℂ) * (J : ℂ)) ^ 2 * complexPoincareSeries 0 J (s + 2) τ := by
  let F : ℂ → ℂ := fun z => complexPoincareSeries 0 J s (ofComplex z)
  let G : ℂ → ℂ := fun z => complexPoincareSeries 0 J (s + 2) (ofComplex z)
  let a : ℂ := s * (1 - s)
  let b : ℂ := (2 * (Real.pi : ℂ) * (J : ℂ)) ^ 2
  have hshift : 1 < (s + 2).re := by norm_num [Complex.add_re]; linarith
  have hF : ContDiffOn ℝ ∞ F upperHalfPlaneSet :=
    PoincareSeriesSmooth.contDiffOn_complexPoincareSeries J hs
  have hG : ContDiffOn ℝ ∞ G upperHalfPlaneSet :=
    PoincareSeriesSmooth.contDiffOn_complexPoincareSeries J hshift
  let R : ℂ → ℂ := fun z =>
    (ordinaryHyperbolicLaplacian F z - a * F z - b * G z) / (z.im : ℂ)^2
  have hR : ContinuousOn R upperHalfPlaneSet :=
    (((ordinaryHyperbolicLaplacian_contDiffOn_of_isOpen isOpen_upperHalfPlaneSet hF).continuousOn.sub
      (continuousOn_const.mul hF.continuousOn)).sub
      (continuousOn_const.mul hG.continuousOn)).div
      ((Complex.continuous_ofReal.comp Complex.continuous_im).pow 2).continuousOn
      (fun z hz => pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (ne_of_gt hz)))
  have hzero : EqOn R 0 upperHalfPlaneSet := by
    apply eqOn_zero_of_continuousOn_integral_contDiff_smul_eq_zero isOpen_upperHalfPlaneSet hR
    intro g hg hc hgu
    let ψ : ℂ → ℂ := fun z => (g z : ℂ)
    have hψ : ContDiff ℝ ∞ ψ := Complex.ofRealCLM.contDiff.comp hg
    have hψc : HasCompactSupport ψ := hc.comp_left Complex.ofReal_zero
    have hψu : tsupport ψ ⊆ upperHalfPlaneSet :=
      (tsupport_comp_subset (f := g) (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero).trans hgu
    have hi := PoincareGreen.hyperbolic_green_test_integrable ψ hψ hψc hψu F hF
    have hj := poincare_weak_equation_integrable ψ hψ hψc hψu J hs
    have heq := integral_poincare_weak_equation ψ hψ hψc hψu J hs
    rw [PoincareGreen.integral_hyperbolic_green_test ψ hψ hψc hψu F hF] at heq
    have hfun : (fun z : ℂ => g z • R z) =
        (fun z => star (ψ z) * ordinaryHyperbolicLaplacian F z / (z.im : ℂ)^2 -
          a * (star (ψ z) * F z / (z.im : ℂ)^2) -
          b * (star (ψ z) * G z / (z.im : ℂ)^2)) := by
      funext z
      simp only [R, ψ, Complex.real_smul, Complex.star_def, Complex.conj_ofReal]
      ring
    have hFi : Integrable (fun z : ℂ => a * (star (ψ z) * F z / (z.im : ℂ)^2)) := hj.2.1.const_mul a
    have hGi : Integrable (fun z : ℂ => b * (star (ψ z) * G z / (z.im : ℂ)^2)) := hj.2.2.const_mul b
    have hsub : Integrable (fun z : ℂ =>
        star (ψ z) * ordinaryHyperbolicLaplacian F z / (z.im : ℂ)^2 -
        a * (star (ψ z) * F z / (z.im : ℂ)^2)) := hi.2.sub hFi
    rw [hfun]
    rw [integral_sub hsub hGi, integral_sub hi.2 hFi,
      integral_const_mul, integral_const_mul]
    change _ - a * _ - b * _ = 0
    change _ = a * _ + b * _ at heq
    rw [heq]
    ring
  have hτ := hzero (x := (τ : ℂ)) τ.im_pos
  dsimp only [R, Pi.zero_apply] at hτ
  have hz : (ordinaryHyperbolicLaplacian F τ - a * F τ - b * G τ) = 0 :=
    (div_eq_zero_iff.mp hτ).resolve_right
      (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr τ.im_pos.ne'))
  simpa only [F, G, a, b, ofComplex_apply] using sub_eq_zero.mp hz

end GapFamily.Analytic.PoincareWeak
