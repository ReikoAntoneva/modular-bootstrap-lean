import GapFamily.Analytic.Cusp.Green.CuspGreenSmoothForm

/-!
# The actual closed gradient of the smooth-source Green response

The ordinary derivative of the logarithmic Green formula gives the vertical
component of the previously constructed form vector.
-/

noncomputable section
namespace GapFamily.Analytic
open Set Filter MeasureTheory ModularGradient
open scoped ContDiff Topology

/-- The actual physical derivative in the scalar cusp coordinate. -/
theorem cuspGreenSmoothPhysical_mul_deriv (T : ℝ) {κ : ℂ} (hκ : κ ≠ 0)
    {f : ℝ → ℂ} (hf : Continuous f) {y : ℝ} (hy : 0 < y) :
    (y : ℂ) * deriv (cuspGreenSmoothPhysical T κ f) y =
      Real.sqrt y •
        (cuspGreenSolutionFormulaDeriv 0 T κ f (Real.log y) +
          (1 / 2 : ℂ) * cuspGreenSolutionFormula 0 T κ f (Real.log y)) := by
  have hd : Differentiable ℝ (cuspGreenSolutionFormula 0 T κ f) :=
    fun t => (hasDerivAt_cuspGreenSolutionFormula 0 T hκ hf t).differentiableAt
  have hs : Real.sqrt y ≠ 0 := (Real.sqrt_pos.mpr hy).ne'
  have hcoef : y * (Real.sqrt y)⁻¹ = Real.sqrt y := by
    field_simp
    nlinarith [Real.sq_sqrt hy.le]
  rw [cuspGreenSmoothPhysical, deriv_cuspLift hd hy,
    deriv_cuspGreenSolutionFormula 0 T hκ hf (Real.log y),
    ← Complex.real_smul, smul_smul, hcoef]
  simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_ofNat]

/-- The horizontal component of the actual completed Green form is zero. -/
theorem cuspGreenSmoothForm_gradient_fst_eq_zero {T : ℝ} (hT : 0 ≤ T)
    {κ : ℂ} (hκ : 0 < κ.re) {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hs : tsupport f ⊆ Ioo 0 T) :
    (formGradient (cuspGreenSmoothForm hT hκ hf hs)).ofLp.1 = 0 :=
  cuspProfileForm_gradient_fst_eq_zero _ _ _ _ _

/-- The vertical gradient of the actual completed form has the differentiated
Green formula as its representative above height one. -/
theorem cuspGreenSmoothForm_gradient_snd_ae {T : ℝ} (hT : 0 ≤ T)
    {κ : ℂ} (hκ : 0 < κ.re) {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hs : tsupport f ⊆ Ioo 0 T) :
    (formGradient (cuspGreenSmoothForm hT hκ hf hs)).ofLp.2 =ᵐ[modularMeasure]
      (fun z : UpperHalfPlane => if 1 < z.im then
        Real.sqrt z.im •
          (cuspGreenSolutionFormulaDeriv 0 T κ f (Real.log z.im) +
            (1 / 2 : ℂ) * cuspGreenSolutionFormula 0 T κ f (Real.log z.im)) else 0) := by
  have hk : κ ≠ 0 := by intro h; simp [h] at hκ
  have he := cuspProfileForm_gradient_snd_ae (cuspGreenSmoothPhysical T κ f)
    (cuspGreenSmoothPhysical_contDiffOn T hk hf)
    (cuspGreenSmoothPhysical_one T κ f)
    (cuspGreenSmoothPhysical_mass_integrable hT hκ hf hs)
    (cuspGreenSmoothPhysical_energy_integrable hT hκ hf hs)
  apply he.trans
  exact Eventually.of_forall fun z => by
    dsimp only
    rw [cuspGreenSmoothPhysical_mul_deriv T hk hf.continuous z.im_pos]

end GapFamily.Analytic
