import GapFamily.Analytic.Cusp.Scalar.CuspConstantResponseForm

/-!
# The explicit actual vertical gradient of the constant response

The square-root coordinate derivative cancels the half-potential term of the
logarithmic response. The resulting outgoing exponential is the representative
of the actual closed vertical gradient on the physical half-plane.
-/

noncomputable section
namespace GapFamily.Analytic

open MeasureTheory ModularGradient

/-- The physical vertical-gradient profile, including the removable parameter. -/
theorem cuspConstantPhysicalResponse_mul_deriv {κ : ℂ}
    (hm : κ ≠ -(1 / 2 : ℂ)) {y : ℝ} (hy : 0 < y) :
    (y : ℂ) * deriv (cuspConstantPhysicalResponse κ) y =
      Real.sqrt y • (Complex.exp (-κ * (Real.log y : ℂ)) / (κ + 1 / 2)) := by
  have hd : Differentiable ℝ (cuspConstantLogResponse κ) :=
    fun t => (hasDerivAt_cuspConstantLogResponse hm t).differentiableAt
  have hhalf : deriv (cuspConstantLogResponse κ) (Real.log y) +
      (1 / 2 : ℝ) • cuspConstantLogResponse κ (Real.log y) =
        Complex.exp (-κ * (Real.log y : ℂ)) / (κ + 1 / 2) := by
    simpa only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat] using deriv_cuspConstantLogResponse_add_half hm (Real.log y)
  have hs : Real.sqrt y ≠ 0 := (Real.sqrt_pos.mpr hy).ne'
  have hcoef : y * (Real.sqrt y)⁻¹ = Real.sqrt y := by
    field_simp
    nlinarith [Real.sq_sqrt hy.le]
  rw [cuspConstantPhysicalResponse, deriv_cuspLift hd hy, hhalf,
    ← Complex.real_smul, smul_smul, hcoef]

/-- The actual closed vertical-gradient class has the explicit outgoing
exponential representative above height one and zero below. -/
theorem cuspConstantForm_gradient_snd_exp_ae {κ : ℂ} (hκ : 0 < κ.re) :
    (formGradient (cuspConstantForm hκ)).ofLp.2 =ᵐ[modularMeasure]
      (fun τ : UpperHalfPlane => if 1 < τ.im then
        Real.sqrt τ.im •
          (Complex.exp (-κ * (Real.log τ.im : ℂ)) / (κ + 1 / 2)) else 0) := by
  have hm : κ ≠ -(1 / 2 : ℂ) := by
    intro h
    subst κ
    norm_num at hκ
  apply (cuspConstantForm_gradient_snd_ae hκ).trans
  exact Filter.Eventually.of_forall fun τ => by
    dsimp only
    rw [cuspConstantPhysicalResponse_mul_deriv hm τ.im_pos]

end GapFamily.Analytic
