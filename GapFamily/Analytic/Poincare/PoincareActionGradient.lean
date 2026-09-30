import GapFamily.Analytic.Modular.Geometry.ModularSeamEnergy
import GapFamily.Analytic.Poincare.PoincareAnalytic

noncomputable section
namespace GapFamily.Analytic.PoincareActionGradient
open Set Filter
open scoped Topology MatrixGroups

/-- The actual ambient modular action, agreeing with the upper-half-plane action. -/
def modularAction (γ : SL(2, ℤ)) (z : ℂ) : ℂ :=
  ((γ • UpperHalfPlane.ofComplex z : UpperHalfPlane) : ℂ)

@[simp] theorem modularAction_apply (γ : SL(2, ℤ)) (τ : UpperHalfPlane) :
    modularAction γ τ = ((γ • τ : UpperHalfPlane) : ℂ) := by
  simp [modularAction]

/-- The conformal derivative scale is exactly the ratio of the two heights. -/
theorem im_mul_norm_action_scale (γ : SL(2, ℤ)) (τ : UpperHalfPlane) :
    τ.im * ‖1 / UpperHalfPlane.denom γ τ ^ 2‖ = (γ • τ).im := by
  rw [ModularGroup.im_smul_eq_div_normSq, Complex.normSq_eq_norm_sq,
    norm_div, norm_one, norm_pow]
  ring

/-- A chain rule for any genuinely differentiable target function. -/
theorem fderiv_comp_modularAction (F : ℂ → ℂ) (γ : SL(2, ℤ)) (τ : UpperHalfPlane)
    (hF : DifferentiableAt ℝ F ((γ • τ : UpperHalfPlane) : ℂ)) (v : ℂ) :
    fderiv ℝ (F ∘ modularAction γ) τ v =
      fderiv ℝ F ((γ • τ : UpperHalfPlane) : ℂ)
        (v * (1 / UpperHalfPlane.denom γ τ ^ 2)) := by
  have hD : HasFDerivAt F (fderiv ℝ F ((γ • τ : UpperHalfPlane) : ℂ))
      (modularAction γ τ) := by
    simpa only [modularAction_apply] using hF.hasFDerivAt
  have hcomp := hD.comp (τ : ℂ) (ModularGradient.hasFDerivAt_modularAction γ τ)
  exact congrArg (fun A : ℂ →L[ℝ] ℂ => A v) hcomp.fderiv

/-- Hyperbolic-frame first-derivative bounds transport without a loss factor. -/
theorem frame_derivative_comp_le (F : ℂ → ℂ) (γ : SL(2, ℤ)) (τ : UpperHalfPlane)
    (hF : DifferentiableAt ℝ F ((γ • τ : UpperHalfPlane) : ℂ))
    (C : ℝ) (hC : ∀ v : ℂ,
      (γ • τ).im * ‖fderiv ℝ F ((γ • τ : UpperHalfPlane) : ℂ) v‖ ≤ C * ‖v‖)
    (v : ℂ) :
    τ.im * ‖fderiv ℝ (F ∘ modularAction γ) τ v‖ ≤ C * ‖v‖ := by
  let d : ℂ := 1 / UpperHalfPlane.denom γ τ ^ 2
  have hd : 0 < ‖d‖ := by
    have hheight := im_mul_norm_action_scale γ τ
    change τ.im * ‖d‖ = (γ • τ).im at hheight
    nlinarith [τ.im_pos, (γ • τ).im_pos, norm_nonneg d]
  have hbound := hC (v * d)
  rw [norm_mul, ← im_mul_norm_action_scale γ τ] at hbound
  rw [fderiv_comp_modularAction F γ τ hF v]
  change τ.im * ‖fderiv ℝ F ((γ • τ : UpperHalfPlane) : ℂ) (v * d)‖ ≤ C * ‖v‖
  apply (mul_le_mul_iff_right₀ hd).mp
  nlinarith [hbound]

/-- One summable scalar majorant controls the explicit frame bound on a compact
spatial set and a bounded exponent strip. No spatial fundamental-domain restriction occurs. -/
theorem exists_seed_frame_majorant (J : ℤ) {a b S : ℝ}
    (ha : 1 < a) (hab : a ≤ b) (hS : 0 ≤ S)
    {K : Set UpperHalfPlane} (hK : IsCompact K) :
    ∃ u : CuspCoset → ℝ, Summable u ∧ (∀ q, 0 ≤ u q) ∧
      ∀ (q : CuspCoset) (s : ℂ) (τ : UpperHalfPlane),
        a ≤ s.re → s.re ≤ b → ‖s‖ ≤ S → τ ∈ K →
        (‖s‖ + 2 * Real.pi * |(J : ℝ)| * (q.out • τ).im) *
          (q.out • τ).im ^ s.re ≤ u q := by
  obtain ⟨M, hM, u, hu, hu0, hqu⟩ := exists_cusp_height_compact_majorant hK ha
  obtain ⟨_, _, v, hv, hv0, hqv⟩ :=
    exists_cusp_height_compact_majorant hK (ha.trans_le hab)
  let C : ℝ := S + 2 * Real.pi * |(J : ℝ)| * M
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨fun q => C * (u q + v q), (hu.add hv).mul_left C,
    fun q => mul_nonneg hC (add_nonneg (hu0 q) (hv0 q)), ?_⟩
  intro q s τ hsa hsb hsS hτ
  have hcoeff : ‖s‖ + 2 * Real.pi * |(J : ℝ)| * (q.out • τ).im ≤ C := by
    dsimp [C]
    exact add_le_add hsS (mul_le_mul_of_nonneg_left (hqu q τ hτ).1 (by positivity))
  have hpowers : (q.out • τ).im ^ s.re ≤ u q + v q :=
    (rpow_le_add_endpoint (q.out • τ).im_pos hsa hsb).trans
      (add_le_add (hqu q τ hτ).2 (hqv q τ hτ).2)
  exact mul_le_mul hcoeff hpowers (Real.rpow_nonneg (q.out • τ).im_pos.le _) hC

end GapFamily.Analytic.PoincareActionGradient
