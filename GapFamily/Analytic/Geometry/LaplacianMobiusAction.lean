import GapFamily.Analytic.Modular.Periodization.ModularPeriodizationAction
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold

noncomputable section

open Set Filter Matrix UpperHalfPlane
open scoped MatrixGroups Topology

namespace GapFamily.Analytic.LaplacianCovariance

/-- Literal fractional-linear action on the ambient complex plane. -/
def rawRealModularAction (γ : SL(2, ℝ)) (z : ℂ) : ℂ :=
  UpperHalfPlane.num (γ : GL (Fin 2) ℝ) z /
    UpperHalfPlane.denom (γ : GL (Fin 2) ℝ) z

theorem rawRealModularAction_coe (γ : SL(2, ℝ)) (τ : UpperHalfPlane) :
    rawRealModularAction γ (τ : ℂ) = (γ • τ : UpperHalfPlane) := by
  exact (UpperHalfPlane.coe_smul_of_det_pos
    (g := (γ : GL (Fin 2) ℝ)) (by simp) τ).symm

theorem rawRealModularAction_germ (γ : SL(2, ℝ)) (τ : UpperHalfPlane) :
    rawRealModularAction γ =ᶠ[𝓝 (τ : ℂ)]
      (fun z : ℂ => ((γ : GL (Fin 2) ℝ) • UpperHalfPlane.ofComplex z : UpperHalfPlane)) := by
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with z hz
  simpa only [UpperHalfPlane.ofComplex_apply_of_im_pos hz, rawRealModularAction] using
    (UpperHalfPlane.coe_smul_of_det_pos
      (g := (γ : GL (Fin 2) ℝ)) (by simp) (⟨z, hz⟩ : UpperHalfPlane)).symm

theorem hasStrictDerivAt_rawRealModularAction (γ : SL(2, ℝ)) (τ : UpperHalfPlane) :
    HasStrictDerivAt (rawRealModularAction γ)
      (1 / UpperHalfPlane.denom (γ : GL (Fin 2) ℝ) τ ^ 2) τ := by
  simpa using (UpperHalfPlane.hasStrictDerivAt_smul
    (g := (γ : GL (Fin 2) ℝ)) (by simp) τ).congr_of_eventuallyEq
      (rawRealModularAction_germ γ τ).symm

theorem deriv_rawRealModularAction (γ : SL(2, ℝ)) (τ : UpperHalfPlane) :
    deriv (rawRealModularAction γ) τ =
      1 / UpperHalfPlane.denom (γ : GL (Fin 2) ℝ) τ ^ 2 :=
  (hasStrictDerivAt_rawRealModularAction γ τ).hasDerivAt.deriv

theorem analyticAt_rawRealModularAction (γ : SL(2, ℝ)) (τ : UpperHalfPlane) :
    AnalyticAt ℂ (rawRealModularAction γ) τ := by
  exact (UpperHalfPlane.analyticAt_smul
    (g := (γ : GL (Fin 2) ℝ)) (by simp) τ).congr
      (rawRealModularAction_germ γ τ).symm

theorem hyperbolic_scale_rawRealModularAction (γ : SL(2, ℝ)) (τ : UpperHalfPlane) :
    τ.im ^ 2 * ‖deriv (rawRealModularAction γ) τ‖ ^ 2 =
      (γ • τ : UpperHalfPlane).im ^ 2 := by
  have him : (γ • τ : UpperHalfPlane).im =
      τ.im / Complex.normSq (UpperHalfPlane.denom (γ : GL (Fin 2) ℝ) τ) := by
    change ((γ : GL (Fin 2) ℝ) • τ : UpperHalfPlane).im = _
    simpa using UpperHalfPlane.im_smul_eq_div_normSq (γ : GL (Fin 2) ℝ) τ
  rw [deriv_rawRealModularAction, him, Complex.normSq_eq_norm_sq,
    norm_div, norm_one, norm_pow]
  ring

theorem rawRealModularAction_int (γ : SL(2, ℤ)) :
    rawRealModularAction (γ : SL(2, ℝ)) = rawModularAction γ := rfl

end GapFamily.Analytic.LaplacianCovariance
