import GapFamily.Analytic.Modular.ModularGradientCore
import GapFamily.Analytic.Modular.Geometry.ModularSeamLinear
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold

/-!
# Actual gradient energy across modular seams

The two real frame derivatives rotate under the modular action. Their summed
squared norm is invariant at every upper-half-plane point, including points
on the boundary of the chosen fundamental domain.
-/

noncomputable section

namespace GapFamily.Analytic.ModularGradient

open Set MeasureTheory UpperHalfPlane
open scoped ContDiff MatrixGroups Topology

/-- The full Euclidean derivative energy, without a holomorphy assumption. -/
def euclideanEnergy (F : ℂ → ℂ) (z : ℂ) : ℝ :=
  ‖fderiv ℝ F z 1‖ ^ 2 + ‖fderiv ℝ F z Complex.I‖ ^ 2

/-- The actual squared norm of the two-component hyperbolic frame gradient. -/
def frameEnergy (F : ℂ → ℂ) (τ : UpperHalfPlane) : ℝ :=
  ‖directional F 1 τ‖ ^ 2 + ‖directional F Complex.I τ‖ ^ 2

theorem frameEnergy_eq_im_sq_mul (F : ℂ → ℂ) (τ : UpperHalfPlane) :
    frameEnergy F τ = τ.im ^ 2 * euclideanEnergy F τ := by
  simp only [frameEnergy, euclideanEnergy, directional, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, mul_pow, sq_abs]
  ring

/-- The built-in real derivative of the actual modular action, specialized to
determinant one. -/
theorem hasFDerivAt_modularAction (γ : SL(2, ℤ)) (τ : UpperHalfPlane) :
    HasFDerivAt (fun z : ℂ => ((γ • UpperHalfPlane.ofComplex z : UpperHalfPlane) : ℂ))
      ((ContinuousLinearMap.toSpanSingleton ℂ
        (1 / UpperHalfPlane.denom γ τ ^ 2)).restrictScalars ℝ) τ := by
  simpa [UpperHalfPlane.smulFDeriv, UpperHalfPlane.σ] using
    (UpperHalfPlane.hasStrictFDerivAt_smul (γ : GL (Fin 2) ℝ) τ).hasFDerivAt

/-- Differentiate the literal automorphy identity on an actual open neighborhood. -/
theorem fderiv_core_modularAction (F : smoothCore) (γ : SL(2, ℤ))
    (τ : UpperHalfPlane) (v : ℂ) :
    fderiv ℝ F.val τ v =
      fderiv ℝ F.val (γ • τ : UpperHalfPlane)
        ((1 / UpperHalfPlane.denom γ τ ^ 2) * v) := by
  let G : ℂ → ℂ := fun z => ((γ • UpperHalfPlane.ofComplex z : UpperHalfPlane) : ℂ)
  have hcomp : HasFDerivAt (F.val ∘ G)
      ((fderiv ℝ F.val (γ • τ : UpperHalfPlane)).comp
        ((ContinuousLinearMap.toSpanSingleton ℂ
          (1 / UpperHalfPlane.denom γ τ ^ 2)).restrictScalars ℝ)) τ := by
    have hF : HasFDerivAt F.val (fderiv ℝ F.val (γ • τ : UpperHalfPlane)) (G τ) := by
      simpa only [G, UpperHalfPlane.ofComplex_apply] using
        (smooth_differentiableAt F.property.1 (γ • τ)).hasFDerivAt
    exact hF.comp (τ : ℂ) (hasFDerivAt_modularAction γ τ)
  have hgerm : F.val ∘ G =ᶠ[𝓝 (τ : ℂ)] F.val := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with z hz
    simpa only [Function.comp_apply, G, UpperHalfPlane.ofComplex_apply_of_im_pos hz] using
      F.property.2.1 γ (⟨z, hz⟩ : UpperHalfPlane)
  have hd := congrArg (fun L : ℂ →L[ℝ] ℂ => L v)
    ((hcomp.congr_of_eventuallyEq hgerm.symm).fderiv)
  change fderiv ℝ F.val τ v =
    fderiv ℝ F.val (γ • τ : UpperHalfPlane) (v * (1 / UpperHalfPlane.denom γ τ ^ 2)) at hd
  simpa only [mul_comm] using hd

/-- Euclidean energy transforms by the squared conformal scale. -/
theorem euclideanEnergy_modularAction (F : smoothCore) (γ : SL(2, ℤ))
    (τ : UpperHalfPlane) :
    euclideanEnergy F.val τ =
      ‖1 / UpperHalfPlane.denom γ τ ^ 2‖ ^ 2 *
        euclideanEnergy F.val (γ • τ : UpperHalfPlane) := by
  unfold euclideanEnergy
  rw [fderiv_core_modularAction F γ τ 1, fderiv_core_modularAction F γ τ Complex.I,
    mul_one]
  exact norm_sq_apply_add_norm_sq_apply_mul_I _ _

/-- Exact pointwise invariance of the complete hyperbolic gradient energy.
This includes every seam point; no fundamental-domain interior premise occurs. -/
theorem frameEnergy_modularAction (F : smoothCore) (γ : SL(2, ℤ))
    (τ : UpperHalfPlane) :
    frameEnergy F.val (γ • τ) = frameEnergy F.val τ := by
  rw [frameEnergy_eq_im_sq_mul, frameEnergy_eq_im_sq_mul,
    ModularGroup.im_smul_eq_div_normSq, euclideanEnergy_modularAction F γ τ,
    Complex.normSq_eq_norm_sq, norm_div, norm_one, norm_pow]
  ring

end GapFamily.Analytic.ModularGradient
