import GapFamily.Analytic.Spatial.SpatialPointKernelBasic
import GapFamily.Analytic.Geometry.LaplacianMobiusAction

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open UpperHalfPlane Matrix
open scoped MatrixGroups

/-- The determinant-one fractional-linear action has this exact difference. -/
theorem coe_smul_sub_eq_div (γ : SL(2, ℝ)) (z w : UpperHalfPlane) :
    ((γ • z : UpperHalfPlane) : ℂ) - ((γ • w : UpperHalfPlane) : ℂ) =
      ((z : ℂ) - (w : ℂ)) /
        (denom (γ : GL (Fin 2) ℝ) z * denom (γ : GL (Fin 2) ℝ) w) := by
  rw [← LaplacianCovariance.rawRealModularAction_coe,
    ← LaplacianCovariance.rawRealModularAction_coe]
  unfold LaplacianCovariance.rawRealModularAction
  have hd : ((γ : GL (Fin 2) ℝ).val.det : ℝ) = 1 := by simp
  have hc := congrArg Complex.ofReal hd
  simp only [Matrix.det_fin_two, Complex.ofReal_sub, Complex.ofReal_mul,
    Complex.ofReal_one] at hc
  field_simp [denom_ne_zero (γ : GL (Fin 2) ℝ) z,
    denom_ne_zero (γ : GL (Fin 2) ℝ) w]
  simp only [num, denom]
  linear_combination ((z : ℂ) - (w : ℂ)) * hc

/-- Simultaneous covariance uses the pinned full real special-linear action. -/
theorem pointParameter_smul (γ : SL(2, ℝ)) (z w : UpperHalfPlane) :
    pointParameter (γ • z : UpperHalfPlane) (γ • w : UpperHalfPlane) =
      pointParameter (z : ℂ) (w : ℂ) := by
  have hz : (γ • z : UpperHalfPlane).im =
      z.im / Complex.normSq (denom (γ : GL (Fin 2) ℝ) z) := by
    change ((γ : GL (Fin 2) ℝ) • z : UpperHalfPlane).im = _
    simpa using UpperHalfPlane.im_smul_eq_div_normSq (γ : GL (Fin 2) ℝ) z
  have hw : (γ • w : UpperHalfPlane).im =
      w.im / Complex.normSq (denom (γ : GL (Fin 2) ℝ) w) := by
    change ((γ : GL (Fin 2) ℝ) • w : UpperHalfPlane).im = _
    simpa using UpperHalfPlane.im_smul_eq_div_normSq (γ : GL (Fin 2) ℝ) w
  simp only [pointParameter, coe_smul_sub_eq_div, UpperHalfPlane.coe_im,
    hz, hw, map_div₀, map_mul]
  field_simp [normSq_denom_ne_zero (γ : GL (Fin 2) ℝ) z.im_ne_zero,
    normSq_denom_ne_zero (γ : GL (Fin 2) ℝ) w.im_ne_zero]

theorem pointKernel_smul (s : ℂ) (γ : SL(2, ℝ)) (z w : UpperHalfPlane) :
    pointKernel s (γ • z : UpperHalfPlane) (γ • w : UpperHalfPlane) =
      pointKernel s (z : ℂ) (w : ℂ) := by
  rw [pointKernel, pointKernel, pointParameter_smul]

/-- The integer modular action is the actual restriction of the real action. -/
theorem pointKernel_modular_smul (s : ℂ) (γ : SL(2, ℤ)) (z w : UpperHalfPlane) :
    pointKernel s (γ • z : UpperHalfPlane) (γ • w : UpperHalfPlane) =
      pointKernel s (z : ℂ) (w : ℂ) := by
  exact pointKernel_smul s (γ : SL(2, ℝ)) z w

end GapFamily.Analytic.SpatialPoint
