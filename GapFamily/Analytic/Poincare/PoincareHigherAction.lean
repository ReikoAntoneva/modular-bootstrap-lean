import GapFamily.Analytic.Geometry.MobiusHigherBound
import GapFamily.Analytic.Poincare.PoincareTermRegularity

noncomputable section
namespace GapFamily.Analytic.PoincareHigherComposition
open Set UpperHalfPlane PoincareActionGradient PoincareTermRegularity
open scoped MatrixGroups

/-- The existing ambient action and the rational action agree on the actual upper half-plane. -/
theorem modularAction_eqOn_raw (γ : SL(2, ℤ)) :
    EqOn (modularAction γ) (rawModularAction γ) upperHalfPlaneSet := by
  intro z hz
  have h := rawModularAction_coe γ (⟨z, hz⟩ : UpperHalfPlane)
  simpa only [modularAction, UpperHalfPlane.ofComplex_apply_of_im_pos hz] using h.symm

/-- All actual real derivatives are independent of the ambient extension below the upper half-plane. -/
theorem iteratedFDeriv_modularAction_eq_raw (γ : SL(2, ℤ)) (τ : UpperHalfPlane) (n : ℕ) :
    iteratedFDeriv ℝ n (modularAction γ) τ = iteratedFDeriv ℝ n (rawModularAction γ) τ := by
  have h := iteratedFDerivWithin_congr (𝕜 := ℝ) (modularAction_eqOn_raw γ) τ.im_pos n
  simpa only [iteratedFDerivWithin_of_isOpen n isOpen_upperHalfPlaneSet τ.im_pos] using h

/-- The canonical ambient action used by the existing Poincaré terms retains the exact height bound. -/
theorem norm_iteratedFDeriv_modularAction_le (γ : SL(2, ℤ)) (τ : UpperHalfPlane)
    (n : ℕ) (hn : 1 ≤ n) :
    ‖iteratedFDeriv ℝ n (modularAction γ) τ‖ ≤
      (n.factorial : ℝ) * (γ • τ : UpperHalfPlane).im / τ.im ^ n := by
  rw [iteratedFDeriv_modularAction_eq_raw]
  exact MobiusHigher.norm_iteratedFDeriv_rawModularAction_le γ τ n hn

end GapFamily.Analytic.PoincareHigherComposition
