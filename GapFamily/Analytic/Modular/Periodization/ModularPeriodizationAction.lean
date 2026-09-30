import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Smooth raw modular action

The fractional-linear formula agrees with the actual modular action on the
positive-imaginary region. Its denominator is nonzero there, so the raw map
is smooth over the real field for use in locally finite periodization.
-/

noncomputable section
open Set Matrix UpperHalfPlane
open scoped MatrixGroups ContDiff
namespace GapFamily.Analytic

/-- The actual modular fractional-linear formula on the ambient complex plane. -/
def rawModularAction (γ : SL(2, ℤ)) (z : ℂ) : ℂ :=
  UpperHalfPlane.num (γ : GL (Fin 2) ℝ) z /
    UpperHalfPlane.denom (γ : GL (Fin 2) ℝ) z

theorem rawModularAction_apply (γ : SL(2, ℤ)) (z : ℂ) :
    rawModularAction γ z =
      ((γ 0 0 : ℂ) * z + (γ 0 1 : ℂ)) /
        ((γ 1 0 : ℂ) * z + (γ 1 1 : ℂ)) := by
  rfl

/-- The raw formula is the prescribed action at every upper-half-plane point. -/
theorem rawModularAction_coe (γ : SL(2, ℤ)) (τ : UpperHalfPlane) :
    rawModularAction γ (τ : ℂ) = (γ • τ : UpperHalfPlane) := by
  exact (UpperHalfPlane.coe_smul_of_det_pos
    (g := (γ : GL (Fin 2) ℝ)) (by simp) τ).symm

/-- Positive imaginary part excludes a pole of the fractional-linear map. -/
theorem rawModularAction_denom_ne_zero (γ : SL(2, ℤ)) {z : ℂ}
    (hz : z ∈ upperHalfPlaneSet) :
    UpperHalfPlane.denom (γ : GL (Fin 2) ℝ) z ≠ 0 :=
  UpperHalfPlane.denom_ne_zero_of_im _ (ne_of_gt hz)

theorem rawModularAction_im_pos (γ : SL(2, ℤ)) {z : ℂ}
    (hz : 0 < z.im) : 0 < (rawModularAction γ z).im := by
  have h := (γ • (⟨z, hz⟩ : UpperHalfPlane)).im_pos
  change 0 < ((γ • (⟨z, hz⟩ : UpperHalfPlane) : UpperHalfPlane) : ℂ).im at h
  rw [← rawModularAction_coe γ (⟨z, hz⟩ : UpperHalfPlane)] at h
  exact h

theorem rawModularAction_mapsTo (γ : SL(2, ℤ)) :
    MapsTo (rawModularAction γ) upperHalfPlaneSet upperHalfPlaneSet :=
  fun _ hz => rawModularAction_im_pos γ hz

/-- Real smoothness supports the directional derivatives of the gradient core. -/
theorem contDiffOn_rawModularAction (γ : SL(2, ℤ)) :
    ContDiffOn ℝ ∞ (rawModularAction γ) upperHalfPlaneSet := by
  have hn : ContDiff ℝ ∞ (UpperHalfPlane.num (γ : GL (Fin 2) ℝ)) := by
    unfold UpperHalfPlane.num
    fun_prop
  have hd : ContDiff ℝ ∞ (UpperHalfPlane.denom (γ : GL (Fin 2) ℝ)) := by
    unfold UpperHalfPlane.denom
    fun_prop
  change ContDiffOn ℝ ∞ (fun z =>
    UpperHalfPlane.num (γ : GL (Fin 2) ℝ) z /
      UpperHalfPlane.denom (γ : GL (Fin 2) ℝ) z) upperHalfPlaneSet
  simpa only [Pi.mul_def, Pi.inv_def, div_eq_mul_inv] using
    hn.contDiffOn.mul (hd.contDiffOn.inv fun _ hz => rawModularAction_denom_ne_zero γ hz)

end GapFamily.Analytic
