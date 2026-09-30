import GapFamily.Analytic.Cusp.Profile.CuspLogCoordinateBasic
import GapFamily.Analytic.Cusp.CuspCoordinateDeriv

/-!
# Differential conjugation of an actual physical cusp profile

The logarithmic profile is the explicit exponential pullback of the original
function. The existing cusp-lift chain rule transfers back through an equality
on the open positive half-line, so both derivatives are the ordinary ones.
-/

noncomputable section

namespace GapFamily.Analytic

open Set
open scoped ContDiff

theorem deriv_cuspLift_cuspLogCoordinate (b : ℝ → ℂ) {y : ℝ} (hy : 0 < y) :
    deriv (cuspLift (cuspLogCoordinate b)) y = deriv b y := by
  have h : EqOn (cuspLift (cuspLogCoordinate b)) b (Ioi 0) :=
    fun _ hy => cuspLift_cuspLogCoordinate hy
  exact h.deriv isOpen_Ioi hy

theorem deriv_deriv_cuspLift_cuspLogCoordinate (b : ℝ → ℂ) {y : ℝ} (hy : 0 < y) :
    deriv (deriv (cuspLift (cuspLogCoordinate b))) y = deriv (deriv b) y := by
  have h : EqOn (deriv (cuspLift (cuspLogCoordinate b))) (deriv b) (Ioi 0) :=
    fun _ hy => deriv_cuspLift_cuspLogCoordinate b hy
  exact h.deriv isOpen_Ioi hy

/-- The actual physical first derivative in the logarithmic coordinate. -/
theorem deriv_eq_cuspLogCoordinate {b : ℝ → ℂ} (hb : ContDiff ℝ ∞ b)
    {y : ℝ} (hy : 0 < y) :
    deriv b y = (Real.sqrt y)⁻¹ •
      (deriv (cuspLogCoordinate b) (Real.log y) +
        (1 / 2 : ℝ) • cuspLogCoordinate b (Real.log y)) := by
  rw [← deriv_cuspLift_cuspLogCoordinate b hy]
  exact deriv_cuspLift ((contDiff_cuspLogCoordinate hb).differentiable (by simp)) hy

/-- Exact ordinary differential conjugation for the original physical profile. -/
theorem cuspLogCoordinate_laplacian {b : ℝ → ℂ} (hb : ContDiff ℝ ∞ b)
    {y : ℝ} (hy : 0 < y) :
    -(y ^ 2) • deriv (deriv b) y =
      Real.sqrt y • (-deriv (deriv (cuspLogCoordinate b)) (Real.log y) +
        (1 / 4 : ℝ) • cuspLogCoordinate b (Real.log y)) := by
  have h := cuspLift_laplacian ((contDiff_cuspLogCoordinate hb).of_le (by simp) :
    ContDiff ℝ 2 (cuspLogCoordinate b)) hy
  rwa [deriv_deriv_cuspLift_cuspLogCoordinate b hy] at h

end GapFamily.Analytic
