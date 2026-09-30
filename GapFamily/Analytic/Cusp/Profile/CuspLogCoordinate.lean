import GapFamily.Analytic.Cusp.Profile.CuspLogCoordinateDeriv
import GapFamily.Analytic.Cusp.Profile.CuspLogCoordinateEnergy
import GapFamily.Analytic.Cusp.Profile.CuspLogCoordinateEnergyCore
import GapFamily.Analytic.Cusp.Profile.CuspLogCoordinateLp

/-!
# Concrete mass, energy and differential transport for scalar cusp profiles

An actual smooth compact profile supported above height one becomes a smooth
compact logarithmic profile supported above zero. Both ordinary energies
converge, and the vanishing boundary cross term gives the exact potential 1/4.
-/

noncomputable section

namespace GapFamily.Analytic

open Set MeasureTheory
open scoped ContDiff

/-- Both sides of the logarithmic energy identity are genuine integrable functions. -/
theorem integrableOn_cuspLogCoordinate_energy {b : ℝ → ℂ}
    (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b) (hs : tsupport b ⊆ Ioi 1) :
    IntegrableOn (fun y => ‖deriv b y‖ ^ 2) (Ioi 1) ∧
      IntegrableOn (fun t => ‖deriv (cuspLogCoordinate b) t‖ ^ 2 +
        ‖cuspLogCoordinate b t‖ ^ 2 / 4) (Ioi 0) := by
  have hb1 : ContDiff ℝ 1 b := hb.of_le (by simp)
  have hv1 : ContDiff ℝ 1 (cuspLogCoordinate b) :=
    (contDiff_cuspLogCoordinate hb).of_le (by simp)
  have hvc := hasCompactSupport_cuspLogCoordinate hc hs
  exact ⟨(cusp_log_core_derivative_integrable hb1 hc).integrableOn,
    (cusp_log_core_derivative_integrable hv1 hvc).integrableOn.add
      ((cusp_log_core_mass_integrable hv1 hvc).integrableOn.div_const 4)⟩

/-- The original physical profile has exactly the free logarithmic derivative
energy plus the scalar potential one quarter; both boundary terms vanish. -/
theorem integral_cuspLogCoordinate_energy {b : ℝ → ℂ}
    (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b) (hs : tsupport b ⊆ Ioi 1) :
    (∫ y in Ioi 1, ‖deriv b y‖ ^ 2) =
      ∫ t in Ioi 0, (‖deriv (cuspLogCoordinate b) t‖ ^ 2 +
        ‖cuspLogCoordinate b t‖ ^ 2 / 4) := by
  have hv := contDiff_cuspLogCoordinate hb
  calc
    _ = ∫ y in Ioi 1, ‖deriv (cuspLift (cuspLogCoordinate b)) y‖ ^ 2 := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      dsimp only
      rw [deriv_cuspLift_cuspLogCoordinate b (zero_lt_one.trans hy)]
    _ = ∫ t in Ioi 0, ‖deriv (cuspLogCoordinate b) t +
        (1 / 2 : ℝ) • cuspLogCoordinate b t‖ ^ 2 :=
      integral_deriv_cuspLift_norm_sq (hv.differentiable (by simp))
    _ = _ := cusp_log_core_energy_identity (hv.of_le (by simp))
      (hasCompactSupport_cuspLogCoordinate hc hs) (cuspLogCoordinate_zero hs)

/-- The complete energy statement includes convergence of both ordinary integrals. -/
theorem cuspLogCoordinate_energy {b : ℝ → ℂ}
    (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b) (hs : tsupport b ⊆ Ioi 1) :
    IntegrableOn (fun y => ‖deriv b y‖ ^ 2) (Ioi 1) ∧
      IntegrableOn (fun t => ‖deriv (cuspLogCoordinate b) t‖ ^ 2 +
        ‖cuspLogCoordinate b t‖ ^ 2 / 4) (Ioi 0) ∧
      (∫ y in Ioi 1, ‖deriv b y‖ ^ 2) =
        ∫ t in Ioi 0, (‖deriv (cuspLogCoordinate b) t‖ ^ 2 +
          ‖cuspLogCoordinate b t‖ ^ 2 / 4) :=
  ⟨(integrableOn_cuspLogCoordinate_energy hb hc hs).1,
    (integrableOn_cuspLogCoordinate_energy hb hc hs).2,
    integral_cuspLogCoordinate_energy hb hc hs⟩

end GapFamily.Analytic
