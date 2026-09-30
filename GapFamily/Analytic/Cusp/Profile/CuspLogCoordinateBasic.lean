import GapFamily.Analytic.Cusp.CuspCoordinate
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Algebra.Support
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# The actual logarithmic cusp profile

The exponential normalization gives the existing cusp pullback in smooth
coordinates. A compact profile supported above height one remains compactly
supported on the positive logarithmic axis, and its ordinary squared mass is
exactly the hyperbolic squared mass of the original profile.
-/

noncomputable section

namespace GapFamily.Analytic

open Set MeasureTheory
open scoped ContDiff

/-- The logarithmic cusp profile, written with its smooth exponential normalization. -/
def cuspLogCoordinate (b : ℝ → ℂ) (t : ℝ) : ℂ :=
  Real.exp (-t / 2) • b (Real.exp t)

/-- The smooth formula is exactly the already constructed cusp pullback. -/
theorem cuspLogCoordinate_eq_cuspPullback (b : ℝ → ℂ) :
    cuspLogCoordinate b = cuspPullback b := by
  funext t
  unfold cuspLogCoordinate cuspPullback
  rw [← Real.exp_half, ← Real.exp_neg]
  congr 2
  ring

/-- The inverse coordinate map recovers the actual profile at every positive height. -/
theorem cuspLift_cuspLogCoordinate {b : ℝ → ℂ} {y : ℝ} (hy : 0 < y) :
    cuspLift (cuspLogCoordinate b) y = b y := by
  rw [cuspLogCoordinate_eq_cuspPullback]
  exact cuspLift_cuspPullback b hy

theorem continuous_cuspLogCoordinate {b : ℝ → ℂ} (hb : Continuous b) :
    Continuous (cuspLogCoordinate b) := by
  unfold cuspLogCoordinate
  fun_prop

/-- Every globally smooth compact-profile candidate gives a globally smooth logarithmic profile. -/
theorem contDiff_cuspLogCoordinate {b : ℝ → ℂ} (hb : ContDiff ℝ ∞ b) :
    ContDiff ℝ ∞ (cuspLogCoordinate b) := by
  unfold cuspLogCoordinate
  fun_prop

/-- Pullback support is contained in the exponential preimage of the original topological support. -/
theorem tsupport_cuspLogCoordinate_subset_preimage (b : ℝ → ℂ) :
    tsupport (cuspLogCoordinate b) ⊆ Real.exp ⁻¹' tsupport b := by
  exact (tsupport_smul_subset_right (fun t : ℝ => Real.exp (-t / 2))
    (fun t : ℝ => b (Real.exp t))).trans
    (tsupport_comp_subset_preimage b Real.continuous_exp)

/-- Support above height one becomes support strictly above logarithmic height zero. -/
theorem tsupport_cuspLogCoordinate_subset {b : ℝ → ℂ}
    (hb : tsupport b ⊆ Ioi 1) : tsupport (cuspLogCoordinate b) ⊆ Ioi 0 := by
  intro t ht
  have h : 1 < Real.exp t := hb (tsupport_cuspLogCoordinate_subset_preimage b ht)
  exact Real.one_lt_exp_iff.mp h

/-- Compact support is preserved because the logarithm is continuous on the original support. -/
theorem hasCompactSupport_cuspLogCoordinate {b : ℝ → ℂ}
    (hc : HasCompactSupport b) (hb : tsupport b ⊆ Ioi 1) :
    HasCompactSupport (cuspLogCoordinate b) := by
  have hlog : ContinuousOn Real.log (tsupport b) := by
    intro y hy
    exact (Real.continuousAt_log (ne_of_gt (zero_lt_one.trans (hb hy)))).continuousWithinAt
  have hk : IsCompact (Real.log '' tsupport b) := hc.isCompact.image_of_continuousOn hlog
  apply hk.of_isClosed_subset (isClosed_tsupport _)
  intro t ht
  exact ⟨Real.exp t, tsupport_cuspLogCoordinate_subset_preimage b ht, Real.log_exp t⟩

/-- The transformed profile vanishes at the finite cusp boundary. -/
theorem cuspLogCoordinate_zero {b : ℝ → ℂ} (hb : tsupport b ⊆ Ioi 1) :
    cuspLogCoordinate b 0 = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro h
  have h0 := tsupport_cuspLogCoordinate_subset hb h
  exact (lt_irrefl (0 : ℝ)) h0

/-- The square-root normalization cancels exactly one exponential Jacobian. -/
theorem cuspLogCoordinate_norm_sq (b : ℝ → ℂ) (t : ℝ) :
    ‖cuspLogCoordinate b t‖^2 = Real.exp (-t) * ‖b (Real.exp t)‖^2 := by
  rw [cuspLogCoordinate, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow]
  have he : Real.exp (-t / 2)^2 = Real.exp (-t) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [he]

/-- The ordinary exponential substitution integrand is the true logarithmic squared norm. -/
theorem cuspLogCoordinate_mass_integrand (b : ℝ → ℂ) (t : ℝ) :
    Real.exp t * (‖b (Real.exp t)‖^2 / (Real.exp t)^2) = ‖cuspLogCoordinate b t‖^2 := by
  rw [cuspLogCoordinate_norm_sq, Real.exp_neg]
  field_simp

/-- Actual integrability of the logarithmic squared norm for a continuous compact cusp profile. -/
theorem integrable_cuspLogCoordinate_norm_sq {b : ℝ → ℂ}
    (hb : Continuous b) (hc : HasCompactSupport b) (hs : tsupport b ⊆ Ioi 1) :
    Integrable (fun t : ℝ => ‖cuspLogCoordinate b t‖^2) := by
  have hv := continuous_cuspLogCoordinate hb
  have hvc := hasCompactSupport_cuspLogCoordinate hc hs
  have hnorm : HasCompactSupport (fun t : ℝ => ‖cuspLogCoordinate b t‖^2) :=
    hvc.comp_left (g := fun z : ℂ => ‖z‖^2) (by simp)
  exact (hv.norm.pow 2).integrable_of_hasCompactSupport hnorm

/-- The positive-axis integrability equivalence follows from the actual exponential substitution. -/
theorem integrableOn_cuspLogCoordinate_mass_iff (b : ℝ → ℂ) :
    IntegrableOn (fun y : ℝ => ‖b y‖^2 / y^2) (Ioi 1) ↔
      IntegrableOn (fun t : ℝ => ‖cuspLogCoordinate b t‖^2) (Ioi 0) := by
  have h := integrableOn_comp_exp_Ioi (fun y : ℝ => ‖b y‖^2 / y^2) 0
  simpa only [Real.exp_zero, smul_eq_mul, cuspLogCoordinate_mass_integrand] using h.symm

/-- A compact cusp profile has genuinely integrable hyperbolic squared mass. -/
theorem integrableOn_cuspLogCoordinate_mass {b : ℝ → ℂ}
    (hb : Continuous b) (hc : HasCompactSupport b) (hs : tsupport b ⊆ Ioi 1) :
    IntegrableOn (fun y : ℝ => ‖b y‖^2 / y^2) (Ioi 1) :=
  (integrableOn_cuspLogCoordinate_mass_iff b).mpr
    (integrable_cuspLogCoordinate_norm_sq hb hc hs).integrableOn

/-- Both genuine integrability assertions and their exact mass identity. -/
theorem cuspLogCoordinate_mass {b : ℝ → ℂ}
    (hb : Continuous b) (hc : HasCompactSupport b) (hs : tsupport b ⊆ Ioi 1) :
    IntegrableOn (fun y : ℝ => ‖b y‖^2 / y^2) (Ioi 1) ∧
      IntegrableOn (fun t : ℝ => ‖cuspLogCoordinate b t‖^2) (Ioi 0) ∧
      (∫ y : ℝ in Ioi 1, ‖b y‖^2 / y^2) =
        ∫ t : ℝ in Ioi 0, ‖cuspLogCoordinate b t‖^2 := by
  refine ⟨integrableOn_cuspLogCoordinate_mass hb hc hs,
    (integrable_cuspLogCoordinate_norm_sq hb hc hs).integrableOn, ?_⟩
  have h := integral_comp_exp_Ioi (fun y : ℝ => ‖b y‖^2 / y^2) 0
  simpa only [Real.exp_zero, smul_eq_mul, cuspLogCoordinate_mass_integrand] using h.symm

/-- Exact mass equality for the continuous compact cusp profile. -/
theorem integral_cuspLogCoordinate_mass {b : ℝ → ℂ}
    (hb : Continuous b) (hc : HasCompactSupport b) (hs : tsupport b ⊆ Ioi 1) :
    (∫ y : ℝ in Ioi 1, ‖b y‖^2 / y^2) =
      ∫ t : ℝ in Ioi 0, ‖cuspLogCoordinate b t‖^2 :=
  (cuspLogCoordinate_mass hb hc hs).2.2

end GapFamily.Analytic
