import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Integration by parts for a compact cusp profile

A globally smooth profile supported compactly above height one can be paired
with a function smooth only at positive heights. The ordinary derivative and
second-derivative products are integrable, and integration by parts on the
actual half-line has no boundary contribution. No extension across height zero
or extra boundary condition at height one is required.
-/

noncomputable section

namespace GapFamily.Analytic

open MeasureTheory Set
open scoped ContDiff

variable {b A : ℝ → ℂ}

private theorem profile_support_pos (hs : tsupport b ⊆ Ioi (1 : ℝ)) :
    tsupport b ⊆ Ioi (0 : ℝ) := by
  intro y hy
  have h := hs hy
  change 1 < y at h
  change 0 < y
  exact lt_trans (by norm_num) h

private theorem profile_secondDeriv_zero {y : ℝ} (hy : y ∉ tsupport b) :
    deriv (deriv b) y = 0 :=
  deriv_of_notMem_tsupport (fun h => hy (tsupport_deriv_subset h))

private theorem profile_factor_integrable {g : ℝ → ℂ}
    (hc : HasCompactSupport b) (hs : tsupport b ⊆ Ioi (1 : ℝ))
    (hg : Continuous g) (hA : ContinuousOn A (Ioi (0 : ℝ)))
    (hzero : ∀ y ∉ tsupport b, g y = 0) :
    Integrable (fun y => g y * A y) := by
  have hcont : ContinuousOn (fun y => g y * A y) (tsupport b) :=
    hg.continuousOn.mul (hA.mono (profile_support_pos hs))
  apply (hcont.integrableOn_compact hc).integrable_of_forall_notMem_eq_zero
  intro y hy
  rw [hzero y hy, zero_mul]

/-- The ordinary first-derivative pairing is globally integrable. -/
theorem cuspProfileLaplacian_deriv_pair_integrable
    (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b)
    (hs : tsupport b ⊆ Ioi (1 : ℝ)) (hA : ContDiffOn ℝ ∞ A (Ioi (0 : ℝ))) :
    Integrable (fun y => star (deriv b y) * deriv A y) := by
  apply profile_factor_integrable hc hs
    (hb.continuous_deriv (by simp)).star
    (hA.continuousOn_deriv_of_isOpen isOpen_Ioi (by simp))
  intro y hy
  rw [deriv_of_notMem_tsupport hy, star_zero]

/-- The ordinary second-derivative pairing is globally integrable. -/
theorem cuspProfileLaplacian_secondDeriv_pair_integrable
    (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b)
    (hs : tsupport b ⊆ Ioi (1 : ℝ)) (hA : ContDiffOn ℝ ∞ A (Ioi (0 : ℝ))) :
    Integrable (fun y => star (deriv (deriv b) y) * A y) := by
  have hb' : ContDiff ℝ ∞ (deriv b) := (contDiff_infty_iff_deriv.mp hb).2
  apply profile_factor_integrable hc hs
    (hb'.continuous_deriv (by simp)).star hA.continuousOn
  intro y hy
  rw [profile_secondDeriv_zero hy, star_zero]

/-- Both actual half-line pairings are integrable. -/
theorem cuspProfileLaplacian_pair_integrableOn
    (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b)
    (hs : tsupport b ⊆ Ioi (1 : ℝ)) (hA : ContDiffOn ℝ ∞ A (Ioi (0 : ℝ))) :
    IntegrableOn (fun y => star (deriv b y) * deriv A y) (Ioi (1 : ℝ)) ∧
      IntegrableOn (fun y => star (deriv (deriv b) y) * A y) (Ioi (1 : ℝ)) :=
  ⟨(cuspProfileLaplacian_deriv_pair_integrable hb hc hs hA).integrableOn,
    (cuspProfileLaplacian_secondDeriv_pair_integrable hb hc hs hA).integrableOn⟩

/-- Actual ordinary integration by parts on the upper cusp half-line. -/
theorem cuspProfileLaplacian_integral_deriv_mul
    (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b)
    (hs : tsupport b ⊆ Ioi (1 : ℝ)) (hA : ContDiffOn ℝ ∞ A (Ioi (0 : ℝ))) :
    (∫ y in Ioi (1 : ℝ), star (deriv b y) * deriv A y) =
      -(∫ y in Ioi (1 : ℝ), star (deriv (deriv b) y) * A y) := by
  have hb' : ContDiff ℝ ∞ (deriv b) := (contDiff_infty_iff_deriv.mp hb).2
  have hu : ∀ y, HasDerivAt (fun t => star (deriv b t))
      (star (deriv (deriv b) y)) y :=
    fun y => (hb'.differentiable (by simp) y).hasDerivAt.star
  have hsupport : tsupport (fun y => star (deriv b y)) ⊆ tsupport b :=
    (tsupport_comp_subset (g := star) (by simp) (deriv b)).trans tsupport_deriv_subset
  have hv : ∀ y ∈ tsupport (fun t => star (deriv b t)), HasDerivAt A (deriv A y) y := by
    intro y hy
    have hy0 : y ∈ Ioi (0 : ℝ) := profile_support_pos hs (hsupport hy)
    exact ((hA.differentiableOn (by simp) y hy0).differentiableAt
      (isOpen_Ioi.mem_nhds hy0)).hasDerivAt
  have huv : Integrable (fun y => star (deriv b y) * A y) := by
    apply profile_factor_integrable hc hs (hb.continuous_deriv (by simp)).star hA.continuousOn
    intro y hy
    rw [deriv_of_notMem_tsupport hy, star_zero]
  have hwhole := MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun y _ => hu y) hv
    (cuspProfileLaplacian_deriv_pair_integrable hb hc hs hA)
    (cuspProfileLaplacian_secondDeriv_pair_integrable hb hc hs hA) huv
  have hfirst : (∫ y in Ioi (1 : ℝ), star (deriv b y) * deriv A y) =
      ∫ y, star (deriv b y) * deriv A y := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    have hyb : y ∉ tsupport b := fun h => hy (hs h)
    rw [deriv_of_notMem_tsupport hyb, star_zero, zero_mul]
  have hsecond : (∫ y in Ioi (1 : ℝ), star (deriv (deriv b) y) * A y) =
      ∫ y, star (deriv (deriv b) y) * A y := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    have hyb : y ∉ tsupport b := fun h => hy (hs h)
    rw [profile_secondDeriv_zero hyb, star_zero, zero_mul]
  rw [hfirst, hsecond]
  exact hwhole

/-- The same identity expressed with the actual second iterated derivative. -/
theorem cuspProfileLaplacian_integral_iteratedDeriv
    (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b)
    (hs : tsupport b ⊆ Ioi (1 : ℝ)) (hA : ContDiffOn ℝ ∞ A (Ioi (0 : ℝ))) :
    (∫ y in Ioi (1 : ℝ), star (deriv b y) * deriv A y) =
      -(∫ y in Ioi (1 : ℝ), star (iteratedDeriv 2 b y) * A y) := by
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
    cuspProfileLaplacian_integral_deriv_mul hb hc hs hA

end GapFamily.Analytic
