import GapFamily.Analytic.Cusp.Profile.CuspProfileApproximationCutoff
import GapFamily.Analytic.Cusp.Profile.CuspProfileApproximationIntegral

/-!+# Actual smooth compact approximation of zero-trace cusp profiles

The sequence is constructed from two smooth transitions. It approximates a
profile smooth at positive heights, vanishing at height one, and having finite
weighted value and vertical derivative energy. Both errors are ordinarily
integrable, and their actual integrals tend to zero.
-/

noncomputable section

namespace GapFamily.Analytic

open Set Filter MeasureTheory
open scoped Topology ContDiff

/-- The explicit compact profile obtained by cutting off near height one and
at infinity. -/
def cuspProfileApproximation (b : ℝ → ℂ) (n : ℕ) : ℝ → ℂ :=
  fun y => cuspProfileCutoff n y • b y

theorem cuspProfileApproximation_contDiff {b : ℝ → ℂ}
    (hb : ContDiffOn ℝ ∞ b (Ioi 0)) (n : ℕ) :
    ContDiff ℝ ∞ (cuspProfileApproximation b n) :=
  contDiff_cuspProfile_cutoff_mul hb (cuspProfileCutoff_contDiff n)
    (cuspProfileCutoff_tsupport_subset n)

theorem cuspProfileApproximation_hasCompactSupport (b : ℝ → ℂ) (n : ℕ) :
    HasCompactSupport (cuspProfileApproximation b n) :=
  hasCompactSupport_cuspProfile_cutoff_mul (cuspProfileCutoff_hasCompactSupport n)

theorem cuspProfileApproximation_tsupport_subset (b : ℝ → ℂ) (n : ℕ) :
    tsupport (cuspProfileApproximation b n) ⊆ Ioi (1 : ℝ) :=
  tsupport_cuspProfile_cutoff_mul (cuspProfileCutoff_tsupport_subset n)

/-- At a fixed cusp height, both the actual value and derivative eventually
agree exactly with those of the original profile. -/
theorem cuspProfileApproximation_eventually_value_deriv (b : ℝ → ℂ) {y : ℝ}
    (hy : 1 < y) : ∀ᶠ n in atTop,
      cuspProfileApproximation b n y = b y ∧
      deriv (cuspProfileApproximation b n) y = deriv b y := by
  filter_upwards [cuspProfileCutoff_eventually_eq_one hy] with n hn
  have heq : cuspProfileApproximation b n =ᶠ[𝓝 y] b := by
    filter_upwards [hn] with t ht
    simp only [cuspProfileApproximation, ht, one_smul]
  exact ⟨heq.eq_of_nhds, heq.deriv_eq⟩

/-- The approximating profiles and their actual derivatives vanish on and
below the boundary height. -/
theorem cuspProfileApproximation_zero_of_le_one (b : ℝ → ℂ) (n : ℕ) {y : ℝ}
    (hy : y ≤ 1) : cuspProfileApproximation b n y = 0 ∧
      deriv (cuspProfileApproximation b n) y = 0 := by
  have hout : y ∉ tsupport (cuspProfileApproximation b n) :=
    fun h => (not_lt_of_ge hy) (cuspProfileApproximation_tsupport_subset b n h)
  exact ⟨image_eq_zero_of_notMem_tsupport hout, HasDerivAt.of_notMem_tsupport hout |>.deriv⟩

/-- Every error is integrable, and the constructed sequence converges in both
of the scalar cusp energy integrals. No cutoff or approximation is assumed. -/
theorem cuspProfileApproximation_convergence {b : ℝ → ℂ}
    (hb : ContDiffOn ℝ ∞ b (Ioi 0)) (hb1 : b 1 = 0)
    (hv : IntegrableOn (fun y => ‖b y‖ ^ 2 / y ^ 2) (Ioi 1))
    (hd : IntegrableOn (fun y => ‖deriv b y‖ ^ 2) (Ioi 1)) :
    (∀ n, IntegrableOn
      (fun y => ‖cuspProfileApproximation b n y - b y‖ ^ 2 / y ^ 2) (Ioi 1) ∧
      IntegrableOn
        (fun y => ‖deriv (cuspProfileApproximation b n) y - deriv b y‖ ^ 2) (Ioi 1)) ∧
    Tendsto (fun n => ∫ y in Ioi (1 : ℝ),
      ‖cuspProfileApproximation b n y - b y‖ ^ 2 / y ^ 2) atTop (𝓝 0) ∧
    Tendsto (fun n => ∫ y in Ioi (1 : ℝ),
      ‖deriv (cuspProfileApproximation b n) y - deriv b y‖ ^ 2) atTop (𝓝 0) := by
  obtain ⟨C, hC, hdC⟩ := cuspProfileCutoff_deriv_bound
  exact cuspProfile_cutoff_integral_convergence hb hb1 hv hd
    cuspProfileCutoff_contDiff
    (fun n y => ⟨cuspProfileCutoff_nonneg n y, cuspProfileCutoff_le_one n y⟩)
    hC hdC (fun _ hy => cuspProfileCutoff_eventually_value_deriv hy)

/-- The two integral convergence statements for the explicit approximation. -/
theorem cuspProfileApproximation_converges {b : ℝ → ℂ}
    (hb : ContDiffOn ℝ ∞ b (Ioi 0)) (hb1 : b 1 = 0)
    (hv : IntegrableOn (fun y => ‖b y‖ ^ 2 / y ^ 2) (Ioi 1))
    (hd : IntegrableOn (fun y => ‖deriv b y‖ ^ 2) (Ioi 1)) :
    Tendsto (fun n => ∫ y in Ioi (1 : ℝ),
      ‖cuspProfileApproximation b n y - b y‖ ^ 2 / y ^ 2) atTop (𝓝 0) ∧
    Tendsto (fun n => ∫ y in Ioi (1 : ℝ),
      ‖deriv (cuspProfileApproximation b n) y - deriv b y‖ ^ 2) atTop (𝓝 0) :=
  (cuspProfileApproximation_convergence hb hb1 hv hd).2

/-- A globally smooth sequence with compact support strictly above height one
approximates every smooth zero-trace scalar cusp profile of finite energy. -/
theorem exists_cuspProfileApproximation {b : ℝ → ℂ}
    (hb : ContDiffOn ℝ ∞ b (Ioi 0)) (hb1 : b 1 = 0)
    (hv : IntegrableOn (fun y => ‖b y‖ ^ 2 / y ^ 2) (Ioi 1))
    (hd : IntegrableOn (fun y => ‖deriv b y‖ ^ 2) (Ioi 1)) :
    ∃ bₙ : ℕ → ℝ → ℂ,
      (∀ n, ContDiff ℝ ∞ (bₙ n) ∧ HasCompactSupport (bₙ n) ∧
        tsupport (bₙ n) ⊆ Ioi (1 : ℝ)) ∧
      (∀ n, IntegrableOn (fun y => ‖bₙ n y - b y‖ ^ 2 / y ^ 2) (Ioi 1) ∧
        IntegrableOn (fun y => ‖deriv (bₙ n) y - deriv b y‖ ^ 2) (Ioi 1)) ∧
      Tendsto (fun n => ∫ y in Ioi (1 : ℝ), ‖bₙ n y - b y‖ ^ 2 / y ^ 2)
        atTop (𝓝 0) ∧
      Tendsto (fun n => ∫ y in Ioi (1 : ℝ), ‖deriv (bₙ n) y - deriv b y‖ ^ 2)
        atTop (𝓝 0) := by
  refine ⟨cuspProfileApproximation b, ?_, cuspProfileApproximation_convergence hb hb1 hv hd⟩
  intro n
  exact ⟨cuspProfileApproximation_contDiff hb n,
    cuspProfileApproximation_hasCompactSupport b n, cuspProfileApproximation_tsupport_subset b n⟩

end GapFamily.Analytic
