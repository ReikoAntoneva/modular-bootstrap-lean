import GapFamily.Analytic.Cusp.Profile.CuspProfileApproximation
import GapFamily.Analytic.Cusp.Profile.CuspProfileNormDifference

/-!
# Graph convergence of the compact cusp profile approximation

The exact scalar formula for the completed form norm turns the two proved
approximation error estimates into a Cauchy sequence in the actual graph domain.
-/

noncomputable section

namespace GapFamily.Analytic

open Set Filter MeasureTheory ModularGradient
open scoped Topology ContDiff

/-- The explicit compact scalar approximation, embedded into the completed
modular form domain through the original smooth automorphic core. -/
def cuspProfileFormSequence (b : ℝ → ℂ) (hb : ContDiffOn ℝ ∞ b (Ioi 0))
    (n : ℕ) : FormDomain :=
  coreForm (cuspProfileCore (cuspProfileApproximation b n)
    (cuspProfileApproximation_contDiff hb n)
    (cuspProfileApproximation_hasCompactSupport b n)
    (cuspProfileApproximation_tsupport_subset b n))

private theorem profile_norm_sub_sq_le (u v w : ℂ) :
    ‖u - v‖ ^ 2 ≤ 2 * (‖u - w‖ ^ 2 + ‖v - w‖ ^ 2) := by
  have h : ‖u - v‖ ≤ ‖u - w‖ + ‖v - w‖ := by
    calc
      ‖u - v‖ = ‖(u - w) - (v - w)‖ := by congr 1; abel
      _ ≤ ‖u - w‖ + ‖v - w‖ := norm_sub_le _ _
  nlinarith [norm_nonneg (u - v), norm_nonneg (u - w), norm_nonneg (v - w),
    sq_nonneg (‖u - w‖ - ‖v - w‖)]

/-- Each actual graph-norm difference is controlled by the four ordinary
scalar errors of its two approximants. -/
theorem cuspProfileFormSequence_norm_sub_sq_le (b : ℝ → ℂ)
    (hb : ContDiffOn ℝ ∞ b (Ioi 0)) (hb1 : b 1 = 0)
    (hv : IntegrableOn (fun y => ‖b y‖ ^ 2 / y ^ 2) (Ioi 1))
    (hd : IntegrableOn (fun y => ‖deriv b y‖ ^ 2) (Ioi 1)) (m n : ℕ) :
    ‖cuspProfileFormSequence b hb m - cuspProfileFormSequence b hb n‖ ^ 2 ≤
      2 * ((∫ y in Ioi (1 : ℝ), ‖cuspProfileApproximation b m y - b y‖ ^ 2 / y ^ 2) +
        (∫ y in Ioi (1 : ℝ), ‖cuspProfileApproximation b n y - b y‖ ^ 2 / y ^ 2) +
        (∫ y in Ioi (1 : ℝ), ‖deriv (cuspProfileApproximation b m) y - deriv b y‖ ^ 2) +
        ∫ y in Ioi (1 : ℝ), ‖deriv (cuspProfileApproximation b n) y - deriv b y‖ ^ 2) := by
  have herr := (cuspProfileApproximation_convergence hb hb1 hv hd).1
  have hval : (∫ y in Ioi (1 : ℝ),
      ‖cuspProfileApproximation b m y - cuspProfileApproximation b n y‖ ^ 2 / y ^ 2) ≤
      2 * ((∫ y in Ioi (1 : ℝ), ‖cuspProfileApproximation b m y - b y‖ ^ 2 / y ^ 2) +
        ∫ y in Ioi (1 : ℝ), ‖cuspProfileApproximation b n y - b y‖ ^ 2 / y ^ 2) := by
    calc
      _ ≤ ∫ y in Ioi (1 : ℝ),
          2 * (‖cuspProfileApproximation b m y - b y‖ ^ 2 / y ^ 2 +
            ‖cuspProfileApproximation b n y - b y‖ ^ 2 / y ^ 2) := by
        apply integral_mono_of_nonneg (Eventually.of_forall (fun y => by positivity))
          (((herr m).1.add (herr n).1).const_mul 2)
        exact Eventually.of_forall (fun y => by
          calc
            _ ≤ (2 * (‖cuspProfileApproximation b m y - b y‖ ^ 2 +
                ‖cuspProfileApproximation b n y - b y‖ ^ 2)) / y ^ 2 :=
              div_le_div_of_nonneg_right (profile_norm_sub_sq_le _ _ _) (sq_nonneg y)
            _ = _ := by simp only [Pi.add_apply]; ring)
      _ = _ := by rw [integral_const_mul, integral_add (herr m).1 (herr n).1]
  have hder : (∫ y in Ioi (1 : ℝ),
      ‖deriv (cuspProfileApproximation b m) y - deriv (cuspProfileApproximation b n) y‖ ^ 2) ≤
      2 * ((∫ y in Ioi (1 : ℝ), ‖deriv (cuspProfileApproximation b m) y - deriv b y‖ ^ 2) +
        ∫ y in Ioi (1 : ℝ), ‖deriv (cuspProfileApproximation b n) y - deriv b y‖ ^ 2) := by
    calc
      _ ≤ ∫ y in Ioi (1 : ℝ),
          2 * (‖deriv (cuspProfileApproximation b m) y - deriv b y‖ ^ 2 +
            ‖deriv (cuspProfileApproximation b n) y - deriv b y‖ ^ 2) := by
        apply integral_mono_of_nonneg (Eventually.of_forall (fun y => sq_nonneg _))
          (((herr m).2.add (herr n).2).const_mul 2)
        exact Eventually.of_forall (fun y => profile_norm_sub_sq_le _ _ _)
      _ = _ := by rw [integral_const_mul, integral_add (herr m).2 (herr n).2]
  dsimp only [cuspProfileFormSequence]
  rw [cuspProfileCore_form_sub_norm_sq]
  linarith

/-- The genuine modular form sequence is Cauchy in its completed graph norm. -/
theorem cuspProfileFormSequence_cauchy (b : ℝ → ℂ)
    (hb : ContDiffOn ℝ ∞ b (Ioi 0)) (hb1 : b 1 = 0)
    (hv : IntegrableOn (fun y => ‖b y‖ ^ 2 / y ^ 2) (Ioi 1))
    (hd : IntegrableOn (fun y => ‖deriv b y‖ ^ 2) (Ioi 1)) :
    CauchySeq (cuspProfileFormSequence b hb) := by
  let V : ℕ → ℝ := fun n => ∫ y in Ioi (1 : ℝ),
    ‖cuspProfileApproximation b n y - b y‖ ^ 2 / y ^ 2
  let D : ℕ → ℝ := fun n => ∫ y in Ioi (1 : ℝ),
    ‖deriv (cuspProfileApproximation b n) y - deriv b y‖ ^ 2
  have hconv := cuspProfileApproximation_converges hb hb1 hv hd
  have hsum : Tendsto (fun n => V n + D n) atTop (𝓝 0) := by
    simpa only [add_zero] using hconv.1.add hconv.2
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  have hsmall : ∀ᶠ n in atTop, V n + D n < ε ^ 2 / 4 :=
    hsum.eventually (gt_mem_nhds (by positivity))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hsmall
  refine ⟨N, fun m hm n hn => ?_⟩
  have hbound := cuspProfileFormSequence_norm_sub_sq_le b hb hb1 hv hd m n
  change ‖cuspProfileFormSequence b hb m - cuspProfileFormSequence b hb n‖ ^ 2 ≤
    2 * (V m + V n + D m + D n) at hbound
  rw [dist_eq_norm]
  have hm' := hN m hm
  have hn' := hN n hn
  nlinarith [norm_nonneg (cuspProfileFormSequence b hb m - cuspProfileFormSequence b hb n)]

/-- Completeness of the actual closed form domain supplies a limit for every
smooth, zero-trace, finite-energy cusp profile. -/
theorem exists_cuspProfileFormSequence_tendsto (b : ℝ → ℂ)
    (hb : ContDiffOn ℝ ∞ b (Ioi 0)) (hb1 : b 1 = 0)
    (hv : IntegrableOn (fun y => ‖b y‖ ^ 2 / y ^ 2) (Ioi 1))
    (hd : IntegrableOn (fun y => ‖deriv b y‖ ^ 2) (Ioi 1)) :
    ∃ u : FormDomain, Tendsto (cuspProfileFormSequence b hb) atTop (𝓝 u) :=
  cauchySeq_tendsto_of_complete (cuspProfileFormSequence_cauchy b hb hb1 hv hd)

end GapFamily.Analytic
