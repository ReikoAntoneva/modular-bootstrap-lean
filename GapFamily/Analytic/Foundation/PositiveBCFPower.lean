import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import GapFamily.Analytic.Foundation.PositivePowerClampFamily
import GapFamily.Analytic.Foundation.PositivePowerClampBound

noncomputable section

namespace GapFamily.Analytic.PositiveBCFPower

open Set Filter
open scoped Topology BoundedContinuousFunction

variable {X : Type*} [TopologicalSpace X]

/-- The genuine bounded continuous positive-base power on the right half-plane.
It is totalized to zero outside that domain, where boundedness need not hold. -/
def positivePower (p : X → ℝ) (hp : Continuous p) (hpos : ∀ x, 0 < p x)
    (M : ℝ) (hM : ∀ x, p x ≤ M) (s : ℂ) : X →ᵇ ℂ := by
  classical
  exact if hs : 0 < s.re then
    BoundedContinuousFunction.ofNormedAddCommGroup (fun x => (p x : ℂ) ^ s)
      ((Complex.continuous_ofReal_cpow_const hs).comp hp) (M ^ s.re)
      (fun x => by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos (hpos x)]
        exact Real.rpow_le_rpow (hpos x).le (hM x) hs.le)
    else 0

theorem positivePower_apply (p : X → ℝ) (hp : Continuous p) (hpos : ∀ x, 0 < p x)
    (M : ℝ) (hM : ∀ x, p x ≤ M) {s : ℂ} (hs : 0 < s.re) (x : X) :
    positivePower p hp hpos M hM s x = (p x : ℂ) ^ s := by
  simp [positivePower, hs]

/-- The clamped entire approximants converge uniformly on every positive
closed sub-half-plane, even when the original bases approach zero. -/
theorem positivePower_clamped_norm_sub_le
    (p : X → ℝ) (hp : Continuous p) (hpos : ∀ x, 0 < p x)
    (M : ℝ) (hM : ∀ x, p x ≤ M) {ε δ : ℝ} {s : ℂ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hs : δ ≤ s.re) :
    ‖clampedPower p hp M hM ε hε s - positivePower p hp hpos M hM s‖ ≤
      2 * ε ^ δ := by
  apply (BoundedContinuousFunction.norm_le
    (mul_nonneg zero_le_two (Real.rpow_nonneg hε.le δ))).mpr
  intro x
  change ‖clampedPower p hp M hM ε hε s x - positivePower p hp hpos M hM s x‖ ≤ _
  rw [clampedPower_apply, positivePower_apply p hp hpos M hM (hδ.trans_le hs)]
  exact GapFamily.Analytic.positivePower_clamp_bound (hpos x) hε hε1 hδ hs

/-- Locally uniform convergence in the actual bounded-continuous-function norm. -/
theorem positivePower_tendstoLocallyUniformlyOn
    (p : X → ℝ) (hp : Continuous p) (hpos : ∀ x, 0 < p x)
    (M : ℝ) (hM : ∀ x, p x ≤ M) :
    TendstoLocallyUniformlyOn
      (fun n : ℕ => clampedPower p hp M hM (Real.exp (-(n : ℝ))) (Real.exp_pos _))
      (positivePower p hp hpos M hM) atTop {s : ℂ | 0 < s.re} := by
  apply Metric.tendstoLocallyUniformlyOn_iff.mpr
  intro η hη s hs
  let δ : ℝ := s.re / 2
  have hδ : 0 < δ := half_pos hs
  have hsδ : δ < s.re := half_lt_self hs
  refine ⟨{z : ℂ | δ < z.re}, mem_nhdsWithin_of_mem_nhds
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hsδ), ?_⟩
  have heps : Tendsto (fun n : ℕ => Real.exp (-(n : ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop
  have herr : Tendsto (fun n : ℕ => 2 * (Real.exp (-(n : ℝ))) ^ δ) atTop (𝓝 0) := by
    have h := ((Real.continuousAt_rpow_const 0 δ (Or.inr hδ.le)).tendsto.comp heps).const_mul 2
    simpa only [Function.comp_def, Real.zero_rpow hδ.ne', mul_zero] using h
  have hsmall : ∀ᶠ n : ℕ in atTop, 2 * (Real.exp (-(n : ℝ))) ^ δ < η :=
    (tendsto_order.mp herr).2 η hη
  filter_upwards [hsmall] with n hn z hz
  rw [dist_comm, dist_eq_norm]
  have heps1 : Real.exp (-(n : ℝ)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg n))
  exact (positivePower_clamped_norm_sub_le p hp hpos M hM
    (Real.exp_pos _) heps1 hδ (le_of_lt hz)).trans_lt hn

/-- Banach-valued holomorphy of the genuine positive power; no positive
uniform lower bound for the base is assumed. -/
theorem positivePower_differentiableOn
    (p : X → ℝ) (hp : Continuous p) (hpos : ∀ x, 0 < p x)
    (M : ℝ) (hM : ∀ x, p x ≤ M) :
    DifferentiableOn ℂ (positivePower p hp hpos M hM) {s : ℂ | 0 < s.re} :=
  (positivePower_tendstoLocallyUniformlyOn p hp hpos M hM).differentiableOn
    (Eventually.of_forall fun n s _ =>
      (clampedPower_analyticAt p hp M hM (Real.exp (-(n : ℝ)))
        (Real.exp_pos _) s).differentiableAt.differentiableWithinAt)
    (isOpen_lt continuous_const Complex.continuous_re)

theorem positivePower_analyticAt
    (p : X → ℝ) (hp : Continuous p) (hpos : ∀ x, 0 < p x)
    (M : ℝ) (hM : ∀ x, p x ≤ M) {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ (positivePower p hp hpos M hM) s :=
  (positivePower_differentiableOn p hp hpos M hM).analyticAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)

/-- Any fixed bounded continuous amplitude preserves the proved norm analyticity. -/
theorem positivePower_mul_analyticAt
    (p : X → ℝ) (hp : Continuous p) (hpos : ∀ x, 0 < p x)
    (M : ℝ) (hM : ∀ x, p x ≤ M) (a : X →ᵇ ℂ) {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ (fun z => positivePower p hp hpos M hM z * a) s :=
  (positivePower_analyticAt p hp hpos M hM hs).mul analyticAt_const

end GapFamily.Analytic.PositiveBCFPower
