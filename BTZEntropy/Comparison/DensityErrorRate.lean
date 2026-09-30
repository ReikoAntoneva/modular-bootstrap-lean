import BTZEntropy.Comparison.InitialPacketSubexponential
import GapFamily.GapFamilyLimit
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Exponential advantage of the repair density

The repair exponent `7 * sqrt (a * E)` stays a fixed linear distance below
BTZ on every positive energy-ratio interval. Polynomial prefactors and the
all-descendant root exponential cost do not exhaust this distance.
-/

noncomputable section

open Real Filter
open scoped Topology

namespace BTZEntropy.Comparison

/-- A uniform elementary upper bound on the repair square root. -/
theorem densityError_sqrt_le {c x R : ℝ} (hc : 1 ≤ c) (hx : 0 ≤ x)
    (hR : 0 ≤ R) :
    sqrt (((c - 1) / 12) * (x * c + R)) ≤
      (c * sqrt x + sqrt c * sqrt R) / 3 := by
  have hc0 : 0 ≤ c := by linarith
  have hq : 0 ≤ ((c - 1) / 12) * (x * c + R) := by positivity
  have hsx := sq_sqrt hx
  have hsc := sq_sqrt hc0
  have hsR := sq_sqrt hR
  apply (sqrt_le_iff).mpr
  constructor
  · positivity
  · have hcross : 0 ≤ 2 * c * sqrt x * sqrt c * sqrt R := by positivity
    have heq : ((c * sqrt x + sqrt c * sqrt R) / 3) ^ 2 =
        (c ^ 2 * x + c * R + 2 * c * sqrt x * sqrt c * sqrt R) / 9 := by
      nlinarith [sq_nonneg (c * sqrt x + sqrt c * sqrt R)]
    rw [heq]
    have hxc : 0 ≤ x * c := mul_nonneg hx hc0
    nlinarith [mul_nonneg hc0 hxc, mul_nonneg hc0 hR]

/-- The coarse coefficient `3` is already enough to separate the two
exponential rates. -/
theorem three_sqrt_le_btz {x : ℝ} (hx : 0 ≤ x) :
    3 * sqrt x ≤ 2 * π * sqrt (x / 3) := by
  have hsx := sq_sqrt hx
  have hsd := sq_sqrt (show 0 ≤ x / 3 by positivity)
  have hs : sqrt x ≤ 2 * sqrt (x / 3) := by
    nlinarith [sqrt_nonneg x, sqrt_nonneg (x / 3)]
  have hpi := mul_le_mul_of_nonneg_right (le_of_lt pi_gt_three)
    (sqrt_nonneg (x / 3))
  nlinarith

/-- The linear margin is uniform in every `x ≥ L`; no upper cutoff on the
energy ratio is needed for this estimate. -/
theorem densityError_exponent_le {c x L R D : ℝ} (hc : 1 ≤ c)
    (hL : 0 < L) (hx : L ≤ x) (hR : 0 ≤ R) :
    7 * sqrt (((c - 1) / 12) * (x * c + R)) + D * sqrt c ≤
      2 * π * c * sqrt (x / 3) - (2 / 3 * sqrt L) * c +
        (7 / 3 * sqrt R + |D|) * sqrt c := by
  have hx0 : 0 ≤ x := le_trans hL.le hx
  have hc0 : 0 ≤ c := by linarith
  have hs := densityError_sqrt_le hc hx0 hR
  have hb := mul_le_mul_of_nonneg_right (three_sqrt_le_btz hx0) hc0
  have hLx := mul_le_mul_of_nonneg_right (sqrt_le_sqrt hx) hc0
  have hD := mul_le_mul_of_nonneg_right (le_abs_self D) (sqrt_nonneg c)
  nlinarith

/-- A root-exponential prefactor is eventually absorbed in any positive
linear exponential rate. The threshold is explicit. -/
theorem rootLinear_absorb {A ε c : ℝ} (hA : 0 ≤ A) (hε : 0 < ε)
    (hc : (A / ε) ^ 2 ≤ c) : A * sqrt c ≤ ε * c := by
  have hr : 0 ≤ A / ε := div_nonneg hA hε.le
  have hc0 : 0 ≤ c := (sq_nonneg (A / ε)).trans hc
  have hs : A / ε ≤ sqrt c := by
    simpa only [sqrt_sq hr] using sqrt_le_sqrt hc
  have hAs : A ≤ ε * sqrt c := by
    have := (div_le_iff₀ hε).mp hs
    nlinarith
  have hm := mul_le_mul_of_nonneg_right hAs (sqrt_nonneg c)
  nlinarith [sq_sqrt hc0]

/-- Every inverse power is available while retaining a positive exponential
margin. The threshold is independent of the ratio `x ≥ L`. -/
theorem densityError_eventually_le {L R C D : ℝ} (hL : 0 < L)
    (hR : 0 ≤ R) (hC : 0 ≤ C) (p n : ℕ) :
    ∀ᶠ c : ℝ in atTop, ∀ x : ℝ, L ≤ x →
      C * (1 + c) ^ p * exp (7 * sqrt (((c - 1) / 12) * (x * c + R)) + D * sqrt c) ≤
        exp (2 * π * c * sqrt (x / 3) - (sqrt L / 3) * c) / (1 + c) ^ n := by
  let ε : ℝ := sqrt L / 3
  let A : ℝ := C + 2 * (p + n) + 7 / 3 * sqrt R + |D|
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  filter_upwards [eventually_ge_atTop (max 1 ((A / ε) ^ 2))] with c hc x hx
  have hc1 : 1 ≤ c := (le_max_left _ _).trans hc
  have hc0 : 0 ≤ c := by linarith
  have hcs : (A / ε) ^ 2 ≤ c := (le_max_right _ _).trans hc
  have habsorb := rootLinear_absorb hA hε hcs
  have hsc : 1 ≤ sqrt c := by simpa using sqrt_le_sqrt hc1
  have hCexp : C ≤ exp (C * sqrt c) := by
    have hm := mul_le_mul_of_nonneg_left hsc hC
    exact (show C ≤ C * sqrt c + 1 by nlinarith).trans (add_one_le_exp _)
  have hpoly := one_add_pow_le_exp_sqrt hc0 (p + n)
  push_cast at hpoly
  have hbase := densityError_exponent_le (D := D) hc1 hL hx hR
  apply (le_div_iff₀ (pow_pos (show 0 < 1 + c by linarith) n)).mpr
  calc
    _ = C * (1 + c) ^ (p + n) *
        exp (7 * sqrt (((c - 1) / 12) * (x * c + R)) + D * sqrt c) := by
      rw [pow_add]; ring
    _ ≤ exp (C * sqrt c) * exp ((2 * (p + n)) * sqrt c) *
        exp (7 * sqrt (((c - 1) / 12) * (x * c + R)) + D * sqrt c) := by
      gcongr
    _ = exp (C * sqrt c + (2 * (p + n)) * sqrt c +
        (7 * sqrt (((c - 1) / 12) * (x * c + R)) + D * sqrt c)) := by
      simp only [exp_add]
    _ ≤ _ := by
      apply exp_le_exp.mpr
      dsimp [A, ε] at habsorb
      nlinarith

/-- The repair bound relative to the leading BTZ exponential has every
inverse-power order, with a uniform exponential improvement. -/
theorem densityError_eventually_ratio_le {L R C D : ℝ} (hL : 0 < L)
    (hR : 0 ≤ R) (hC : 0 ≤ C) (p n : ℕ) :
    ∀ᶠ c : ℝ in atTop, ∀ x : ℝ, L ≤ x →
      (C * (1 + c) ^ p *
        exp (7 * sqrt (((c - 1) / 12) * (x * c + R)) + D * sqrt c)) /
          exp (2 * π * c * sqrt (x / 3)) ≤
        exp (-(sqrt L / 3) * c) / (1 + c) ^ n := by
  filter_upwards [densityError_eventually_le (D := D) hL hR hC p n] with c hc x hx
  calc
    _ ≤ (exp (2 * π * c * sqrt (x / 3) - (sqrt L / 3) * c) /
        (1 + c) ^ n) / exp (2 * π * c * sqrt (x / 3)) :=
      div_le_div_of_nonneg_right (hc x hx) (exp_nonneg _)
    _ = _ := by
      rw [exp_sub, neg_mul, exp_neg]
      field_simp

/-- In particular the normalized density error is bounded by any requested
inverse power, uniformly on a positive ratio interval. -/
theorem densityError_eventually_inverse_pow {L R C D : ℝ} (hL : 0 < L)
    (hR : 0 ≤ R) (hC : 0 ≤ C) (p n : ℕ) :
    ∀ᶠ c : ℝ in atTop, ∀ x : ℝ, L ≤ x →
      (C * (1 + c) ^ p *
        exp (7 * sqrt (((c - 1) / 12) * (x * c + R)) + D * sqrt c)) /
          exp (2 * π * c * sqrt (x / 3)) ≤ 1 / c ^ n := by
  filter_upwards [densityError_eventually_ratio_le (D := D) hL hR hC p n,
    eventually_ge_atTop (1 : ℝ)] with c hc hc1 x hx
  have hc0 : 0 ≤ c := by linarith
  have he : exp (-(sqrt L / 3) * c) ≤ 1 := by
    apply exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (div_nonneg (sqrt_nonneg L) (by norm_num))) hc0
  calc
    _ ≤ exp (-(sqrt L / 3) * c) / (1 + c) ^ n := hc x hx
    _ ≤ 1 / (1 + c) ^ n := div_le_div_of_nonneg_right he (by positivity)
    _ ≤ _ := one_div_le_one_div_of_le (pow_pos (by linarith : 0 < c) n)
      (pow_le_pow_left₀ hc0 (by linarith) n)

/-- The same bound holds for every sufficiently large real charge, uniformly
in the energy ratio. The shift in the square root is exactly `a`. -/
theorem densityError_eventually_gapFamilyCharge_le {L R C D : ℝ} (hL : 0 < L)
    (hR : 0 ≤ R) (hC : 0 ≤ C) (p n : ℕ) :
    ∀ᶠ a : ℝ in atTop, ∀ x : ℝ, L ≤ x →
      C * (1 + GapFamily.gapFamilyCharge a) ^ p *
        exp (7 * sqrt (a *
          (x * GapFamily.gapFamilyCharge a + R)) +
            D * sqrt (GapFamily.gapFamilyCharge a)) ≤
        exp (2 * π * GapFamily.gapFamilyCharge a * sqrt (x / 3) -
          (sqrt L / 3) * GapFamily.gapFamilyCharge a) /
            (1 + GapFamily.gapFamilyCharge a) ^ n := by
  have h := GapFamily.tendsto_gapFamilyCharge_atTop.eventually
    (densityError_eventually_le (D := D) hL hR hC p n)
  filter_upwards [h] with a ha x hx
  have hs : (GapFamily.gapFamilyCharge a - 1) / 12 =
      a := by
    unfold GapFamily.gapFamilyCharge
    ring
  simpa only [hs] using ha x hx

end BTZEntropy.Comparison
