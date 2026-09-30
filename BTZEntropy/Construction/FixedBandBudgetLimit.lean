import BTZEntropy.Construction.FixedBandDegree
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
# Vanishing budget at a fixed cutoff

A fixed exponential approximation ratio absorbs every fixed polynomial loss
when the degree grows like the square root of the charge.
-/

noncomputable section

open Filter Real
open scoped Topology

namespace BTZEntropy.Construction

private theorem polynomial_exp_div_pow_le
    {A X F C D L ρ : ℝ} (p k : ℕ)
    (hA : 0 ≤ A) (hX : 0 ≤ X) (hF : 0 ≤ F) (hρ : 0 < ρ)
    (hpoly : X ≤ F * ((k : ℝ) + 1) ^ 2)
    (hL : L ≤ 2 * C * k + D) (hgain : 2 * C + 1 ≤ log ρ) :
    A * X ^ p * exp L / ρ ^ k ≤
      (A * F ^ p * exp D) * (((k : ℝ) + 1) ^ (2 * p) * exp (-(k : ℝ))) := by
  have hexp : exp L / ρ ^ k ≤ exp (D - k) := by
    have hm := mul_le_mul_of_nonneg_right hgain (Nat.cast_nonneg (α := ℝ) k)
    calc
      _ = exp (L - (k : ℝ) * log ρ) := by
        rw [exp_sub, ← log_pow, exp_log (pow_pos hρ k)]
      _ ≤ _ := exp_le_exp.mpr (by nlinarith)
  calc
    _ = (A * X ^ p) * (exp L / ρ ^ k) := by ring
    _ ≤ (A * (F * ((k : ℝ) + 1) ^ 2) ^ p) * exp (D - k) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hX hpoly p) hA)
        hexp (by positivity) (by positivity)
    _ = _ := by rw [mul_pow, ← pow_mul, sub_eq_add_neg, exp_add]; ring

private theorem tendsto_shifted_pow_mul_exp_neg (p : ℕ) :
    Tendsto (fun x : ℝ => (x + 1) ^ p * exp (-x)) atTop (𝓝 0) := by
  have h := (tendsto_pow_mul_exp_neg_atTop_nhds_zero p).comp
    (tendsto_atTop_add_const_right atTop 1 tendsto_id)
  have h' := h.const_mul (exp 1)
  simp only [mul_zero] at h'
  convert h' using 1
  ext x
  dsimp only [Function.comp_def, id_eq]
  rw [show -(x + 1) = -x - 1 by ring, exp_sub]
  field_simp

/-- With the processing endpoint and approximation ratio fixed first, every
fixed polynomial prefactor is absorbed as the charge tends to infinity. -/
theorem tendsto_fixedBand_budget_zero {A B C D U ρ : ℝ} (p : ℕ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hU : 0 < U)
    (hρ : 0 < ρ) (hgain : 2 * C + 1 ≤ log ρ) :
    Tendsto (fun a : ℝ => A * (1 + a + B) ^ p *
      exp (C * sqrt (a * U) + D) / ρ ^ fixedBandDegree a U) atTop (𝓝 0) := by
  let F : ℝ := (1 + B) * (1 + 1 / U)
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hk : Tendsto (fun a : ℝ => (fixedBandDegree a U : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_fixedBandDegree_atTop hU)
  have hupper : Tendsto (fun a : ℝ => (A * F ^ p * exp D) *
      (((fixedBandDegree a U : ℝ) + 1) ^ (2 * p) *
        exp (-(fixedBandDegree a U : ℝ)))) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def] using
      ((tendsto_shifted_pow_mul_exp_neg (2 * p)).comp hk).const_mul
        (A * F ^ p * exp D)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with a ha
    positivity
  · filter_upwards [eventually_ge_atTop (0 : ℝ),
      eventually_fixedBandDegree_large hU 0] with a ha hlarge
    have hpoly : 1 + a + B ≤ F * ((fixedBandDegree a U : ℝ) + 1) ^ 2 := by
      calc
        1 + a + B ≤ (1 + B) * (1 + a) := by nlinarith [mul_nonneg ha hB]
        _ ≤ (1 + B) * ((1 + 1 / U) * ((fixedBandDegree a U : ℝ) + 1) ^ 2) :=
          mul_le_mul_of_nonneg_left (fixedBandDegree_polynomial_base ha hU) (by positivity)
        _ = _ := by dsimp [F]; ring
    have hroot := fixedBandDegree_half_sqrt hlarge.2
    have hL : C * sqrt (a * U) + D ≤ 2 * C * (fixedBandDegree a U : ℝ) + D := by
      nlinarith [mul_le_mul_of_nonneg_left hroot hC]
    exact polynomial_exp_div_pow_le p (fixedBandDegree a U)
      hA (by positivity) hF hρ hpoly hL hgain

/-- Any prescribed positive numerical budget is eventually valid with a
single charge threshold. -/
theorem eventually_fixedBand_budget_le {A B C D U ρ ε : ℝ} (p : ℕ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hU : 0 < U)
    (hρ : 0 < ρ) (hgain : 2 * C + 1 ≤ log ρ) (hε : 0 < ε) :
    ∀ᶠ a : ℝ in atTop, A * (1 + a + B) ^ p *
      exp (C * sqrt (a * U) + D) / ρ ^ fixedBandDegree a U ≤ ε := by
  exact ((tendsto_fixedBand_budget_zero p hA hB hC hU hρ hgain).eventually
    (gt_mem_nhds hε)).mono fun _ h => h.le

end BTZEntropy.Construction
