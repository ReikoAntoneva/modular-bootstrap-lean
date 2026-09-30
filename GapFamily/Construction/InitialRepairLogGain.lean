import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Logarithmic gain from the initial repair ratio

Increasing the integer ratio makes its logarithm dominate any fixed loss.
The threshold is chosen before the later band parameter, so the resulting
gain is uniform in that parameter.
-/

open Real

namespace GapFamily.Construction

/-- The initial-cell length ratio used in the repair remainder estimate. -/
noncomputable def initialRepairRatio (s : ℕ) : ℝ :=
  (1 / 100 : ℝ) * (s : ℝ) / sqrt 2

/-- An integer threshold makes the logarithm of the repair ratio dominate
any prescribed real constant, while keeping the ratio at least two. -/
theorem exists_initialRepair_log_gain_constant (T : ℝ) :
    ∃ s₀ : ℕ, 1 ≤ s₀ ∧ ∀ s : ℕ, s₀ ≤ s →
      2 ≤ initialRepairRatio s ∧ T ≤ log (initialRepairRatio s) := by
  obtain ⟨s₀, hs₀⟩ := exists_nat_ge (max 1 (100 * sqrt 2 * max 2 (exp T)))
  have hs₀1 : (1 : ℝ) ≤ s₀ := (le_max_left _ _).trans hs₀
  refine ⟨s₀, by exact_mod_cast hs₀1, ?_⟩
  intro s hs
  have hsreal : (s₀ : ℝ) ≤ s := by exact_mod_cast hs
  have hlarge : 100 * sqrt 2 * max 2 (exp T) ≤ (s : ℝ) :=
    ((le_max_right _ _).trans hs₀).trans hsreal
  have hratio : max 2 (exp T) ≤ initialRepairRatio s := by
    unfold initialRepairRatio
    apply (le_div_iff₀ (show 0 < sqrt 2 by positivity)).mpr
    nlinarith
  refine ⟨(le_max_left _ _).trans hratio, ?_⟩
  have hlog := log_le_log (exp_pos T) ((le_max_right _ _).trans hratio)
  simpa only [log_exp] using hlog

/-- The chosen integer ratio absorbs both constant losses and the losses
divided by that ratio. -/
theorem exists_initialRepair_log_gain {Ck CU CB H : ℝ}
    (_hCk : 0 ≤ Ck) (hCU : 0 ≤ CU) (hCB : 0 ≤ CB) :
    ∃ s₀ : ℕ, 1 ≤ s₀ ∧ ∀ s : ℕ, s₀ ≤ s →
      2 ≤ initialRepairRatio s ∧
        Ck + CU / (s : ℝ) + 6 * CB / (s : ℝ) + H ≤
          log (initialRepairRatio s) := by
  obtain ⟨s₀, hs₀1, hgain⟩ :=
    exists_initialRepair_log_gain_constant (Ck + CU + 6 * CB + H)
  refine ⟨s₀, hs₀1, ?_⟩
  intro s hs
  obtain ⟨hratio, hlog⟩ := hgain s hs
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs₀1.trans hs
  have hCUdiv : CU / (s : ℝ) ≤ CU := div_le_self hCU hs1
  have hCBdiv : 6 * CB / (s : ℝ) ≤ 6 * CB := div_le_self (by positivity) hs1
  exact ⟨hratio, by linarith⟩

end GapFamily.Construction
