import GapFamily.Construction.ProportionalParameter
import GapFamily.Construction.InitialRepairBudget

/-!
# Initial repair budget for every sufficiently large real charge

The rounded degree changes the endpoint and repair-band constants by a
factor of two. A single auxiliary ratio absorbs these fixed losses before
the polynomial prefactor or the proportional gap is chosen.
-/

open Real

namespace GapFamily.Construction

theorem proportionalRepair_polynomial_base_le {a : ℝ} {s : ℕ}
    (hs : 1 ≤ s) (hlarge : 2 ≤ a / s) (hU : 1 ≤ proportionalCutoff a s) :
    1 + a + (2 * proportionalCutoff a s + 4) ≤
      (2 * (s : ℝ) + 14) * (proportionalDegree a s : ℝ) := by
  have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hk1 : (1 : ℝ) ≤ (proportionalDegree a s : ℝ) := by
    have h : 1 ≤ proportionalDegree a s := Nat.one_le_floor_iff _ |>.mpr (by linarith)
    exact_mod_cast h
  have ha := proportionalParameter_charge_le_degree hs hlarge
  have hb := proportionalParameter_scaled_repairBand_le hs hlarge hU
  have hband0 : 0 ≤ 2 * proportionalCutoff a s + 4 := by linarith
  have hband := mul_le_mul_of_nonneg_right hs' hband0
  nlinarith

theorem proportionalRepair_exponent_le {a Ck CU CB ρ : ℝ} {s : ℕ}
    (hCU : 0 ≤ CU) (hCB : 0 ≤ CB) (hs : 1 ≤ s)
    (hlarge : 2 ≤ a / s) (hU : 1 ≤ proportionalCutoff a s)
    (hgain : Ck + 2 * CU / (s : ℝ) + 12 * CB / (s : ℝ) + 1 ≤ log ρ) :
    Ck * (proportionalDegree a s : ℝ) + CU * proportionalCutoff a s +
      CB * (2 * proportionalCutoff a s + 4) + (proportionalDegree a s : ℝ) ≤
        (proportionalDegree a s : ℝ) * log ρ := by
  have hspos : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hcut : proportionalCutoff a s ≤ 2 * (proportionalDegree a s : ℝ) / s := by
    apply (le_div_iff₀ hspos).mpr
    simpa only [mul_comm] using proportionalParameter_scaled_cutoff_le_degree hs hlarge
  have hband : 2 * proportionalCutoff a s + 4 ≤
      12 * (proportionalDegree a s : ℝ) / s := by
    apply (le_div_iff₀ hspos).mpr
    simpa only [mul_comm] using proportionalParameter_scaled_repairBand_le hs hlarge hU
  have hcut' := mul_le_mul_of_nonneg_left hcut hCU
  have hband' := mul_le_mul_of_nonneg_left hband hCB
  have hgain' := mul_le_mul_of_nonneg_right hgain
    (Nat.cast_nonneg (proportionalDegree a s) : (0 : ℝ) ≤ _)
  calc
    _ ≤ (Ck + 2 * CU / (s : ℝ) + 12 * CB / (s : ℝ) + 1) *
        (proportionalDegree a s : ℝ) := by
      calc
        _ ≤ Ck * (proportionalDegree a s : ℝ) +
            CU * (2 * (proportionalDegree a s : ℝ) / s) +
            CB * (12 * (proportionalDegree a s : ℝ) / s) +
            (proportionalDegree a s : ℝ) := by linarith
        _ = _ := by ring
    _ ≤ _ := by simpa only [mul_comm (log ρ)] using hgain'

/-- Every polynomial prefactor has a threshold on all real charges,
once the fixed logarithmic gain is available. -/
theorem exists_proportionalRepair_budget {A Ck CU CB ρ : ℝ} {s : ℕ} (p : ℕ)
    (hA : 0 ≤ A) (hCU : 0 ≤ CU) (hCB : 0 ≤ CB) (hρ : 0 < ρ) (hs : 1 ≤ s)
    (hgain : Ck + 2 * CU / (s : ℝ) + 12 * CB / (s : ℝ) + 1 ≤ log ρ) :
    ∃ a₀ : ℝ, 1 ≤ a₀ ∧ ∀ a : ℝ, a₀ ≤ a →
      A * (1 + a +
          (2 * proportionalCutoff a s + 4)) ^ p *
        exp (Ck * (proportionalDegree a s : ℝ) +
          CU * proportionalCutoff a s +
          CB * (2 * proportionalCutoff a s + 4)) /
          ρ ^ proportionalDegree a s ≤ 1 / 8 := by
  obtain ⟨n, hn⟩ := exists_nat_ge
    (8 * (A * (2 * (s : ℝ) + 14) ^ p) * ((p + 1).factorial : ℝ))
  obtain ⟨a₁, ha₁pos, ha₁⟩ := exists_proportionalParameter_degree_threshold hs n
  obtain ⟨a₂, _, ha₂⟩ := exists_proportionalParameter_charge_threshold ((s : ℝ) ^ 2)
  refine ⟨max a₁ a₂, ha₁pos.trans (le_max_left _ _), ?_⟩
  intro a ha
  obtain ⟨hk, hlarge⟩ := ha₁ a ((le_max_left _ _).trans ha)
  have hcharge := ha₂ a ((le_max_right _ _).trans ha)
  have hspos : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hU : 1 ≤ proportionalCutoff a s := by
    unfold proportionalCutoff
    exact (le_div_iff₀ (by positivity)).mpr (by simpa using hcharge)
  apply initialRepair_budget_of_degree p (proportionalDegree a s)
    hA (by
      have ha0 : 0 ≤ a := (sq_nonneg (s : ℝ)).trans hcharge
      unfold proportionalCutoff
      positivity) hρ
    (proportionalRepair_polynomial_base_le hs hlarge hU)
  · exact hn.trans (by exact_mod_cast hk)
  · exact proportionalRepair_exponent_le hCU hCB hs hlarge hU hgain

/-- The auxiliary ratio is selected before every later polynomial loss;
the choice is also independent of the proportional-gap parameter. -/
theorem exists_proportionalRepair_budget_ratio {Ck CU CB : ℝ}
    (hCk : 0 ≤ Ck) (hCU : 0 ≤ CU) (hCB : 0 ≤ CB) :
    ∃ s₀ : ℕ, 1 ≤ s₀ ∧ ∀ s : ℕ, s₀ ≤ s →
      2 ≤ initialRepairRatio s ∧
        Ck + 2 * CU / (s : ℝ) + 12 * CB / (s : ℝ) + 1 ≤
          log (initialRepairRatio s) ∧
        ∀ A : ℝ, 0 ≤ A → ∀ p : ℕ,
          ∃ a₀ : ℝ, 1 ≤ a₀ ∧ ∀ a : ℝ, a₀ ≤ a →
            A * (1 + a +
                (2 * proportionalCutoff a s + 4)) ^ p *
              exp (Ck * (proportionalDegree a s : ℝ) +
                CU * proportionalCutoff a s +
                CB * (2 * proportionalCutoff a s + 4)) /
                (initialRepairRatio s) ^ proportionalDegree a s ≤
                  1 / 8 := by
  obtain ⟨s₀, hs₀, hgain⟩ := exists_initialRepair_log_gain
    (CU := 2 * CU) (CB := 2 * CB) (H := 1) hCk (by positivity) (by positivity)
  refine ⟨s₀, hs₀, ?_⟩
  intro s hs
  obtain ⟨hρ, hlog⟩ := hgain s hs
  have hlog' : Ck + 2 * CU / (s : ℝ) + 12 * CB / (s : ℝ) + 1 ≤
      log (initialRepairRatio s) := by
    convert hlog using 1
    ring
  refine ⟨hρ, hlog', ?_⟩
  intro A hA p
  exact exists_proportionalRepair_budget p hA hCU hCB (by linarith) (hs₀.trans hs) hlog'

end GapFamily.Construction
