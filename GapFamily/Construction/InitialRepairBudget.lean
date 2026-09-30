import GapFamily.Construction.ReferenceErrorAbsorption
import GapFamily.Construction.InitialRepairLogGain
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Numerical budget for the initial repair

A logarithmic approximation gain absorbs the exponential loss of an initial
repair. An explicit factorial threshold then absorbs every fixed polynomial
prefactor, including the number of initial rows.
-/

open Real

namespace GapFamily.Construction

/-- A natural approximation degree absorbs a polynomial prefactor and leaves
one eighth of the normalized repair budget. -/
theorem initialRepair_budget_of_degree {A D X L ρ : ℝ} (p k : ℕ)
    (hA : 0 ≤ A) (hX : 0 ≤ X) (hρ : 0 < ρ)
    (hpoly : X ≤ D * (k : ℝ))
    (hlarge : 8 * (A * D ^ p) * ((p + 1).factorial : ℝ) ≤ k)
    (hgain : L + (k : ℝ) ≤ (k : ℝ) * log ρ) :
    A * X ^ p * exp L / ρ ^ k ≤ 1 / 8 := by
  have hp : (A * D ^ p) * (k : ℝ) ^ p ≤ exp (k : ℝ) / 8 := by
    have h := referenceError_polynomial_absorption
      (Nat.cast_nonneg k) p (K := 2 * (A * D ^ p)) (by nlinarith [hlarge])
    linarith
  have hpoly' : A * X ^ p ≤ exp (k : ℝ) / 8 := by
    calc
      _ ≤ A * (D * (k : ℝ)) ^ p :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hX hpoly p) hA
      _ = (A * D ^ p) * (k : ℝ) ^ p := by rw [mul_pow]; ring
      _ ≤ _ := hp
  apply (div_le_iff₀ (pow_pos hρ k)).2
  calc
    _ ≤ (exp (k : ℝ) / 8) * exp L :=
      mul_le_mul_of_nonneg_right hpoly' (exp_nonneg L)
    _ = exp ((k : ℝ) + L) / 8 := by rw [exp_add]; ring
    _ ≤ exp ((k : ℝ) * log ρ) / 8 :=
      div_le_div_of_nonneg_right (exp_le_exp.mpr (by linarith)) (by norm_num)
    _ = (1 / 8) * ρ ^ k := by rw [← log_pow, exp_log (pow_pos hρ k)]; ring

/-- The initial cutoff contributes at most six times the endpoint scale. -/
theorem initialRepair_cutoff_le {U : ℝ} (hU : 1 ≤ U) :
    2 * U + 4 ≤ 6 * U := by linarith

/-- For the integer construction, the polynomial base is linear in the
approximation degree with a coefficient fixed before the band scale grows. -/
theorem initialRepair_polynomial_base_le {R s n : ℕ}
    (hR : 1 ≤ R) (hs : 1 ≤ s) (hn : 1 ≤ n) :
    1 + (R : ℝ) * (s : ℝ) ^ 2 * n + (2 * ((R : ℝ) * n) + 4) ≤
      ((s : ℝ) + 7) * (R * s * n : ℕ) := by
  have hR' : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hU : (1 : ℝ) ≤ (R : ℝ) * n := by
    nlinarith [mul_nonneg (show 0 ≤ (R : ℝ) - 1 by linarith)
      (show 0 ≤ (n : ℝ) - 1 by linarith)]
  have hk : (R : ℝ) * n ≤ (R : ℝ) * s * n := by nlinarith
  push_cast
  nlinarith

/-- The prescribed logarithmic gain absorbs both the endpoint and cutoff
exponential losses, uniformly in the later integer band scale. -/
theorem initialRepair_exponent_le {Ck CU CB ρ : ℝ} {R s n : ℕ}
    (_hCU : 0 ≤ CU) (hCB : 0 ≤ CB)
    (hR : 1 ≤ R) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hgain : Ck + CU / (s : ℝ) + 6 * CB / (s : ℝ) + 1 ≤ log ρ) :
    Ck * (R * s * n : ℕ) + CU * ((R : ℝ) * n) +
      CB * (2 * ((R : ℝ) * n) + 4) + (R * s * n : ℕ) ≤
        (R * s * n : ℕ) * log ρ := by
  have hR' : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hU : (1 : ℝ) ≤ (R : ℝ) * n := by
    nlinarith [mul_nonneg (show 0 ≤ (R : ℝ) - 1 by linarith)
      (show 0 ≤ (n : ℝ) - 1 by linarith)]
  have hs0 : (s : ℝ) ≠ 0 := by linarith
  have hcut := mul_le_mul_of_nonneg_left (initialRepair_cutoff_le hU) hCB
  have hm := mul_le_mul_of_nonneg_right hgain (Nat.cast_nonneg (R * s * n))
  have heq : (Ck + CU / (s : ℝ) + 6 * CB / (s : ℝ) + 1) *
      (R * s * n : ℕ) = Ck * (R * s * n : ℕ) +
        CU * ((R : ℝ) * n) + 6 * CB * ((R : ℝ) * n) + (R * s * n : ℕ) := by
    push_cast
    field_simp
  rw [heq] at hm
  nlinarith

/-- After the integer ratio is fixed with one unit of logarithmic gain, every
fixed polynomial loss has a proved integer threshold for the initial budget. -/
theorem exists_initialRepair_budget {A Ck CU CB ρ : ℝ} (p : ℕ) {R s : ℕ}
    (hA : 0 ≤ A) (hCU : 0 ≤ CU) (hCB : 0 ≤ CB) (hρ : 0 < ρ)
    (hR : 1 ≤ R) (hs : 1 ≤ s)
    (hgain : Ck + CU / (s : ℝ) + 6 * CB / (s : ℝ) + 1 ≤ log ρ) :
    ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
      A * (1 + (R : ℝ) * (s : ℝ) ^ 2 * n + (2 * ((R : ℝ) * n) + 4)) ^ p *
        exp (Ck * (R * s * n : ℕ) + CU * ((R : ℝ) * n) +
          CB * (2 * ((R : ℝ) * n) + 4)) / ρ ^ (R * s * n) ≤ 1 / 8 := by
  obtain ⟨n₀, hn₀⟩ := exists_nat_ge
    (max 1 (8 * (A * ((s : ℝ) + 7) ^ p) * ((p + 1).factorial : ℝ)))
  have hn₀1 : (1 : ℝ) ≤ n₀ := (le_max_left _ _).trans hn₀
  have hn₀large : 8 * (A * ((s : ℝ) + 7) ^ p) * ((p + 1).factorial : ℝ) ≤ n₀ :=
    (le_max_right _ _).trans hn₀
  refine ⟨n₀, by exact_mod_cast hn₀1, ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := (by exact_mod_cast hn₀1 : 1 ≤ n₀).trans hn
  have hRs : 1 ≤ R * s := one_le_mul_of_one_le_of_one_le hR hs
  have hnk : n ≤ R * s * n := by nlinarith
  apply initialRepair_budget_of_degree p (R * s * n) hA
    (by positivity) hρ (initialRepair_polynomial_base_le hR hs hn1)
  · exact hn₀large.trans (by exact_mod_cast hn.trans hnk)
  · exact initialRepair_exponent_le hCU hCB hR hs hn1 hgain

/-- The ratio is selected using only the fixed exponential losses. Every
larger integer ratio then admits the initial repair budget for every positive
integer reference scale and every fixed polynomial prefactor. -/
theorem exists_initialRepair_budget_ratio {Ck CU CB : ℝ}
    (hCk : 0 ≤ Ck) (hCU : 0 ≤ CU) (hCB : 0 ≤ CB) :
    ∃ s₀ : ℕ, 1 ≤ s₀ ∧ ∀ s : ℕ, s₀ ≤ s →
      2 ≤ initialRepairRatio s ∧ ∀ R : ℕ, 1 ≤ R → ∀ A : ℝ, 0 ≤ A →
        ∀ p : ℕ, ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
          A * (1 + (R : ℝ) * (s : ℝ) ^ 2 * n +
              (2 * ((R : ℝ) * n) + 4)) ^ p *
            exp (Ck * (R * s * n : ℕ) + CU * ((R : ℝ) * n) +
              CB * (2 * ((R : ℝ) * n) + 4)) /
                (initialRepairRatio s) ^ (R * s * n) ≤ 1 / 8 := by
  obtain ⟨s₀, hs₀, hs⟩ := exists_initialRepair_log_gain (H := 1) hCk hCU hCB
  refine ⟨s₀, hs₀, ?_⟩
  intro s hslarge
  obtain ⟨hρ, hgain⟩ := hs s hslarge
  refine ⟨hρ, ?_⟩
  intro R hR A hA p
  exact exists_initialRepair_budget p hA hCU hCB (by linarith) hR
    (hs₀.trans hslarge) hgain

end GapFamily.Construction
