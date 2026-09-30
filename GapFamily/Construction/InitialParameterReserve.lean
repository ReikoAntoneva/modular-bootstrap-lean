import GapFamily.Construction.InitialParameter
import GapFamily.Construction.InitialCellNumerical

/-!
# Initial-cell reserve at the integer construction parameters

The exact identities `sqrt(a U) = k` and `C_N sqrt(a b) ≤ k` convert the
physical positive and negative mass budgets to the proved numerical reserve.
The factor `1+a` contributes only a fixed polynomial coefficient in `s`.
-/

open Real

namespace GapFamily.Construction

/-- The integer degree is at least the large parameter `n`. -/
theorem initialParameter_degree_ge {R s : ℕ} (hR : 1 ≤ R) (hs : 1 ≤ s) (n : ℕ) :
    n ≤ R * s * n := by
  have hRs : 1 ≤ R * s := by simpa using Nat.mul_le_mul hR hs
  simpa only [one_mul] using Nat.mul_le_mul_right n hRs

/-- The vacuum polynomial factor is bounded by a fixed multiple of `k+1`. -/
theorem initialParameter_polynomial_base_le (R n : ℕ) {s : ℕ} (hs : 1 ≤ s) :
    1 + ((R * s ^ 2 * n : ℕ) : ℝ) ≤
      (s : ℝ) * (((R * s * n : ℕ) : ℝ) + 1) := by
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  push_cast
  nlinarith

/-- The physical negative-mass budget has the numerical form required by
the initial-cell reserve theorem. -/
theorem initialParameter_negative_budget_le (R s n : ℕ) (hs : 1 ≤ s)
    {B C_N N : ℝ} (hB : 0 ≤ B) (hC : C_N ≤ sqrt (R : ℝ)) (p : ℕ)
    (hnegative : N ≤ B * (1 + ((R * s ^ 2 * n : ℕ) : ℝ)) ^ p *
      exp (C_N * sqrt (((R * s ^ 2 * n : ℕ) : ℝ) * (n : ℝ)))) :
    N ≤ (B * (s : ℝ) ^ p) * (((R * s * n : ℕ) : ℝ) + 1) ^ p *
      exp (((R * s * n : ℕ) : ℝ)) := by
  have hpoly : (1 + ((R * s ^ 2 * n : ℕ) : ℝ)) ^ p ≤
      (s : ℝ) ^ p * (((R * s * n : ℕ) : ℝ) + 1) ^ p := by
    calc
      _ ≤ ((s : ℝ) * (((R * s * n : ℕ) : ℝ) + 1)) ^ p :=
        pow_le_pow_left₀ (by positivity) (initialParameter_polynomial_base_le R n hs) p
      _ = _ := mul_pow _ _ _
  have hexp : exp (C_N * sqrt (((R * s ^ 2 * n : ℕ) : ℝ) * (n : ℝ))) ≤
      exp (((R * s * n : ℕ) : ℝ)) :=
    exp_le_exp.mpr (initialParameter_negative_exponent_le R s n hC)
  refine hnegative.trans ?_
  calc
    _ ≤ B * ((s : ℝ) ^ p * (((R * s * n : ℕ) : ℝ) + 1) ^ p) *
        exp (((R * s * n : ℕ) : ℝ)) := by gcongr
    _ = _ := by ring

/-- The physical initial-cell budgets eventually give strict moment
positivity and any prescribed variation reserve at the construction's
natural parameters. The threshold is proved to exist. -/
theorem exists_initialParameter_variation_threshold
    (R s : ℕ) (hR : 1 ≤ R) (hs : 1 ≤ s) {c B C_N : ℝ}
    (hc : 0 < c) (hB : 0 ≤ B) (hC : C_N ≤ sqrt (R : ℝ)) (p : ℕ) (β : ℝ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ x₀ x₁ A N : ℝ,
      c * exp (4 * sqrt (((R * s ^ 2 * n : ℕ) : ℝ) * ((R * n : ℕ) : ℝ))) ≤
        A * (x₁ - x₀) →
      N ≤ B * (1 + ((R * s ^ 2 * n : ℕ) : ℝ)) ^ p *
        exp (C_N * sqrt (((R * s ^ 2 * n : ℕ) : ℝ) * (n : ℝ))) →
      0 < initialCellMomentMargin x₀ x₁ A N (R * s * n) ∧
        β < initialCellVariationReserve x₀ x₁ A N (R * s * n) := by
  obtain ⟨k₀, hk₀⟩ := exists_initialCell_variation_threshold hc
    (show 0 ≤ B * (s : ℝ) ^ p by positivity) p β
  refine ⟨k₀, ?_⟩
  intro n hn x₀ x₁ A N hpositive hnegative
  apply hk₀ (R * s * n) (hn.trans (initialParameter_degree_ge hR hs n)) x₀ x₁ A N
  · simpa only [initialParameter_sqrt_aU] using hpositive
  · exact initialParameter_negative_budget_le R s n hs hB hC p hnegative

end GapFamily.Construction
