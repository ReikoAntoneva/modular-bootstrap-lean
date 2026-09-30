import GapFamily.Construction.InitialCellMoment
import GapFamily.Construction.ReferenceErrorAbsorption

/-!
# Numerical reserve for the signed initial cell

The upper-half mass grows with exponent `4k`, whereas negative mass costs
`exp k` and extrapolation costs `6^k ≤ exp (2k)`. The strict remaining
exponential gain absorbs every fixed polynomial and gives arbitrarily large
variation reserve. All degree thresholds below are proved to exist.
-/

open Real

namespace GapFamily.Construction

/-- A convenient strict exponential upper bound for Chebyshev extrapolation. -/
theorem initialCell_six_pow_le_exp_two (k : ℕ) :
    (6 : ℝ) ^ k ≤ exp (2 * (k : ℝ)) := by
  have hquadratic := quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num)
  have hexp : 6 ≤ exp (2 : ℝ) := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, exp_add]
    norm_num at hquadratic
    nlinarith [exp_pos (1 : ℝ)]
  calc
    _ ≤ (exp 2) ^ k := pow_le_pow_left₀ (by norm_num) hexp k
    _ = _ := by rw [← exp_nat_mul]; congr 1; ring

/-- Every fixed polynomial in `k+1` is eventually strictly smaller than
`exp k`; the threshold follows directly from one exponential-series term. -/
theorem exists_initialCell_polynomial_threshold (C : ℝ) (p : ℕ) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → C * ((k : ℝ) + 1) ^ p < exp (k : ℝ) := by
  obtain ⟨k₀, hk₀⟩ := exists_nat_ge (4 * (C * exp 1) * ((p + 1).factorial : ℝ))
  refine ⟨k₀, ?_⟩
  intro k hk
  have hcast : (k₀ : ℝ) ≤ k := by exact_mod_cast hk
  have hterm := referenceError_polynomial_absorption
    (show (0 : ℝ) ≤ (k : ℝ) + 1 by positivity) p
    (show 4 * (C * exp 1) * ((p + 1).factorial : ℝ) ≤ (k : ℝ) + 1 by linarith)
  rw [exp_add] at hterm
  have hsmall : C * ((k : ℝ) + 1) ^ p ≤ exp (k : ℝ) / 4 := by
    apply (mul_le_mul_iff_left₀ (exp_pos (1 : ℝ))).mp
    calc
      _ = (C * exp 1) * ((k : ℝ) + 1) ^ p := by ring
      _ ≤ (exp (k : ℝ) * exp 1) / 4 := hterm
      _ = _ := by ring
  exact hsmall.trans_lt (by have := exp_pos (k : ℝ); linarith)

/-- Once the negative polynomial has been absorbed by one unit of exponent,
the actual initial-cell reserve retains two units of exponent. -/
theorem initialCellVariationReserve_lower_of_growth
    {x₀ x₁ A N c B : ℝ} (k p : ℕ) (hc : 0 < c) (hB : 0 ≤ B)
    (hpositive : c * exp (4 * (k : ℝ)) ≤ A * (x₁ - x₀))
    (hnegative : N ≤ B * ((k : ℝ) + 1) ^ p * exp (k : ℝ))
    (hgrowth : 64 * B * ((k : ℝ) + 1) ^ (p + 3) ≤ c * exp (k : ℝ)) :
    c * exp (2 * (k : ℝ)) / (256 * ((k : ℝ) + 1) ^ 6) ≤
      initialCellVariationReserve x₀ x₁ A N k := by
  let t : ℝ := (k : ℝ) + 1
  let z : ℝ := exp (k : ℝ)
  have ht : 0 < t := by dsimp [t]; positivity
  have hz : 0 < z := exp_pos _
  have htwo : exp (2 * (k : ℝ)) = z ^ 2 := exp_nat_mul _ 2
  have hfour : exp (4 * (k : ℝ)) = z ^ 4 := exp_nat_mul _ 4
  have h6 : (6 : ℝ) ^ k ≤ z ^ 2 := htwo ▸ initialCell_six_pow_le_exp_two k
  have hpos : c * z ^ 4 ≤ A * (x₁ - x₀) := hfour ▸ hpositive
  have hneg : N * (6 : ℝ) ^ k ≤ B * t ^ p * z ^ 3 := by
    calc
      _ ≤ (B * t ^ p * z) * (6 : ℝ) ^ k :=
        mul_le_mul_of_nonneg_right hnegative (by positivity)
      _ ≤ (B * t ^ p * z) * z ^ 2 :=
        mul_le_mul_of_nonneg_left h6 (by positivity)
      _ = _ := by ring
  have hneg' : N * (6 : ℝ) ^ k ≤ c * z ^ 4 / (64 * t ^ 3) := by
    apply (le_div_iff₀ (by positivity : 0 < 64 * t ^ 3)).mpr
    calc
      _ ≤ (B * t ^ p * z ^ 3) * (64 * t ^ 3) :=
        mul_le_mul_of_nonneg_right hneg (by positivity)
      _ = (64 * B * t ^ (p + 3)) * z ^ 3 := by rw [pow_add]; ring
      _ ≤ (c * z) * z ^ 3 := mul_le_mul_of_nonneg_right hgrowth (by positivity)
      _ = _ := by ring
  have hmargin : c * z ^ 4 / (64 * t ^ 3) ≤ initialCellMomentMargin x₀ x₁ A N k := by
    have hpos' := div_le_div_of_nonneg_right hpos (by positivity : 0 ≤ 32 * t ^ 3)
    have heq : c * z ^ 4 / (32 * t ^ 3) = 2 * (c * z ^ 4 / (64 * t ^ 3)) := by ring
    rw [heq] at hpos'
    change _ ≤ A * (x₁ - x₀) / (32 * t ^ 3) - N * (6 : ℝ) ^ k
    linarith
  rw [htwo]
  change c * z ^ 2 / (256 * t ^ 6) ≤
    initialCellMomentMargin x₀ x₁ A N k / (4 * t ^ 3 * (6 : ℝ) ^ k)
  apply (le_div_iff₀ (by positivity : 0 < 4 * t ^ 3 * (6 : ℝ) ^ k)).mpr
  calc
    _ ≤ (c * z ^ 2 / (256 * t ^ 6)) * (4 * t ^ 3 * z ^ 2) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left h6 (by positivity)) (by positivity)
    _ = c * z ^ 4 / (64 * t ^ 3) := by field_simp; ring
    _ ≤ _ := hmargin

/-- The numerical initial-cell hypotheses give strict moment positivity and
any prescribed variation reserve, uniformly over all cells and signed masses. -/
theorem exists_initialCell_variation_threshold {c B : ℝ}
    (hc : 0 < c) (hB : 0 ≤ B) (p : ℕ) (β : ℝ) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ x₀ x₁ A N : ℝ,
      c * exp (4 * (k : ℝ)) ≤ A * (x₁ - x₀) →
      N ≤ B * ((k : ℝ) + 1) ^ p * exp (k : ℝ) →
      0 < initialCellMomentMargin x₀ x₁ A N k ∧
        β < initialCellVariationReserve x₀ x₁ A N k := by
  let M : ℝ := max 1 β
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  obtain ⟨k₁, hk₁⟩ := exists_initialCell_polynomial_threshold (64 * B / c) (p + 3)
  obtain ⟨k₂, hk₂⟩ := exists_initialCell_polynomial_threshold (256 * M / c) 6
  refine ⟨max k₁ k₂, ?_⟩
  intro k hk x₀ x₁ A N hpositive hnegative
  have hgrowth : 64 * B * ((k : ℝ) + 1) ^ (p + 3) ≤ c * exp (k : ℝ) := by
    have hh := mul_lt_mul_of_pos_left (hk₁ k ((le_max_left _ _).trans hk)) hc
    have heq : c * ((64 * B / c) * ((k : ℝ) + 1) ^ (p + 3)) =
        64 * B * ((k : ℝ) + 1) ^ (p + 3) := by field_simp
    rw [heq] at hh
    exact hh.le
  have hlower := initialCellVariationReserve_lower_of_growth k p hc hB
    hpositive hnegative hgrowth
  have hMbound : M < c * exp (2 * (k : ℝ)) / (256 * ((k : ℝ) + 1) ^ 6) := by
    apply (lt_div_iff₀ (by positivity : 0 < 256 * ((k : ℝ) + 1) ^ 6)).mpr
    have hh := mul_lt_mul_of_pos_left (hk₂ k ((le_max_right _ _).trans hk)) hc
    have heq : c * ((256 * M / c) * ((k : ℝ) + 1) ^ 6) =
        M * (256 * ((k : ℝ) + 1) ^ 6) := by field_simp
    rw [heq] at hh
    exact hh.trans_le (mul_le_mul_of_nonneg_left
      (exp_le_exp.mpr (by have := Nat.cast_nonneg (α := ℝ) k; linarith)) hc.le)
  have hreserve : M < initialCellVariationReserve x₀ x₁ A N k := hMbound.trans_le hlower
  constructor
  · have hpositiveReserve : 0 < initialCellVariationReserve x₀ x₁ A N k := hM.trans hreserve
    exact (div_pos_iff_of_pos_right (by positivity)).mp hpositiveReserve
  · exact (le_max_right _ _).trans_lt hreserve

end GapFamily.Construction
