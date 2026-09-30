import BTZEntropy.Construction.FixedBandTailReserve
import GapFamily.Construction.RealTailCell

/-! Actual signed tail cells above a fixed energy threshold. The threshold
does not grow with the charge; only the charge required for the reserve does. -/

noncomputable section
open Set MeasureTheory Real Filter
open GapFamily.Analytic GapFamily.Construction

namespace BTZEntropy.Construction

/-- The terminal half-cell has mass greater than one uniformly above a fixed
threshold, including at arbitrarily large spin and energy. -/
theorem eventually_fixedTail_terminal_mass_gt_one {T c : ℝ}
    (hT : 10 ≤ T) (hc : 0 < c) :
    ∀ᶠ a : ℝ in atTop, ∀ L : ℝ, T ≤ L → ∀ r : ℝ, 0 ≤ r → r ≤ L →
      1 <
        ((2 * c * exp (8 * sqrt (a * L)) * sqrt L) * (L + 1 / 2 - r) -
          2 * exp (7 * sqrt (a * (L + 1))) / sqrt L) *
            (rootCoord r (L + 1) - rootCoord r (L + 1 / 2)) := by
  filter_upwards [eventually_fixedTail_exponential_dominates hT
    (show 0 < 4 / c by positivity),
    eventually_fixedTail_reserve_ge_uniform hT (32 / c),
    eventually_ge_atTop (1 : ℝ)] with a hdom hreserve ha
  intro L hTL r hr hrL
  have hL : 1 ≤ L := by linarith
  let P := exp (8 * sqrt (a * L))
  let H := exp (7 * sqrt (a * (L + 1)))
  have hP : 0 ≤ P := exp_nonneg _
  have hH : 0 ≤ H := exp_nonneg _
  have hsum : 1 ≤ a + L := by linarith
  have hpow : 1 ≤ (a + L) ^ 6 := one_le_pow₀ hsum
  have hsmall : (4 / c) * H ≤ P := by
    apply le_trans _ (hdom L hTL)
    simpa only [mul_one] using mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow (show 0 ≤ 4 / c by positivity)) hH
  have hfour : 4 * H ≤ c * P := by
    have hscaled := mul_le_mul_of_nonneg_left hsmall hc.le
    have heq : c * (4 / c * H) = 4 * H := by field_simp
    simpa only [heq] using hscaled
  have hdominates : 4 * H ≤ c * L * P := by
    apply hfour.trans
    have := mul_nonneg (mul_nonneg hc.le hP) (sub_nonneg.mpr hL)
    nlinarith
  have hden : 1 ≤ (L + 1) * (a + L) ^ 12 := by
    calc
      (1 : ℝ) = 1 * 1 := by norm_num
      _ ≤ (L + 1) * (a + L) ^ 12 :=
        mul_le_mul (by linarith) (one_le_pow₀ hsum) (by norm_num) (by linarith)
  have hPlarge : 32 / c ≤ P :=
    (hreserve L hTL).trans (div_le_self hP hden)
  have hcPlarge : 32 ≤ c * P := by
    simpa only [mul_comm] using (div_le_iff₀ hc).mp hPlarge
  exact lt_of_lt_of_le (by linarith : 1 < c * P / 16)
    (terminal_cell_mass_lower_bound hr hrL hL hc.le hP hdominates)

/-- Every prescribed degree on the linear charge-plus-energy scale has the
positive shortest-cell reserve required by signed quadrature. -/
theorem eventually_fixedTail_shortest_cell_reserve_gt_half
    {T c D : ℝ} (hT : 10 ≤ T) (hc : 0 < c) (hD : 0 < D) :
    ∀ᶠ a : ℝ in atTop, ∀ L : ℝ, T ≤ L → ∀ r : ℝ, 0 ≤ r → r ≤ L →
      ∀ k : ℕ, (k : ℝ) + 1 ≤ D * (a + L) →
        1 / 2 <
          ((2 * c * exp (8 * sqrt (a * L)) * sqrt L) *
              (cellCoordinateLength r L (L + 1 / 2)) ^ 2 /
              (8192 * ((k : ℝ) + 1) ^ 6) -
              2 * exp (7 * sqrt (a * (L + 1))) / sqrt L) *
            cellCoordinateLength r L (L + 1 / 2) / (64 * ((k : ℝ) + 1) ^ 6) := by
  filter_upwards [eventually_fixedTail_exponential_dominates hT
      (show 0 < 1048576 * D ^ 6 / c by positivity),
    eventually_fixedTail_reserve_ge_uniform hT (268435456 * D ^ 12 / c),
    eventually_ge_atTop (1 : ℝ)] with a hdom hlarge ha
  intro L hTL r hr hrL k hk
  exact lt_of_lt_of_le (by norm_num) (shortest_cell_reserve_ge_one_of_growth
    ha (by linarith) hr hrL hc hD (exp_nonneg _) (exp_nonneg _) hk
    (hdom L hTL) (hlarge L hTL))

/-- The actual signed density, rather than a positivity assumption, supplies
the fixed-threshold unit-node cells with exact moments. -/
theorem eventually_fixedTail_hasTailCell {T D : ℝ} (hT : 10 ≤ T) (hD : 0 < D) :
    ∀ᶠ a : ℝ in atTop, ∀ L : ℝ, T ≤ L →
      ∀ j : ℤ, |(j : ℝ)| ≤ L → ∀ k : ℕ, (k : ℝ) + 1 ≤ D * (a + L) →
      ∀ q : ℝ → ℝ, IntegrableOn q (Ioo L (L + 1)) (referenceMeasure j) →
        (∀ E ∈ Icc L (L + 1),
          |q E - vacuumLeading a E j| ≤ exp (7 * sqrt (a * E))) →
        HasTailCell j L k q := by
  have hc : 0 < 2 * π ^ 4 / 625 := by positivity
  filter_upwards [eventually_fixedTail_terminal_mass_gt_one hT hc,
    eventually_fixedTail_shortest_cell_reserve_gt_half hT hc hD,
    eventually_ge_atTop (100 : ℝ)] with a hterminal hreserve ha
  intro L hTL j hj k hk q hq herror
  exact exists_physical_cell_canceling_residual j (by linarith) hj
    (by linarith) (by linarith) hc.le (exp_nonneg _) (exp_nonneg _) q hq
    (cell_numerator_lower_bound_of_vacuum_error j ha hj q herror)
    (hterminal L hTL |(j : ℝ)| (abs_nonneg _) hj)
    (hreserve L hTL |(j : ℝ)| (abs_nonneg _) hj k hk)

/-- Actual fixed-threshold cells retain the ordinary total-variation bounds
used by canonical repair. -/
theorem eventually_fixedTail_exists_tailCell {T D : ℝ}
    (hT : 10 ≤ T) (hD : 0 < D) :
    ∀ᶠ a : ℝ in atTop, ∀ L : ℝ, T ≤ L →
      ∀ j : ℤ, |(j : ℝ)| ≤ L → ∀ k : ℕ, (k : ℝ) + 1 ≤ D * (a + L) →
      ∀ q : ℝ → ℝ, IntegrableOn q (Ioo L (L + 1)) (referenceMeasure j) →
      (∀ E ∈ Icc L (L + 1),
        |q E - vacuumLeading a E j| ≤ exp (7 * sqrt (a * E))) →
      ∃ cell : TailCell j L k q,
        cell.residual.variation.real univ ≤ 12 * exp (4 * π * (a + L)) ∧
        log (2 + cell.residual.variation.real univ) ≤ (4 * π + 14) * (a + L) := by
  filter_upwards [eventually_fixedTail_hasTailCell hT hD,
    eventually_ge_atTop (100 : ℝ)] with a hcell ha
  intro L hTL j hj k hk q hq herror
  obtain ⟨cell⟩ := nonempty_tailCell_of_hasTailCell hq
    (hcell L hTL j hj k hk q hq herror)
  exact ⟨cell, cell.variation_le ha (by linarith) hj herror,
    cell.log_variation_le ha (by linarith) hj herror⟩

/-- A fixed starting energy supports every rounded real-charge tail moment
schedule at one charge threshold, uniformly over all subsequent layers. -/
theorem eventually_fixedTail_realTailCell {T : ℝ} (hT : 10 ≤ T)
    {K : ℕ} (hK : 0 < K) :
    ∀ᶠ a : ℝ in atTop, ∀ m : ℕ, ∀ L : ℝ, T ≤ L →
      (m : ℝ) ≤ L → L < (m : ℝ) + 1 →
      ∀ j : ℤ, |(j : ℝ)| ≤ L →
      ∀ q : ℝ → ℝ, IntegrableOn q (Ioo L (L + 1)) (referenceMeasure j) →
      (∀ E ∈ Icc L (L + 1),
        |q E - vacuumLeading a E j| ≤ exp (7 * sqrt (a * E))) →
      1 ≤ realTailMomentDegree K a m ∧
      ∃ cell : TailCell j L (realTailMomentDegree K a m) q,
        cell.residual.variation.real univ ≤ 12 * exp (4 * π * (a + L)) ∧
        log (2 + cell.residual.variation.real univ) ≤ (4 * π + 14) * (a + L) := by
  filter_upwards [eventually_fixedTail_exists_tailCell hT
    (show 0 < 3 * ((K : ℝ) + 1) by positivity), eventually_ge_atTop (1 : ℝ)]
      with a hcell ha
  intro m L hTL hmL _ j hj q hq herror
  exact ⟨realTailMomentDegree_pos hK a,
    hcell L hTL j hj _ (realTailMomentDegree_add_one_le ha hmL) q hq herror⟩

end BTZEntropy.Construction
