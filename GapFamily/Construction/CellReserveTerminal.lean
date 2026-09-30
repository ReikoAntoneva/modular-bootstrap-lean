import GapFamily.Construction.CellCoordinateGeometry
import GapFamily.Construction.TailReserve

/-! Uniform terminal-half mass for the actual tail-cell exponential coefficients. -/

noncomputable section

open Set Filter Real
open scoped Topology

namespace GapFamily.Construction

/-- A scalar dominance condition yields a uniform lower bound for terminal-half mass. -/
theorem terminal_cell_mass_lower_bound {r L c P H : ℝ}
    (hr : 0 ≤ r) (hrL : r ≤ L) (hL : 1 ≤ L) (hc : 0 ≤ c) (hP : 0 ≤ P)
    (hdom : 4 * H ≤ c * L * P) :
    c * P / 16 ≤
      ((2 * c * P * sqrt L) * (L + 1 / 2 - r) - 2 * H / sqrt L) *
        (rootCoord r (L + 1) - rootCoord r (L + 1 / 2)) := by
  have hL0 : 0 ≤ L := by linarith
  have hs : 0 < sqrt L := sqrt_pos.mpr (by linarith)
  have hs2 := sq_sqrt hL0
  have hcP : 0 ≤ c * P := mul_nonneg hc hP
  have herror : 2 * H / sqrt L ≤ c * P * sqrt L / 2 := by
    apply (div_le_iff₀ hs).mpr
    nlinarith
  have hpositive : c * P * sqrt L ≤ (2 * c * P * sqrt L) * (L + 1 / 2 - r) := by
    have := mul_nonneg (mul_nonneg hcP hs.le) (sub_nonneg.mpr hrL)
    nlinarith
  have hfactor : c * P * sqrt L / 2 ≤
      (2 * c * P * sqrt L) * (L + 1 / 2 - r) - 2 * H / sqrt L := by
    linarith
  have hd := (tail_cellCoordinateLength_bounds (r := r) (L := L + 1 / 2) (V := L + 1)
    hr (by linarith) (by norm_num) (by norm_num)).1
  have ht : 0 < sqrt (L + 1 / 2 + 1) := sqrt_pos.mpr (by linarith)
  have hcap : sqrt (L + 1 / 2 + 1) ≤ 2 * sqrt L := by
    apply (sq_le_sq₀ (sqrt_nonneg _) (by positivity)).mp
    rw [sq_sqrt (by linarith), mul_pow, hs2]
    nlinarith
  let d := rootCoord r (L + 1) - rootCoord r (L + 1 / 2)
  have hd0 : 0 ≤ d := by
    dsimp [d, rootCoord]
    exact sub_nonneg.mpr (sqrt_le_sqrt (by linarith))
  have hdunit : 1 ≤ d * (8 * sqrt L) := by
    have hfirst : 1 ≤ d * (4 * sqrt (L + 1 / 2 + 1)) :=
      (div_le_iff₀ (mul_pos (by norm_num) ht)).mp hd
    exact hfirst.trans (mul_le_mul_of_nonneg_left (by linarith) hd0)
  calc
    c * P / 16 ≤ (c * P * sqrt L / 2) * d := by
      have := mul_le_mul_of_nonneg_left hdunit hcP
      nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_right hfactor hd0

/-- The actual exponential coefficients eventually satisfy terminal mass conditions uniformly
over every energy above a fixed positive charge ray. -/
theorem eventually_tail_terminal_conditions {c t : ℝ} (hc : 0 < c) (ht : 0 < t) :
    ∀ᶠ a : ℝ in atTop, ∀ L : ℝ, t * a ≤ L →
      1 ≤ L ∧
      4 * exp (7 * sqrt (a * (L + 1))) ≤ c * L * exp (8 * sqrt (a * L)) ∧
      16 < c * exp (8 * sqrt (a * L)) := by
  filter_upwards [eventually_tail_exponential_dominates ht (show 0 < 4 / c by positivity),
    eventually_tail_reserve_ge_uniform ht (32 / c),
    eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (1 / t)] with a hdom hreserve ha htbound
  intro L hL
  have hL1 : 1 ≤ L := by
    have hta : 1 ≤ t * a := by
      simpa only [mul_comm] using (div_le_iff₀ ht).mp htbound
    exact hta.trans hL
  let P := exp (8 * sqrt (a * L))
  let H := exp (7 * sqrt (a * (L + 1)))
  have hP : 0 ≤ P := exp_nonneg _
  have hH : 0 ≤ H := exp_nonneg _
  have hsum : 1 ≤ a + L := by linarith
  have hpow6 : 1 ≤ (a + L) ^ 6 := one_le_pow₀ hsum
  have hsmall : (4 / c) * H ≤ P := by
    apply le_trans _ (hdom L hL)
    simpa only [mul_one] using mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow6 (show 0 ≤ 4 / c by positivity)) hH
  have hfour : 4 * H ≤ c * P := by
    have hscaled := mul_le_mul_of_nonneg_left hsmall hc.le
    have heq : c * (4 / c * H) = 4 * H := by field_simp
    simpa only [heq] using hscaled
  have hdominates : 4 * H ≤ c * L * P := by
    apply hfour.trans
    have := mul_nonneg (mul_nonneg hc.le hP) (sub_nonneg.mpr hL1)
    nlinarith
  have hden : 1 ≤ (L + 1) * (a + L) ^ 12 := by
    calc
      (1 : ℝ) = 1 * 1 := by norm_num
      _ ≤ (L + 1) * (a + L) ^ 12 :=
        mul_le_mul (by linarith) (one_le_pow₀ hsum) (by norm_num) (by linarith)
  have hPlarge : 32 / c ≤ P :=
    (hreserve L hL).trans (div_le_self hP hden)
  have hcPlarge : 32 ≤ c * P := by
    simpa only [mul_comm] using (div_le_iff₀ hc).mp hPlarge
  exact ⟨hL1, hdominates, by linarith⟩

/-- The terminal-half product exceeds one for all physical spins and all unbounded tail
energies at one sufficiently large charge threshold. -/
theorem eventually_tail_terminal_mass_gt_one {c t : ℝ} (hc : 0 < c) (ht : 0 < t) :
    ∀ᶠ a : ℝ in atTop, ∀ L : ℝ, t * a ≤ L → ∀ r : ℝ, 0 ≤ r → r ≤ L →
      1 <
        ((2 * c * exp (8 * sqrt (a * L)) * sqrt L) * (L + 1 / 2 - r) -
          2 * exp (7 * sqrt (a * (L + 1))) / sqrt L) *
            (rootCoord r (L + 1) - rootCoord r (L + 1 / 2)) := by
  filter_upwards [eventually_tail_terminal_conditions hc ht] with a ha
  intro L hL r hr hrL
  obtain ⟨hL1, hdom, hlarge⟩ := ha L hL
  have hbound := terminal_cell_mass_lower_bound hr hrL hL1 hc.le
    (exp_nonneg (8 * sqrt (a * L))) hdom
  exact lt_of_lt_of_le (by linarith : 1 < c * exp (8 * sqrt (a * L)) / 16) hbound

end GapFamily.Construction
