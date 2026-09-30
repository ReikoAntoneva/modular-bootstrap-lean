import GapFamily.Construction.CellReserveBound

/-!
# Uniform numerical reserve on every unbounded tail cell

The degree is bounded by a fixed multiple of `a+L`. The existing uniform
exponential estimates supply the numerical C3 inequality, without an oracle.
-/

open Set Real Filter
open scoped Topology

namespace GapFamily.Construction

/-- Explicit exponential dominance and growth supply the actual shortest-cell
reserve for every degree below the prescribed linear scale. -/
theorem shortest_cell_reserve_ge_one_of_growth
    {a L r c D P H : ℝ} {k : ℕ}
    (ha : 1 ≤ a) (hL : 1 ≤ L) (hr : 0 ≤ r) (hrL : r ≤ L)
    (hc : 0 < c) (hD : 0 < D) (hP : 0 ≤ P) (hH : 0 ≤ H)
    (hk : (k : ℝ)+1 ≤ D*(a+L))
    (hdom : (1048576*D^6/c)*(a+L)^6*H ≤ P)
    (hlarge : 268435456*D^12/c ≤ P/((L+1)*(a+L)^12)) :
    1 ≤ ((2*c*P*sqrt L)*(cellCoordinateLength r L (L+1/2))^2/
          (8192*((k : ℝ)+1)^6)-2*H/sqrt L)*
        cellCoordinateLength r L (L+1/2)/(64*((k : ℝ)+1)^6) := by
  have hsum : 0 < a+L := by linarith
  have hk6 : ((k : ℝ)+1)^6 ≤ D^6*(a+L)^6 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (by positivity : 0 ≤ (k : ℝ)+1) hk 6
  have hk12 : ((k : ℝ)+1)^12 ≤ D^12*(a+L)^12 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (by positivity : 0 ≤ (k : ℝ)+1) hk 12
  have hdom' : 1048576*((k : ℝ)+1)^6*H ≤ c*P := by
    have hd := mul_le_mul_of_nonneg_left hdom hc.le
    have heq : c*((1048576*D^6/c)*(a+L)^6*H) =
        1048576*(D^6*(a+L)^6)*H := by field_simp
    rw [heq] at hd
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hk6 (by norm_num)) hH).trans hd
  have hlarge' : 268435456*((L+1)*(D^12*(a+L)^12)) ≤ c*P := by
    have hh := (le_div_iff₀ (show 0 < (L+1)*(a+L)^12 by positivity)).mp hlarge
    have hh' := mul_le_mul_of_nonneg_left hh hc.le
    have heq : c*((268435456*D^12/c)*((L+1)*(a+L)^12)) =
        268435456*((L+1)*(D^12*(a+L)^12)) := by field_simp
    rwa [heq] at hh'
  have hden : 0 < 268435456*L*((k : ℝ)+1)^12 := by positivity
  have hone : 1 ≤ c*P/(268435456*L*((k : ℝ)+1)^12) := by
    apply (one_le_div hden).mpr
    apply le_trans _ hlarge'
    have hh := mul_le_mul (show L ≤ L+1 by linarith) hk12
      (by positivity : 0 ≤ ((k : ℝ)+1)^12) (by positivity : 0 ≤ L+1)
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh (show (0:ℝ) ≤ 268435456 by norm_num)
  exact hone.trans (shortest_cell_reserve_lower_bound hr hrL hL hc.le hP hdom')

/-- A single charge threshold proves the actual shortest-cell reserve in
all spins and at all larger energies, with no upper energy restriction. -/
theorem eventually_tail_shortest_cell_reserve_gt_half
    {t c D : ℝ} (ht : 0 < t) (hc : 0 < c) (hD : 0 < D) :
    ∀ᶠ a : ℝ in atTop, ∀ L : ℝ, t*a ≤ L → ∀ r : ℝ, 0 ≤ r → r ≤ L →
      ∀ k : ℕ, (k : ℝ)+1 ≤ D*(a+L) →
        1/2 <
          ((2*c*exp (8*sqrt (a*L))*sqrt L)*(cellCoordinateLength r L (L+1/2))^2/
              (8192*((k : ℝ)+1)^6)-2*exp (7*sqrt (a*(L+1)))/sqrt L)*
            cellCoordinateLength r L (L+1/2)/(64*((k : ℝ)+1)^6) := by
  filter_upwards [eventually_tail_exponential_dominates ht
      (show 0 < 1048576*D^6/c by positivity),
    eventually_tail_reserve_ge_uniform ht (268435456*D^12/c),
    eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (1/t)] with a hdom hlarge ha hat
  intro L hta r hr hrL k hk
  have hL : 1 ≤ L := by
    have hh := (div_le_iff₀ ht).mp hat
    nlinarith
  exact lt_of_lt_of_le (by norm_num) (shortest_cell_reserve_ge_one_of_growth
    ha hL hr hrL hc hD (exp_nonneg _) (exp_nonneg _) hk (hdom L hta) (hlarge L hta))

end GapFamily.Construction
