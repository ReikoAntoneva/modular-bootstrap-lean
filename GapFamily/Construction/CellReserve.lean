import GapFamily.Construction.CellCoordinateResidual
import GapFamily.Construction.CellCoordinateVacuum
import GapFamily.Construction.CellReserveTerminal
import GapFamily.Construction.CellReserveUniform
import GapFamily.Construction.CellScheduleDegree

/-!
# Uniform tail cells on the frozen integer schedule

Both numerical inputs of the physical-cell residual theorem are derived here.
The genuine remaining inputs concern the actual current signed numerator and
its ordinary integrability and comparison with the actual leading vacuum.
-/

noncomputable section

open Set MeasureTheory Real Filter
open GapFamily.Analytic
open scoped BigOperators Topology

namespace GapFamily.Construction

/-- An actual tail cell, with its prescribed number of physical unit atoms and
its ordinary finite signed residual. This predicate contains only conclusions. -/
def HasTailCell (j : ℤ) (L : ℝ) (k : ℕ) (q : ℝ → ℝ) : Prop :=
  ∃ V ∈ Icc (L+1/2) (L+1), ∃ N : ℕ, 0 < N ∧ ∃ node : Fin N → ℝ,
    (∀ i, node i ∈ Icc L V) ∧
    (∫ E in Ioo L V, q E ∂referenceMeasure j) = (N : ℝ) ∧
    cellResidualMeasure j L V q node univ = 0 ∧
    (cellResidualMeasure j L V q node).variation (Icc L V)ᶜ = 0 ∧
    ∀ p : Polynomial ℝ, p.natDegree ≤ k →
      (cellResidualMeasure j L V q node).Integrable
        (fun E => p.eval (rootCoord |(j : ℝ)| E)) ∧
      (∫ᵛ E, p.eval (rootCoord |(j : ℝ)| E)
        ∂<•cellResidualMeasure j L V q node) = 0

/-- Uniform existence of actual tail cells for every allowed linear degree.
No terminal-window or polynomial-reserve inequality is an input. -/
theorem eventually_hasTailCell {t D : ℝ} (ht : 0 < t) (hD : 0 < D) :
    ∀ᶠ a : ℝ in atTop, ∀ L : ℝ, t*a ≤ L →
      ∀ j : ℤ, |(j : ℝ)| ≤ L → ∀ k : ℕ, (k : ℝ)+1 ≤ D*(a+L) →
      ∀ q : ℝ → ℝ, IntegrableOn q (Ioo L (L+1)) (referenceMeasure j) →
        (∀ E ∈ Icc L (L+1), |q E-vacuumLeading a E j| ≤ exp (7*sqrt (a*E))) →
        HasTailCell j L k q := by
  have hc : 0 < 2*π^4/625 := by positivity
  filter_upwards [eventually_tail_terminal_mass_gt_one hc ht,
    eventually_tail_shortest_cell_reserve_gt_half ht hc hD,
    eventually_ge_atTop (100 : ℝ), eventually_ge_atTop (1/t)] with a hterminal hreserve ha hat
  intro L hta j hj k hk q hq herror
  have hL : 0 < L := by
    have hh := (div_le_iff₀ ht).mp hat
    nlinarith
  exact exists_physical_cell_canceling_residual j hL hj (by linarith) (by linarith)
    hc.le (exp_nonneg _) (exp_nonneg _) q hq
    (cell_numerator_lower_bound_of_vacuum_error j ha hj q herror)
    (hterminal L hta |(j : ℝ)| (abs_nonneg _) hj)
    (hreserve L hta |(j : ℝ)| (abs_nonneg _) hj k hk)

/-- The literal natural charge and layer degree instantiate the uniform real
estimate at one threshold for every later integer layer and physical spin. -/
theorem eventually_scheduled_hasTailCell {R₀ M : ℕ} (K : ℕ)
    (hR₀ : 0 < R₀) (hM : 0 < M) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, R₀*n ≤ m →
      ∀ L : ℝ, (m : ℝ) ≤ L → ∀ j : ℤ, |(j : ℝ)| ≤ L →
      ∀ q : ℝ → ℝ, IntegrableOn q (Ioo L (L+1)) (referenceMeasure j) →
        (∀ E ∈ Icc L (L+1),
          |q E-vacuumLeading ((M*n : ℕ) : ℝ) E j| ≤
            exp (7*sqrt (((M*n : ℕ) : ℝ)*E))) →
        HasTailCell j L (tailMomentDegree K (M*n) m) q := by
  have hreal := eventually_hasTailCell (schedule_cutoff_ray_pos hR₀ hM)
    (show 0 < 2*((K : ℝ)+1) by positivity)
  have hsched := eventually_schedule_uniform_tail R₀ M hM hreal
  filter_upwards [hsched, eventually_scheduleCharge_ge M hM 1] with n hn ha
  intro m hm L hL j hj q hq herror
  exact hn m hm L hL j hj _
    (tailMomentDegree_add_one_le (by exact_mod_cast ha) hL) q hq herror

/-- The frozen schedule `M=R*s²`, `a=M*n`, `T=R₀*n`, `k_m=K(a+m+1)`
has actual prescribed unit-node cells for every sufficiently large `n`, every
executed slot `m≤L<m+1`, and every physical spin. The threshold is uniform in
all those unbounded indices. -/
theorem exists_threshold_scheduled_tail_cell
    {R₀ R K s : ℕ} (hR₀ : 0 < R₀) (hR : 0 < R) (hK : 0 < K) (hs : 0 < s) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ m : ℕ, R₀*n ≤ m →
      ∀ L : ℝ, (m : ℝ) ≤ L → L < (m : ℝ)+1 →
      ∀ j : ℤ, |(j : ℝ)| ≤ L →
      ∀ q : ℝ → ℝ, IntegrableOn q (Ioo L (L+1)) (referenceMeasure j) →
        (∀ E ∈ Icc L (L+1),
          |q E-vacuumLeading ((R*s^2*n : ℕ) : ℝ) E j| ≤
            exp (7*sqrt (((R*s^2*n : ℕ) : ℝ)*E))) →
        1 ≤ tailMomentDegree K (R*s^2*n) m ∧
          HasTailCell j L (tailMomentDegree K (R*s^2*n) m) q := by
  obtain ⟨n₀, hn₀⟩ := (eventually_atTop.1
    (eventually_scheduled_hasTailCell K hR₀ (schedule_multiplier_pos hR hs)))
  refine ⟨n₀, ?_⟩
  intro n hn m hm L hL _ j hj q hq herror
  constructor
  · change 1 ≤ K*((R*s^2*n)+m+1)
    exact Nat.succ_le_iff.mpr (Nat.mul_pos hK (by omega))
  · exact hn₀ n hn m hm L hL j hj q hq herror

end GapFamily.Construction
