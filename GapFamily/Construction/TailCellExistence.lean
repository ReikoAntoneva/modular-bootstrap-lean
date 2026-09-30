import GapFamily.Construction.TailCellBound
import GapFamily.Construction.TailCellReference
import GapFamily.Construction.TailCellVariation
import GapFamily.Analytic.Foundation.FullVacuumIntegrability

/-! Actual tail-cell data with integer mass, exactly that many unit nodes,
vanishing moments, and the uniform ordinary total-variation budget needed by
local repair. All numerical reserve conditions have already been proved in
`CellReserve`; no additional good-parameter existence assumption is introduced. -/

noncomputable section
open Set MeasureTheory Real Filter
open GapFamily.Analytic
open scoped Topology

namespace GapFamily.Construction

/-- The ordinary finite signed cell supplied to a tail repair step. Unit
weights are encoded by the literal node type `Fin count`, including multiplicity. -/
structure TailCell (j : ℤ) (L : ℝ) (k : ℕ) (q : ℝ → ℝ) where
  right : ℝ
  right_mem : right ∈ Icc (L + 1 / 2) (L + 1)
  count : ℕ
  count_pos : 0 < count
  node : Fin count → ℝ
  node_mem : ∀ i, node i ∈ Icc L right
  density_integrable : IntegrableOn q (Ioo L right) (referenceMeasure j)
  mass_eq : (∫ E in Ioo L right, q E ∂referenceMeasure j) = (count : ℝ)
  residual_mass : cellResidualMeasure j L right q node univ = 0
  residual_support : (cellResidualMeasure j L right q node).variation (Icc L right)ᶜ = 0
  moment : ∀ p : Polynomial ℝ, p.natDegree ≤ k →
    (cellResidualMeasure j L right q node).Integrable
      (fun E => p.eval (rootCoord |(j : ℝ)| E)) ∧
    (∫ᵛ E, p.eval (rootCoord |(j : ℝ)| E)
      ∂<•cellResidualMeasure j L right q node) = 0

/-- The actual atoms-minus-continuum residual, retaining its signed measure type. -/
def TailCell.residual {j : ℤ} {L : ℝ} {k : ℕ} {q : ℝ → ℝ}
    (cell : TailCell j L k q) : SignedMeasure ℝ :=
  cellResidualMeasure j L cell.right q cell.node

/-- The already proved C8 endpoint theorem supplies all fields of the actual cell. -/
theorem nonempty_tailCell_of_hasTailCell {j : ℤ} {L : ℝ} {k : ℕ} {q : ℝ → ℝ}
    (hq : IntegrableOn q (Ioo L (L + 1)) (referenceMeasure j))
    (hcell : HasTailCell j L k q) : Nonempty (TailCell j L k q) := by
  obtain ⟨V, hV, N, hN, node, hnode, hmass, hzero, hsupport, hmoment⟩ := hcell
  exact ⟨{
    right := V
    right_mem := hV
    count := N
    count_pos := hN
    node := node
    node_mem := hnode
    density_integrable := hq.mono_set (Ioo_subset_Ioo le_rfl hV.2)
    mass_eq := hmass
    residual_mass := hzero
    residual_support := hsupport
    moment := hmoment }⟩

/-- The ordinary absolute continuum mass on the chosen cell is uniformly bounded. -/
theorem TailCell.abs_mass_le {a L : ℝ} {j : ℤ} {k : ℕ} {q : ℝ → ℝ}
    (cell : TailCell j L k q) (ha : 100 ≤ a) (hL : 1 ≤ L)
    (hj : |(j : ℝ)| ≤ L)
    (herror : ∀ E ∈ Icc L (L + 1),
      |q E - vacuumLeading a E j| ≤ exp (7 * sqrt (a * E))) :
    (∫ E in Ioo L cell.right, |q E| ∂referenceMeasure j) ≤
      6 * exp (4 * π * (a + L)) := by
  have hLV : L ≤ cell.right := by linarith [cell.right_mem.1]
  have hmass := tailCell_integral_abs_le j hL hj hLV cell.right_mem.2
    (show 0 ≤ 3 * exp (4 * π * (a + L)) by positivity) cell.density_integrable
    (fun E hE => tailCell_abs_numerator_le ha hL j hj q herror E
      ⟨hE.1.le, hE.2.le.trans cell.right_mem.2⟩)
  linarith

/-- The exact number of unit nodes has the same exponential mass budget. -/
theorem TailCell.count_le {a L : ℝ} {j : ℤ} {k : ℕ} {q : ℝ → ℝ}
    (cell : TailCell j L k q) (ha : 100 ≤ a) (hL : 1 ≤ L)
    (hj : |(j : ℝ)| ≤ L)
    (herror : ∀ E ∈ Icc L (L + 1),
      |q E - vacuumLeading a E j| ≤ exp (7 * sqrt (a * E))) :
    (cell.count : ℝ) ≤ 6 * exp (4 * π * (a + L)) := by
  have h : (cell.count : ℝ) ≤ ∫ E in Ioo L cell.right, |q E| ∂referenceMeasure j := by
    simpa only [cell.mass_eq, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) cell.count)] using
      norm_integral_le_integral_norm (μ := (referenceMeasure j).restrict (Ioo L cell.right)) q
  exact h.trans (cell.abs_mass_le ha hL hj herror)

/-- The actual cell residual obeys the uniform exponential TV bound, with
no assumption that the current continuum density is pointwise positive. -/
theorem TailCell.variation_le {a L : ℝ} {j : ℤ} {k : ℕ} {q : ℝ → ℝ}
    (cell : TailCell j L k q) (ha : 100 ≤ a) (hL : 1 ≤ L)
    (hj : |(j : ℝ)| ≤ L)
    (herror : ∀ E ∈ Icc L (L + 1),
      |q E - vacuumLeading a E j| ≤ exp (7 * sqrt (a * E))) :
    cell.residual.variation.real univ ≤ 12 * exp (4 * π * (a + L)) := by
  have hmass := cell.abs_mass_le ha hL hj herror
  have hvar := cellResidualMeasure_variation_le_twice_abs_mass j L cell.right cell.node
    cell.density_integrable cell.mass_eq
  change (cellResidualMeasure j L cell.right q cell.node).variation.real univ ≤ _
  linarith

/-- The logarithmic cost of the actual ordinary signed residual is linear
in the actual unbounded cell location and charge. -/
theorem TailCell.log_variation_le {a L : ℝ} {j : ℤ} {k : ℕ} {q : ℝ → ℝ}
    (cell : TailCell j L k q) (ha : 100 ≤ a) (hL : 1 ≤ L)
    (hj : |(j : ℝ)| ≤ L)
    (herror : ∀ E ∈ Icc L (L + 1),
      |q E - vacuumLeading a E j| ≤ exp (7 * sqrt (a * E))) :
    log (2 + cell.residual.variation.real univ) ≤ (4 * π + 14) * (a + L) :=
  tailCell_log_variation_le (by linarith) hL (measureReal_nonneg)
    (cell.variation_le ha hL hj herror)

/-- One charge threshold supplies all physical tail cells and their repair
budgets above a fixed positive ray, uniformly in unbounded layer and spin. -/
theorem eventually_exists_tailCell {t D : ℝ} (ht : 0 < t) (hD : 0 < D) :
    ∀ᶠ a : ℝ in atTop, ∀ L : ℝ, t * a ≤ L →
      ∀ j : ℤ, |(j : ℝ)| ≤ L → ∀ k : ℕ, (k : ℝ) + 1 ≤ D * (a + L) →
      ∀ q : ℝ → ℝ, IntegrableOn q (Ioo L (L + 1)) (referenceMeasure j) →
      (∀ E ∈ Icc L (L + 1),
        |q E - vacuumLeading a E j| ≤ exp (7 * sqrt (a * E))) →
      ∃ cell : TailCell j L k q,
        cell.residual.variation.real univ ≤ 12 * exp (4 * π * (a + L)) ∧
        log (2 + cell.residual.variation.real univ) ≤ (4 * π + 14) * (a + L) := by
  filter_upwards [eventually_hasTailCell ht hD, eventually_ge_atTop (100 : ℝ),
    eventually_ge_atTop (1 / t)] with a hcell ha hat
  intro L hta j hj k hk q hq herror
  have hL : 1 ≤ L := by
    have hh := (div_le_iff₀ ht).mp hat
    nlinarith
  obtain ⟨cell⟩ := nonempty_tailCell_of_hasTailCell hq (hcell L hta j hj k hk q hq herror)
  exact ⟨cell, cell.variation_le ha hL hj herror, cell.log_variation_le ha hL hj herror⟩

/-- The C8 invariant can be stated relative to the actual full vacuum,
using its proved quarter-error estimate rather than a vacuum remainder oracle. -/
theorem eventually_exists_tailCell_of_vacuumPerturbation {t D : ℝ}
    (ht : 0 < t) (hD : 0 < D) :
    ∀ᶠ a : ℝ in atTop, ∀ L : ℝ, t * a ≤ L →
      ∀ j : ℤ, |(j : ℝ)| ≤ L → ∀ k : ℕ, (k : ℝ) + 1 ≤ D * (a + L) →
      ∀ q : ℝ → ℝ, IntegrableOn q (Ioo L (L + 1)) (referenceMeasure j) →
      (∀ E ∈ Icc L (L + 1),
        |q E - vacuumNumerator a E j| ≤ (3 / 4 : ℝ) * exp (7 * sqrt (a * E))) →
      ∃ cell : TailCell j L k q,
        cell.residual.variation.real univ ≤ 12 * exp (4 * π * (a + L)) ∧
        log (2 + cell.residual.variation.real univ) ≤ (4 * π + 14) * (a + L) := by
  obtain ⟨A, _, hA⟩ := exists_vacuumPerturbation_tail_error_threshold
  filter_upwards [eventually_exists_tailCell ht hD, eventually_ge_atTop A,
    eventually_ge_atTop (1 / t)] with a hcell ha hat
  intro L hta j hj k hk q hq herror
  have hL : 1 ≤ L := by
    have hh := (div_le_iff₀ ht).mp hat
    nlinarith
  exact hcell L hta j hj k hk q hq (hA a L j ha hL hj q herror)

/-- In particular, the actual canonical full vacuum itself has genuine tail
unit-node cells. Its ordinary integrability is proved, not an input. -/
theorem eventually_exists_vacuum_tailCell {t D : ℝ} (ht : 0 < t) (hD : 0 < D) :
    ∀ᶠ a : ℝ in atTop, ∀ L : ℝ, t * a ≤ L →
      ∀ j : ℤ, |(j : ℝ)| ≤ L → ∀ k : ℕ, (k : ℝ) + 1 ≤ D * (a + L) →
      ∃ cell : TailCell j L k (fun E => vacuumNumerator a E j),
        cell.residual.variation.real univ ≤ 12 * exp (4 * π * (a + L)) ∧
        log (2 + cell.residual.variation.real univ) ≤ (4 * π + 14) * (a + L) := by
  filter_upwards [eventually_exists_tailCell_of_vacuumPerturbation ht hD,
    eventually_ge_atTop (2 : ℝ)] with a hcell ha
  intro L hta j hj k hk
  apply hcell L hta j hj k hk (fun E => vacuumNumerator a E j)
  · have hi : IntegrableOn (fun E => vacuumNumerator a E j)
        (Ioo |(j : ℝ)| (L + 1)) (referenceMeasure j) :=
      (vacuumFullKernel_lowBand_integrable a (L + 1) j ha).re
    exact hi.mono_set (Ioo_subset_Ioo hj le_rfl)
  · intro E hE
    simp only [sub_self, abs_zero]
    positivity

/-- The frozen integer schedule produces a single natural threshold for all
later layers, including the prescribed degree and the residual repair budget. -/
theorem exists_threshold_scheduled_tailCell {R₀ R K s : ℕ}
    (hR₀ : 0 < R₀) (hR : 0 < R) (hK : 0 < K) (hs : 0 < s) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ m : ℕ, R₀ * n ≤ m →
      ∀ L : ℝ, (m : ℝ) ≤ L → L < (m : ℝ) + 1 →
      ∀ j : ℤ, |(j : ℝ)| ≤ L →
      ∀ q : ℝ → ℝ, IntegrableOn q (Ioo L (L + 1)) (referenceMeasure j) →
      (∀ E ∈ Icc L (L + 1),
        |q E - vacuumLeading ((R * s ^ 2 * n : ℕ) : ℝ) E j| ≤
          exp (7 * sqrt (((R * s ^ 2 * n : ℕ) : ℝ) * E))) →
      1 ≤ tailMomentDegree K (R * s ^ 2 * n) m ∧
      ∃ cell : TailCell j L (tailMomentDegree K (R * s ^ 2 * n) m) q,
        cell.residual.variation.real univ ≤
          12 * exp (4 * π * (((R * s ^ 2 * n : ℕ) : ℝ) + L)) ∧
        log (2 + cell.residual.variation.real univ) ≤
          (4 * π + 14) * (((R * s ^ 2 * n : ℕ) : ℝ) + L) := by
  have hM := schedule_multiplier_pos hR hs
  have hreal := eventually_exists_tailCell (schedule_cutoff_ray_pos hR₀ hM)
    (show 0 < 2 * ((K : ℝ) + 1) by positivity)
  have hsched := eventually_schedule_uniform_tail R₀ (R * s ^ 2) hM hreal
  have hcharge := eventually_scheduleCharge_ge (R * s ^ 2) hM 1
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp (hsched.and hcharge)
  refine ⟨n₀, ?_⟩
  intro n hn m hm L hL _ j hj q hq herror
  obtain ⟨hcell, ha⟩ := hn₀ n hn
  refine ⟨Nat.succ_le_iff.mpr (Nat.mul_pos hK (by omega)), ?_⟩
  exact hcell m hm L hL j hj _
    (tailMomentDegree_add_one_le (by exact_mod_cast ha) hL) q hq herror

end GapFamily.Construction
