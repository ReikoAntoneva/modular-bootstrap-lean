import GapFamily.Construction.ThermalEnvelope
import GapFamily.Construction.ThermalEnvelopeNode
import GapFamily.Construction.ThermalEnvelopeVariation

/-! Each actual tail cell is thermally dominated by its part of the fixed
all-spin envelope. Its atoms retain their unit weights, including endpoints,
and its signed residual is measured through ordinary positive total variation. -/

noncomputable section
open Set MeasureTheory Real Filter
open GapFamily.Analytic
open scoped BigOperators

namespace GapFamily.Construction

/-- The actual positive measure of the cell's prescribed unit nodes. -/
def TailCell.nodeMeasure {j : ℤ} {L : ℝ} {k : ℕ} {q : ℝ → ℝ}
    (cell : TailCell j L k q) : Measure ℝ :=
  ∑ i : Fin cell.count, Measure.dirac (cell.node i)

/-- Every real test is integrable against the finite positive node measure. -/
theorem TailCell.nodeMeasure_integrable {j : ℤ} {L : ℝ} {k : ℕ} {q : ℝ → ℝ}
    (cell : TailCell j L k q) (f : ℝ → ℝ) : Integrable f cell.nodeMeasure := by
  apply integrable_finsetSum_measure.mpr
  intro i hi
  exact integrable_dirac (by finiteness)

/-- Ordinary integration against the unit measure is the literal finite node sum. -/
theorem TailCell.integral_nodeMeasure {j : ℤ} {L : ℝ} {k : ℕ} {q : ℝ → ℝ}
    (cell : TailCell j L k q) (f : ℝ → ℝ) :
    (∫ E, f E ∂cell.nodeMeasure) = ∑ i, f (cell.node i) := by
  rw [TailCell.nodeMeasure, integral_finsetSum_measure]
  · simp only [integral_dirac]
  · intro i hi
    exact integrable_dirac (by finiteness)

/-- The C8 error invariant gives domination by the actual C10 numerator,
without replacing the signed current density by a positive one. -/
theorem TailCell.abs_le_tailEnvelope {a L : ℝ} {j : ℤ} {k : ℕ} {q : ℝ → ℝ}
    (cell : TailCell j L k q) (ha : 2 ≤ a) (hj : |(j : ℝ)| ≤ L)
    (herror : ∀ E ∈ Icc L (L + 1),
      |q E - vacuumLeading a E j| ≤ exp (7 * sqrt (a * E))) :
    ∀ E ∈ Ioo L cell.right, |q E| ≤ tailEnvelopeNumerator a E j := by
  intro E hE
  have hq := herror E ⟨hE.1.le, hE.2.le.trans cell.right_mem.2⟩
  have hpos := vacuumLeading_nonneg a E j ha (hj.trans hE.1.le)
  calc
    |q E| = |(q E - vacuumLeading a E j) + vacuumLeading a E j| := by congr 1; ring
    _ ≤ |q E - vacuumLeading a E j| + |vacuumLeading a E j| := abs_add_le _ _
    _ ≤ tailEnvelopeNumerator a E j := by
      rw [abs_of_nonneg hpos]
      dsimp [tailEnvelopeNumerator]
      linarith

/-- The exact thermal mass of all newly created unit nodes is bounded by
exp(t) times the fixed envelope mass on that same cell. -/
theorem TailCell.thermal_nodeMeasure_le_tailEnvelope
    {a T L : ℝ} {j : ℤ} {k : ℕ} {q : ℝ → ℝ}
    (cell : TailCell j L k q) (ha : 100 ≤ a) (hT : 1 ≤ T)
    (hTL : T ≤ L) (hj : |(j : ℝ)| ≤ L) {t : ℝ} (ht : 0 ≤ t)
    (herror : ∀ E ∈ Icc L (L + 1),
      |q E - vacuumLeading a E j| ≤ exp (7 * sqrt (a * E))) :
    (∫ E, exp (-t * E) ∂cell.nodeMeasure) ≤
      exp t * ∫ E in Ioo L cell.right, exp (-t * E) ∂tailEnvelopeMeasure a T j := by
  have ha2 : 2 ≤ a := by linarith
  have hL : 1 ≤ L := hT.trans hTL
  have hLV : L ≤ cell.right := by linarith [cell.right_mem.1]
  rw [cell.integral_nodeMeasure,
    integral_restrict_tailEnvelopeMeasure a T j ha2 hTL hj]
  exact cell.thermal_node_sum_le_of_envelope (by linarith) ht
    (integrableOn_tailEnvelopeNumerator a j hL hj hLV)
    (fun E hE => tailEnvelopeNumerator_nonneg a E j ha2 (hj.trans hE.1.le))
    (cell.abs_le_tailEnvelope ha2 hj herror)

/-- The actual weighted total variation of atoms minus current continuum has
exactly the C10 factor 1+exp(t), with an ordinary convergent pairing. -/
theorem TailCell.thermal_residual_le_tailEnvelope
    {a T L : ℝ} {j : ℤ} {k : ℕ} {q : ℝ → ℝ}
    (cell : TailCell j L k q) (ha : 100 ≤ a) (hT : 1 ≤ T)
    (hTL : T ≤ L) (hj : |(j : ℝ)| ≤ L) {t : ℝ} (ht : 0 ≤ t)
    (herror : ∀ E ∈ Icc L (L + 1),
      |q E - vacuumLeading a E j| ≤ exp (7 * sqrt (a * E))) :
    (∫ E, exp (-t * E) ∂cell.residual.variation) ≤
      (1 + exp t) * ∫ E in Ioo L cell.right, exp (-t * E) ∂tailEnvelopeMeasure a T j := by
  have ha2 : 2 ≤ a := by linarith
  have hL : 1 ≤ L := hT.trans hTL
  have hL0 : 0 ≤ L := by linarith
  have hLV : L ≤ cell.right := by linarith [cell.right_mem.1]
  have hnodes := cell.thermal_node_sum_le_of_envelope hL0 ht
    (integrableOn_tailEnvelopeNumerator a j hL hj hLV)
    (fun E hE => tailEnvelopeNumerator_nonneg a E j ha2 (hj.trans hE.1.le))
    (cell.abs_le_tailEnvelope ha2 hj herror)
  have hdensity := cell.thermal_density_le_of_envelope hL0 ht
    (integrableOn_tailEnvelopeNumerator a j hL hj hLV)
    (cell.abs_le_tailEnvelope ha2 hj herror)
  rw [integral_restrict_tailEnvelopeMeasure a T j ha2 hTL hj]
  exact (cell.thermal_variation_le hL0 ht).trans
    ((add_le_add hnodes hdensity).trans_eq (by ring))

/-- All three thermal objects in the local estimate are genuine ordinary
integrable pairings at every positive temperature. -/
theorem TailCell.thermal_envelope_pairing_integrable
    {a T L : ℝ} {j : ℤ} {k : ℕ} {q : ℝ → ℝ}
    (cell : TailCell j L k q) (ha : 100 ≤ a) (hT : 1 ≤ T)
    (hTL : T ≤ L) {t : ℝ} (ht : 0 < t) :
    Integrable (fun E => exp (-t * E)) cell.nodeMeasure ∧
      Integrable (fun E => exp (-t * E)) cell.residual.variation ∧
      IntegrableOn (fun E => exp (-t * E)) (Ioo L cell.right) (tailEnvelopeMeasure a T j) :=
  ⟨cell.nodeMeasure_integrable _, cell.thermal_residual_integrable (by linarith) ht.le,
    (integrable_thermal_tailEnvelopeMeasure a T j ha hT ht).integrableOn⟩

end GapFamily.Construction
