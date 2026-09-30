import GapFamily.Construction.ThermalEnvelopeCell
import GapFamily.Analytic.Foundation.DisjointRowIntegral

/-! Countable physical cells consume disjoint parts of the actual all-spin
thermal envelope. Both their literal unit nodes and their ordinary signed
residual variations are therefore thermally summable.
-/

noncomputable section

open Set MeasureTheory Real
open GapFamily.Analytic

namespace GapFamily.Construction

variable {ι : Type*} (J : ι → ℤ) (L : ι → ℝ) (k : ι → ℕ) (q : ι → ℝ → ℝ)
  (cell : ∀ i, TailCell (J i) (L i) (k i) (q i))
  (a T : ℝ) (ha : 100 ≤ a) (hT : 1 ≤ T)
  (hTL : ∀ i, T ≤ L i) (hJ : ∀ i, |(J i : ℝ)| ≤ L i)
  (hdis : Pairwise (fun i l => J i = J l →
    Disjoint (Ioo (L i) (cell i).right) (Ioo (L l) (cell l).right)))
  (herror : ∀ i E, E ∈ Icc (L i) (L i + 1) →
    |q i E - vacuumLeading a E (J i)| ≤ exp (7 * sqrt (a * E)))

include ha hT hdis

/-- The envelope portions assigned to disjoint physical cells have finite
total thermal mass, even across infinitely many different spin rows. -/
theorem summable_disjointTailCell_envelope {t : ℝ} (ht : 0 < t) :
    Summable (fun i => ∫ E in Ioo (L i) (cell i).right,
      exp (-t * E) ∂tailEnvelopeMeasure a T (J i)) := by
  exact summable_integral_disjoint_rows J
    (fun i => Ioo (L i) (cell i).right) (tailEnvelopeMeasure a T)
    (fun _ E => exp (-t * E)) (fun _ => measurableSet_Ioo) hdis
    (fun j => integrable_thermal_tailEnvelopeMeasure a T j ha hT ht)
    (fun _ => Filter.Eventually.of_forall fun _ => exp_nonneg _)
    (summable_integral_thermal_tailEnvelopeMeasure a T ha hT ht)

theorem tsum_disjointTailCell_envelope_le {t : ℝ} (ht : 0 < t) :
    (∑' i, ∫ E in Ioo (L i) (cell i).right,
      exp (-t * E) ∂tailEnvelopeMeasure a T (J i)) ≤
      ∑' j : ℤ, ∫ E, exp (-t * E) ∂tailEnvelopeMeasure a T j := by
  exact tsum_integral_disjoint_rows_le J
    (fun i => Ioo (L i) (cell i).right) (tailEnvelopeMeasure a T)
    (fun _ E => exp (-t * E)) (fun _ => measurableSet_Ioo) hdis
    (fun j => integrable_thermal_tailEnvelopeMeasure a T j ha hT ht)
    (fun _ => Filter.Eventually.of_forall fun _ => exp_nonneg _)
    (summable_integral_thermal_tailEnvelopeMeasure a T ha hT ht)

include hTL hJ herror

/-- All newly emitted unit nodes are thermally summable, retaining repeated
nodes and closed-cell endpoints as distinct occurrences. -/
theorem summable_disjointTailCell_nodeMass {t : ℝ} (ht : 0 < t) :
    Summable (fun i => ∫ E, exp (-t * E) ∂(cell i).nodeMeasure) := by
  apply ((summable_disjointTailCell_envelope J L k q cell a T ha hT hdis ht).mul_left
    (exp t)).of_nonneg_of_le
  · intro i
    exact integral_nonneg (fun _ => exp_nonneg _)
  · intro i
    exact (cell i).thermal_nodeMeasure_le_tailEnvelope ha hT (hTL i) (hJ i) ht.le
      (herror i)

/-- The ordinary thermal total variation of every actual signed residual is
summable over the complete cell family. -/
theorem summable_disjointTailCell_residual {t : ℝ} (ht : 0 < t) :
    Summable (fun i => ∫ E, exp (-t * E) ∂(cell i).residual.variation) := by
  apply ((summable_disjointTailCell_envelope J L k q cell a T ha hT hdis ht).mul_left
    (1 + exp t)).of_nonneg_of_le
  · intro i
    exact integral_nonneg (fun _ => exp_nonneg _)
  · intro i
    exact (cell i).thermal_residual_le_tailEnvelope ha hT (hTL i) (hJ i) ht.le
      (herror i)

/-- The total mass of all actual unit nodes obeys the fixed envelope bound. -/
theorem tsum_disjointTailCell_nodeMass_le {t : ℝ} (ht : 0 < t) :
    (∑' i, ∫ E, exp (-t * E) ∂(cell i).nodeMeasure) ≤
      exp t * ∑' j : ℤ, ∫ E, exp (-t * E) ∂tailEnvelopeMeasure a T j := by
  calc
    _ ≤ ∑' i, exp t * ∫ E in Ioo (L i) (cell i).right,
        exp (-t * E) ∂tailEnvelopeMeasure a T (J i) :=
      Summable.tsum_le_tsum
        (fun i => (cell i).thermal_nodeMeasure_le_tailEnvelope ha hT (hTL i) (hJ i)
          ht.le (herror i))
        (summable_disjointTailCell_nodeMass J L k q cell a T ha hT hTL hJ hdis herror ht)
        ((summable_disjointTailCell_envelope J L k q cell a T ha hT hdis ht).mul_left _)
    _ = exp t * ∑' i, ∫ E in Ioo (L i) (cell i).right,
        exp (-t * E) ∂tailEnvelopeMeasure a T (J i) := by rw [tsum_mul_left]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (tsum_disjointTailCell_envelope_le J L k q cell a T ha hT hdis ht) (exp_nonneg _)

theorem tsum_disjointTailCell_residual_le {t : ℝ} (ht : 0 < t) :
    (∑' i, ∫ E, exp (-t * E) ∂(cell i).residual.variation) ≤
      (1 + exp t) * ∑' j : ℤ, ∫ E, exp (-t * E) ∂tailEnvelopeMeasure a T j := by
  calc
    _ ≤ ∑' i, (1 + exp t) * ∫ E in Ioo (L i) (cell i).right,
        exp (-t * E) ∂tailEnvelopeMeasure a T (J i) :=
      Summable.tsum_le_tsum
        (fun i => (cell i).thermal_residual_le_tailEnvelope ha hT (hTL i) (hJ i)
          ht.le (herror i))
        (summable_disjointTailCell_residual J L k q cell a T ha hT hTL hJ hdis herror ht)
        ((summable_disjointTailCell_envelope J L k q cell a T ha hT hdis ht).mul_left _)
    _ = (1 + exp t) * ∑' i, ∫ E in Ioo (L i) (cell i).right,
        exp (-t * E) ∂tailEnvelopeMeasure a T (J i) := by rw [tsum_mul_left]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (tsum_disjointTailCell_envelope_le J L k q cell a T ha hT hdis ht) (by positivity)

/-- The complete sigma-indexed family of literal unit nodes has a convergent
thermal series; no injectivity of node locations is required. -/
theorem summable_disjointTailCell_nodes {t : ℝ} (ht : 0 < t) :
    Summable (fun p : Σ i, Fin (cell i).count => exp (-t * (cell p.1).node p.2)) := by
  apply (summable_sigma_of_nonneg (fun _ => exp_nonneg _)).mpr
  constructor
  · intro i
    exact (hasSum_fintype _).summable
  · have h := summable_disjointTailCell_nodeMass J L k q cell a T ha hT hTL hJ hdis herror ht
    simp_rw [TailCell.integral_nodeMeasure] at h
    simpa only [tsum_fintype] using h

end GapFamily.Construction
