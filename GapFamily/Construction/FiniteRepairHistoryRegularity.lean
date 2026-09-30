import GapFamily.Construction.FiniteRepairHistory
import GapFamily.Analytic.Poincare.Repair.PoincareLocalAnchorVariation

/-! Continuity and ordinary total-variation summability of the actual finite
repair histories and their complete reference-plus-repair stages. -/

noncomputable section
namespace GapFamily.Construction

open Set MeasureTheory UpperHalfPlane
open Analytic PoincareEnergyFourier

theorem continuous_repairHistorySeed (history : List CanonicalRepairDatum) :
    Continuous (repairHistorySeed history) :=
  continuous_list_sum history fun d _ => d.continuous_seed

theorem continuous_finiteRepairHistorySeed (a b : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b)
    (history : List CanonicalRepairDatum) :
    Continuous (finiteRepairHistorySeed a b ha hb history) :=
  (continuous_canonicalMarkerReferenceSeed a b ha hb).add
    (continuous_repairHistorySeed history)

private theorem variation_real_add_le (μ ν : SignedMeasure ℝ) :
    (μ + ν).variation.real univ ≤ μ.variation.real univ + ν.variation.real univ := by
  simpa using signedMeasure_variation_real_sub_le μ (-ν)

private theorem summable_list_sum_variation {ι : Type*} (μ : ι → ℤ → SignedMeasure ℝ)
    (L : List ι) (hμ : ∀ i ∈ L, Summable (fun j : ℤ => (μ i j).variation.real univ)) :
    Summable (fun j : ℤ => ((L.map (fun i => μ i j)).sum).variation.real univ) := by
  induction L with
  | nil => simp
  | cons i L ih =>
    have hi := hμ i (by simp)
    have hL := ih (fun k hk => hμ k (List.mem_cons_of_mem i hk))
    apply (hi.add hL).of_nonneg_of_le (fun _ => ENNReal.toReal_nonneg)
    intro j
    exact variation_real_add_le (μ i j) ((L.map (fun k => μ k j)).sum)

/-- Finite histories retain absolute thermal summability of the actual signed
measures over all integer spins. -/
theorem summable_repairHistoryThermalOutput_totalVariation
    (history : List CanonicalRepairDatum) {t : ℝ} (ht : 0 < t) :
    Summable (fun j : ℤ => (repairHistoryThermalOutput history j t).variation.real univ) :=
  summable_list_sum_variation (fun (d : CanonicalRepairDatum) j => d.thermalOutput j t) history
    (fun d _ => d.summable_thermalOutput_totalVariation ht)

/-- The complete finite-stage nonvacuum measure has summable ordinary thermal
variation, including both the canonical reference and every actual repair. -/
theorem summable_finiteRepairHistoryThermalMeasure_totalVariation
    (a b : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b) (history : List CanonicalRepairDatum)
    {t : ℝ} (ht : 0 < t) :
    Summable (fun j : ℤ =>
      (finiteRepairHistoryThermalMeasure a b ha hb history j t).variation.real univ) := by
  apply ((summable_canonicalMarkerReferenceThermalMeasure_totalVariation a b ha hb ht).add
    (summable_repairHistoryThermalOutput_totalVariation history ht)).of_nonneg_of_le
      (fun _ => ENNReal.toReal_nonneg)
  intro j
  exact variation_real_add_le (canonicalMarkerReferenceThermalMeasure a b ha hb j t)
    (repairHistoryThermalOutput history j t)

/-- Every repair history remains supported in the physical energy cone. -/
theorem repairHistoryThermalOutput_restrict_below_edge
    (history : List CanonicalRepairDatum) (j : ℤ) {t : ℝ} (ht : 0 < t) :
    (repairHistoryThermalOutput history j t).restrict (Iio |(j : ℝ)|) = 0 := by
  induction history with
  | nil => simp
  | cons d H ih =>
    rw [repairHistoryThermalOutput_cons, VectorMeasure.restrict_add, ih, add_zero]
    exact correctedThermalFiniteOutputMeasure_restrict_below_edge d.active d.repairInput
      j (3 * d.cutoffB) d.repairInput_physicalSupport ht

theorem finiteRepairHistoryThermalMeasure_restrict_below_edge
    (a b : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b) (history : List CanonicalRepairDatum)
    (j : ℤ) {t : ℝ} (ht : 0 < t) :
    (finiteRepairHistoryThermalMeasure a b ha hb history j t).restrict (Iio |(j : ℝ)|) = 0 := by
  rw [finiteRepairHistoryThermalMeasure, VectorMeasure.restrict_add,
    repairHistoryThermalOutput_restrict_below_edge history j ht, add_zero]
  exact markerReferenceThermalMeasure_restrict_below_edge (lowBandSpinSet b) a b ha
    (by linarith) (isUnit_correctedLowBandIdentityPlus_canonical b hb) j ht

/-- Physical support is a statement about the full ordinary variation measure. -/
theorem finiteRepairHistoryThermalMeasure_ae_physical
    (a b : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b) (history : List CanonicalRepairDatum)
    (j : ℤ) {t : ℝ} (ht : 0 < t) :
    ∀ᵐ E ∂(finiteRepairHistoryThermalMeasure a b ha hb history j t).variation,
      |(j : ℝ)| ≤ E := by
  have hr : (finiteRepairHistoryThermalMeasure a b ha hb history j t).variation.restrict
      (Iio |(j : ℝ)|) = 0 := by
    rw [← VectorMeasure.variation_restrict measurableSet_Iio,
      finiteRepairHistoryThermalMeasure_restrict_below_edge a b ha hb history j ht,
      VectorMeasure.variation_zero]
  exact (measure_eq_zero_iff_ae_notMem.mp (Measure.restrict_eq_zero.mp hr)).mono
    fun _ hE => le_of_not_gt hE

end GapFamily.Construction
