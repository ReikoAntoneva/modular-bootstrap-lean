import GapFamily.Construction.RealInitialState
import GapFamily.Construction.FiniteRepairStateOutput
import GapFamily.Construction.ReferenceOutput
import GapFamily.Construction.InitialDensityClipping

/-! The actual initial repair history has precisely the literal retained unit
nodes and the stored, pointwise cleared ordinary continuum as its output. -/

noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators

namespace GapFamily.Construction
open Analytic

variable (S : Finset ℤ) (b U : ℝ) (k : ℕ) (q : ℤ → ℝ → ℝ)
  (cells : ∀ J : S, InitialReferenceCell J (max b |(J : ℝ)|) U k
    (q J))
  (B0 : ℝ) (hB0 : 1 ≤ B0) (hcut : ∀ J, (cells J).right < B0)
  (hqthermal : ∀ (j : ℤ) (t : ℝ), 0 < t → Integrable (fun e => Real.exp (-t * e) * q j e)
    (referenceMeasure j))
  (hqzero : ∀ j : ℤ, ∀ᵐ e ∂referenceMeasure j, e < max b |(j : ℝ)| → q j e = 0)

include hcut in
/-- The finite sum of actual exterior responses has an ordinary thermal integral. -/
theorem realInitialRepairExterior_thermal_integrable (j : ℤ) {t : ℝ} (ht : 0 < t) :
    Integrable (fun e => Real.exp (-t * e) *
      realInitialRepairExterior S b U k q cells B0 hB0 j e) (referenceMeasure j) := by
  simpa only [realInitialRepairExterior, Finset.mul_sum, mul_ite, mul_zero] using
    integrable_finsetSum Finset.univ (fun J _ =>
      (cells J).integrable_exteriorNumerator_indicator_thermal B0 hB0
        (le_max_right b |(J : ℝ)|) (hcut J) j ht)

include hcut hqthermal in
/-- Clipping the reference and actual exterior sum preserves ordinary thermal integrability. -/
theorem realInitialRepairNumerator_thermal_integrable (j : ℤ) {t : ℝ} (ht : 0 < t) :
    Integrable (fun e => Real.exp (-t * e) *
      realInitialRepairNumerator S b U k q cells B0 hB0 j e) (referenceMeasure j) := by
  have hi := ((hqthermal j t ht).add
    (realInitialRepairExterior_thermal_integrable S b U k q cells B0 hB0 hcut j ht)).indicator
      (measurableSet_Ici (a := realInitialRepairFront S b U k q cells j))
  apply hi.congr
  filter_upwards [] with e
  by_cases he : e < realInitialRepairFront S b U k q cells j
  · simp [realInitialRepairNumerator, he, not_le.mpr he]
  · simp [realInitialRepairNumerator, he, le_of_not_gt he, mul_add]

include hqthermal in
theorem realInitialRepairState_thermalIntegrable :
    (realInitialRepairState S b U k q cells B0 hB0 hcut).ThermalIntegrable :=
  fun j _ ht => realInitialRepairNumerator_thermal_integrable S b U k q cells B0 hB0 hcut hqthermal j ht

include hcut in
private theorem realInitialRepairExterior_density_sum (j : ℤ) {t : ℝ} (ht : 0 < t) :
    (∑ J : S, (referenceMeasure j).withDensityᵥ (fun e => if B0 < e then
      Real.exp (-t * e) * (cells J).exteriorNumerator B0 hB0 j e else 0)) =
    (referenceMeasure j).withDensityᵥ (fun e => Real.exp (-t * e) *
      realInitialRepairExterior S b U k q cells B0 hB0 j e) := by
  ext s hs
  simp only [_root_.sum_apply]
  rw [withDensityᵥ_apply
    (realInitialRepairExterior_thermal_integrable S b U k q cells B0 hB0 hcut j ht) hs]
  rw [Finset.sum_congr rfl (fun J _ => withDensityᵥ_apply
    ((cells J).integrable_exteriorNumerator_indicator_thermal B0 hB0
      (le_max_right b |(J : ℝ)|) (hcut J) j ht) hs)]
  rw [← integral_finsetSum Finset.univ (fun J _ =>
    ((cells J).integrable_exteriorNumerator_indicator_thermal B0 hB0
      (le_max_right b |(J : ℝ)|) (hcut J) j ht).restrict)]
  apply integral_congr_ae
  filter_upwards [] with e
  simp only [realInitialRepairExterior, Finset.mul_sum, mul_ite, mul_zero]

private theorem realInitialRepairHistory_output_decomposition (j : ℤ) {t : ℝ} (ht : 0 < t) :
    repairHistoryThermalOutput
      (realInitialRepairHistory S b U k q cells B0 hB0 hcut) j t =
      (∑ J : S, if j = (J : ℤ) then thermalSignedInputMeasure (cells J).residual t else 0) +
      (referenceMeasure j).withDensityᵥ (fun e => Real.exp (-t * e) *
        realInitialRepairExterior S b U k q cells B0 hB0 j e) := by
  rw [repairHistoryThermalOutput_realInitialRepairHistory]
  simp_rw [(fun J : S => (cells J).repairOutput_eq_residual_add_exterior B0 hB0
    (le_max_right b |(J : ℝ)|) (hcut J) j ht)]
  rw [Finset.sum_add_distrib,
    realInitialRepairExterior_density_sum S b U k q cells B0 hB0 hcut j ht]

private theorem realInitialRepairResidual_sum_of_mem (j : ℤ) (hj : j ∈ S) (t : ℝ) :
    (∑ J : S, if j = (J : ℤ) then thermalSignedInputMeasure (cells J).residual t else 0) =
      thermalSignedInputMeasure (cells ⟨j, hj⟩).residual t := by
  rw [Finset.sum_eq_single (⟨j, hj⟩ : S)]
  · simp
  · intro J _ hJ
    exact ite_eq_right (fun he => hJ (Subtype.ext he.symm))
  · simp

private theorem realInitialRepairResidual_sum_of_notMem (j : ℤ) (hj : j ∉ S) (t : ℝ) :
    (∑ J : S, if j = (J : ℤ) then thermalSignedInputMeasure (cells J).residual t else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro J _
  split_ifs with he
  · exact (hj (he ▸ J.property)).elim
  · rfl

include hcut hqzero in
/-- On a repaired row the clipped representative is exactly the removed cell
density plus all actual exterior responses, up to ordinary null sets. -/
theorem realInitialRepairNumerator_ae_of_mem (j : ℤ) (hj : j ∈ S) :
    realInitialRepairNumerator S b U k q cells B0 hB0 j =ᵐ[referenceMeasure j]
      (fun e => removeCellDensity (max b |(j : ℝ)|) (cells ⟨j, hj⟩).right
        (q j) e +
        realInitialRepairExterior S b U k q cells B0 hB0 j e) := by
  change (fun e => if e < realInitialRepairFront S b U k q cells j then 0 else
    q j e +
      realInitialRepairExterior S b U k q cells B0 hB0 j e) =ᵐ[referenceMeasure j] _
  rw [realInitialRepairFront_of_mem S b U k q cells j hj]
  exact clippedDensity_ae_eq_removeCellDensity_add (referenceMeasure j)
      (max b |(j : ℝ)|) (cells ⟨j, hj⟩).right B0
      (q j)
      (realInitialRepairExterior S b U k q cells B0 hB0 j)
      (hqzero j)
      (fun e he => realInitialRepairExterior_eq_zero S b U k q cells B0 hB0 j e he.le)
      (hcut ⟨j, hj⟩).le

include hcut hqzero in
/-- On an unselected row clipping changes neither the reference nor any
actual exterior response in the physical reference measure. -/
theorem realInitialRepairNumerator_ae_of_notMem (j : ℤ) (hj : j ∉ S) :
    realInitialRepairNumerator S b U k q cells B0 hB0 j =ᵐ[referenceMeasure j]
      (fun e => q j e +
        realInitialRepairExterior S b U k q cells B0 hB0 j e) := by
  have hgap : ∀ᵐ e ∂referenceMeasure j, e < max b |(j : ℝ)| →
      realInitialRepairExterior S b U k q cells B0 hB0 j e = 0 := by
    filter_upwards [referenceMeasure_ae_above_edge j] with e hedge he
    have heb : e < b := (lt_max_iff.mp he).resolve_right (not_lt.mpr hedge.le)
    apply Finset.sum_eq_zero
    intro J _
    have hbB : b < B0 := ((le_max_left b |(J : ℝ)|).trans
      (cells J).left_le_right).trans_lt (hcut J)
    exact ite_eq_right (not_lt.mpr (heb.trans hbB).le)
  change (fun e => if e < realInitialRepairFront S b U k q cells j then 0 else
    q j e +
      realInitialRepairExterior S b U k q cells B0 hB0 j e) =ᵐ[referenceMeasure j] _
  rw [realInitialRepairFront_of_notMem S b U k q cells j hj]
  exact clippedDensity_ae_eq_add (referenceMeasure j) (max b |(j : ℝ)|)
      (q j)
      (realInitialRepairExterior S b U k q cells B0 hB0 j)
      (hqzero j) hgap

include hqthermal hqzero in
/-- The literal initial history has exactly its marker, chosen unit nodes,
and the ordinary continuum stored in the common finite-state representation. -/
theorem realInitialRepairState_hasReferenceOutput (a δ : ℝ) (ref : ReferenceOutput a)
    (href : ∀ j t, 0 < t → ref.thermalOutput j t = unitMarkerThermalMeasure δ j t +
      (referenceMeasure j).withDensityᵥ (fun e => Real.exp (-t * e) * q j e)) :
    (realInitialRepairState S b U k q cells B0 hB0 hcut).HasReferenceOutput ref δ := by
  intro j t ht
  have hq := hqthermal j t ht
  have hr := realInitialRepairExterior_thermal_integrable S b U k q cells B0 hB0 hcut j ht
  change ref.thermalOutput j t +
      repairHistoryThermalOutput (realInitialRepairHistory S b U k q cells B0 hB0 hcut) j t =
    (unitMarkerThermalMeasure δ j t +
      unitNodeRowThermalMeasure (realInitialRepairNodes S b U k q cells) j t) +
      (referenceMeasure j).withDensityᵥ (fun e => Real.exp (-t * e) *
        realInitialRepairNumerator S b U k q cells B0 hB0 j e)
  rw [href j t ht,
    realInitialRepairHistory_output_decomposition S b U k q cells B0 hB0 hcut j ht,
    unitNodeRowThermalMeasure_realInitialRepairNodes]
  change (unitMarkerThermalMeasure δ j t + _) + _ = _
  by_cases hj : j ∈ S
  · rw [dite_eq_left hj, realInitialRepairResidual_sum_of_mem S b U k q cells j hj t]
    have heq : (referenceMeasure j).withDensityᵥ (fun e => Real.exp (-t * e) *
        realInitialRepairNumerator S b U k q cells B0 hB0 j e) =
      (referenceMeasure j).withDensityᵥ (fun e => Real.exp (-t * e) *
        removeCellDensity (max b |(j : ℝ)|) (cells ⟨j, hj⟩).right
          (q j) e) +
      (referenceMeasure j).withDensityᵥ (fun e => Real.exp (-t * e) *
        realInitialRepairExterior S b U k q cells B0 hB0 j e) := by
      rw [← withDensityᵥ_add (integrable_thermal_removeCellDensity j _ _ t hq) hr]
      apply WithDensityᵥEq.congr_ae
      filter_upwards [realInitialRepairNumerator_ae_of_mem S b U k q cells B0 hB0 hcut hqzero j hj]
        with e he
      simp only [he, Pi.add_apply, mul_add]
    rw [heq]
    have hreplace := (cells ⟨j, hj⟩).thermal_replacement t hq
    rw [thermalSignedInputMeasure_unitAtomSignedMeasure] at hreplace
    calc
      _ = unitMarkerThermalMeasure δ j t +
          ((referenceMeasure j).withDensityᵥ (fun e => Real.exp (-t * e) *
            q j e) +
            thermalSignedInputMeasure (cells ⟨j, hj⟩).residual t) +
          (referenceMeasure j).withDensityᵥ (fun e => Real.exp (-t * e) *
            realInitialRepairExterior S b U k q cells B0 hB0 j e) := by abel
      _ = _ := by rw [hreplace]; abel
  · rw [dite_eq_right hj, realInitialRepairResidual_sum_of_notMem S b U k q cells j hj t,
      zero_add, add_zero]
    have heq : (referenceMeasure j).withDensityᵥ (fun e => Real.exp (-t * e) *
        realInitialRepairNumerator S b U k q cells B0 hB0 j e) =
      (referenceMeasure j).withDensityᵥ (fun e => Real.exp (-t * e) *
        q j e) +
      (referenceMeasure j).withDensityᵥ (fun e => Real.exp (-t * e) *
        realInitialRepairExterior S b U k q cells B0 hB0 j e) := by
      rw [← withDensityᵥ_add hq hr]
      apply WithDensityᵥEq.congr_ae
      filter_upwards [realInitialRepairNumerator_ae_of_notMem S b U k q cells B0 hB0 hcut hqzero j hj]
        with e he
      simp only [he, Pi.add_apply, mul_add]
    rw [heq, add_assoc]

end GapFamily.Construction
