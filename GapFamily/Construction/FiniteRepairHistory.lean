import GapFamily.Construction.CanonicalRepairDatum
import GapFamily.Construction.MarkerReferenceThermalSummability

/-! Finite histories of literal canonical local repairs. The seed, ordinary
thermal output, and retained atoms are computed from the same concrete inputs. -/

noncomputable section
namespace GapFamily.Construction

open Set MeasureTheory UpperHalfPlane
open Analytic PoincareEnergyContinuation PoincareEnergyFourier PoincareFourier
open scoped MatrixGroups

/-- The finite sum of the actual modular correction seeds in a history. -/
def repairHistorySeed (history : List CanonicalRepairDatum) (τ : UpperHalfPlane) : ℂ :=
  (history.map (fun d => d.seed τ)).sum

/-- The finite sum of the ordinary thermal output measures of those same seeds. -/
def repairHistoryThermalOutput (history : List CanonicalRepairDatum) (j : ℤ) (t : ℝ) :
    SignedMeasure ℝ :=
  (history.map (fun d => d.thermalOutput j t)).sum

/-- Only active raw input rows enter a repair. This retains their actual signed
atoms, while the canonical inverse and anchor terms remain atomless. -/
def repairHistoryRawInput (history : List CanonicalRepairDatum) (j : ℤ) : SignedMeasure ℝ :=
  (history.map (fun d => if j ∈ lowBandSpinSet d.cutoffB then d.input j else 0)).sum

@[simp] theorem repairHistorySeed_nil (τ : UpperHalfPlane) : repairHistorySeed [] τ = 0 := rfl
@[simp] theorem repairHistoryThermalOutput_nil (j : ℤ) (t : ℝ) :
    repairHistoryThermalOutput [] j t = 0 := rfl
@[simp] theorem repairHistoryRawInput_nil (j : ℤ) : repairHistoryRawInput [] j = 0 := rfl

@[simp] theorem repairHistorySeed_cons (d : CanonicalRepairDatum)
    (history : List CanonicalRepairDatum) (τ : UpperHalfPlane) :
    repairHistorySeed (d :: history) τ = d.seed τ + repairHistorySeed history τ := rfl
@[simp] theorem repairHistoryThermalOutput_cons (d : CanonicalRepairDatum)
    (history : List CanonicalRepairDatum) (j : ℤ) (t : ℝ) :
    repairHistoryThermalOutput (d :: history) j t =
      d.thermalOutput j t + repairHistoryThermalOutput history j t := rfl
@[simp] theorem repairHistoryRawInput_cons (d : CanonicalRepairDatum)
    (history : List CanonicalRepairDatum) (j : ℤ) :
    repairHistoryRawInput (d :: history) j =
      (if j ∈ lowBandSpinSet d.cutoffB then d.input j else 0) +
        repairHistoryRawInput history j := rfl

theorem repairHistorySeed_append (H K : List CanonicalRepairDatum) (τ : UpperHalfPlane) :
    repairHistorySeed (H ++ K) τ = repairHistorySeed H τ + repairHistorySeed K τ := by
  simp only [repairHistorySeed, List.map_append, List.sum_append]

theorem repairHistoryThermalOutput_append (H K : List CanonicalRepairDatum) (j : ℤ) (t : ℝ) :
    repairHistoryThermalOutput (H ++ K) j t =
      repairHistoryThermalOutput H j t + repairHistoryThermalOutput K j t := by
  simp only [repairHistoryThermalOutput, List.map_append, List.sum_append]

theorem repairHistoryRawInput_append (H K : List CanonicalRepairDatum) (j : ℤ) :
    repairHistoryRawInput (H ++ K) j = repairHistoryRawInput H j + repairHistoryRawInput K j := by
  simp only [repairHistoryRawInput, List.map_append, List.sum_append]

theorem repairHistorySeed_smul (history : List CanonicalRepairDatum)
    (τ : UpperHalfPlane) (g : SL(2, ℤ)) :
    repairHistorySeed history (g • τ) = repairHistorySeed history τ := by
  unfold repairHistorySeed
  congr 1
  apply List.map_congr_left
  intro d _
  exact d.seed_smul τ g

/-- Every finite repair history has its full ordinary convergent Fourier output. -/
theorem hasSum_repairHistorySeed_output (history : List CanonicalRepairDatum)
    (y : ℝ) (hy : 0 < y) (x : ℝ) :
    HasSum (fun j : ℤ => (Real.sqrt y : ℂ) *
      (repairHistoryThermalOutput history j (2 * Real.pi * y) univ : ℂ) * cuspFourierMode j x)
      (repairHistorySeed history (rowPoint y hy x)) := by
  induction history with
  | nil => simpa using (hasSum_zero : HasSum (fun _ : ℤ => (0 : ℂ)) 0)
  | cons d H ih =>
    simpa only [repairHistoryThermalOutput_cons, _root_.add_apply, Complex.ofReal_add,
      mul_add, add_mul, repairHistorySeed_cons] using (d.hasSum_seed_output y hy x).add ih

/-- The repair history creates no atoms beyond its actual raw signed input atoms. -/
theorem repairHistoryThermalOutput_singleton (history : List CanonicalRepairDatum)
    (j : ℤ) {t : ℝ} (ht : 0 < t) (e : ℝ) :
    repairHistoryThermalOutput history j t {e} =
      Real.exp (-t * e) * repairHistoryRawInput history j {e} := by
  induction history with
  | nil => simp
  | cons d H ih =>
    rw [repairHistoryThermalOutput_cons, repairHistoryRawInput_cons,
      _root_.add_apply, _root_.add_apply, d.thermalOutput_singleton j ht e, ih]
    simp only [CanonicalRepairDatum.active]
    split_ifs <;> simp_all [mul_add]

/-- Every accumulated repair leaves the entire negative-energy vacuum measure fixed. -/
theorem repairHistoryThermalOutput_preserves_vacuum (history : List CanonicalRepairDatum)
    (V : SignedMeasure ℝ) (j : ℤ) {t : ℝ} (ht : 0 < t) :
    (V + repairHistoryThermalOutput history j t).restrict (Iio (0 : ℝ)) =
      V.restrict (Iio (0 : ℝ)) := by
  induction history generalizing V with
  | nil => simp
  | cons d H ih =>
    rw [repairHistoryThermalOutput_cons, ← add_assoc, ih]
    exact d.thermalOutput_preserves_vacuum V j ht

/-- Below every repair cutoff, the full output is exactly the finite raw input
thermal measure; no inverse response or threshold atom remains there. -/
theorem repairHistoryThermalOutput_restrict_below (history : List CanonicalRepairDatum)
    (B : ℝ) (hB : ∀ d ∈ history, B ≤ d.cutoffB) (j : ℤ) {t : ℝ} (ht : 0 < t) :
    (repairHistoryThermalOutput history j t).restrict (Iio B) =
      (history.map (fun d =>
        (if j ∈ lowBandSpinSet d.cutoffB then thermalSignedInputMeasure (d.input j) t else 0).restrict
          (Iio B))).sum := by
  induction history with
  | nil => simp
  | cons d H ih =>
    have hd : B ≤ d.cutoffB := hB d (by simp)
    have hH : ∀ e ∈ H, B ≤ e.cutoffB := fun e he => hB e (List.mem_cons_of_mem d he)
    rw [repairHistoryThermalOutput_cons, VectorMeasure.restrict_add, ih hH]
    simp only [List.map_cons, List.sum_cons]
    congr 1
    have he := congrArg (fun μ : SignedMeasure ℝ => μ.restrict (Iio B))
      (d.thermalOutput_restrict_below_cutoff j ht)
    simpa only [VectorMeasure.restrict_restrict _ measurableSet_Iio measurableSet_Iio,
      Iio_inter_Iio, min_eq_left hd, min_eq_right hd, CanonicalRepairDatum.active] using! he

/-- The actual complete finite-stage seed, including its prescribed vacuum. -/
def finiteRepairHistorySeed (a b : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b)
    (history : List CanonicalRepairDatum) (τ : UpperHalfPlane) : ℂ :=
  canonicalMarkerReferenceSeed a b ha hb τ + repairHistorySeed history τ

/-- Its actual nonvacuum ordinary thermal measure in each integer spin. -/
def finiteRepairHistoryThermalMeasure (a b : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b)
    (history : List CanonicalRepairDatum) (j : ℤ) (t : ℝ) : SignedMeasure ℝ :=
  canonicalMarkerReferenceThermalMeasure a b ha hb j t + repairHistoryThermalOutput history j t

theorem finiteRepairHistorySeed_smul (a b : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b)
    (history : List CanonicalRepairDatum) (τ : UpperHalfPlane) (g : SL(2, ℤ)) :
    finiteRepairHistorySeed a b ha hb history (g • τ) =
      finiteRepairHistorySeed a b ha hb history τ := by
  simp only [finiteRepairHistorySeed, canonicalMarkerReferenceSeed_smul, repairHistorySeed_smul]

theorem finiteRepairHistorySeed_append_singleton (a b : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b)
    (history : List CanonicalRepairDatum) (d : CanonicalRepairDatum) (τ : UpperHalfPlane) :
    finiteRepairHistorySeed a b ha hb (history ++ [d]) τ =
      finiteRepairHistorySeed a b ha hb history τ + d.seed τ := by
  simp only [finiteRepairHistorySeed, repairHistorySeed_append, repairHistorySeed_cons,
    repairHistorySeed_nil, add_zero, add_assoc]

theorem finiteRepairHistoryThermalMeasure_append_singleton
    (a b : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b)
    (history : List CanonicalRepairDatum) (d : CanonicalRepairDatum) (j : ℤ) (t : ℝ) :
    finiteRepairHistoryThermalMeasure a b ha hb (history ++ [d]) j t =
      finiteRepairHistoryThermalMeasure a b ha hb history j t + d.thermalOutput j t := by
  simp only [finiteRepairHistoryThermalMeasure, repairHistoryThermalOutput_append,
    repairHistoryThermalOutput_cons, repairHistoryThermalOutput_nil, add_zero, add_assoc]

/-- Exact permanent-atom bookkeeping for the same ordinary measure appearing
in the full Fourier reconstruction. -/
theorem finiteRepairHistoryThermalMeasure_singleton
    (a b : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b)
    (history : List CanonicalRepairDatum) (j : ℤ) {t : ℝ} (ht : 0 < t) (e : ℝ) :
    finiteRepairHistoryThermalMeasure a b ha hb history j t {e} =
      Real.exp (-t * e) *
        ((if j = 0 ∧ e = b then 1 else 0) + repairHistoryRawInput history j {e}) := by
  rw [finiteRepairHistoryThermalMeasure, _root_.add_apply,
    canonicalMarkerReferenceThermalMeasure_singleton a b ha hb j ht e,
    repairHistoryThermalOutput_singleton history j ht e]
  split_ifs <;> ring

/-- The original single vacuum contribution and the exact finite-stage thermal
measure reconstruct the same modular seed by an ordinary convergent series. -/
theorem hasSum_finiteRepairHistorySeed_output
    (a b : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b)
    (history : List CanonicalRepairDatum) (y : ℝ) (hy : 0 < y) (x : ℝ) :
    HasSum (fun j : ℤ => (Real.sqrt y : ℂ) *
      (finiteRepairHistoryThermalMeasure a b ha hb history j (2 * Real.pi * y) univ : ℂ) *
        cuspFourierMode j x)
      (finiteRepairHistorySeed a b ha hb history (rowPoint y hy x) - vacuumDirectRow a y x) := by
  convert (hasSum_canonicalMarkerReferenceSeed_thermalMeasure a b ha hb y hy x).add
    (hasSum_repairHistorySeed_output history y hy x) using 1
  · funext j
    simp only [finiteRepairHistoryThermalMeasure, _root_.add_apply, Complex.ofReal_add,
      mul_add, add_mul]
  · unfold finiteRepairHistorySeed
    ring

theorem finiteRepairHistorySeed_eq_full_output
    (a b : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b)
    (history : List CanonicalRepairDatum) (y : ℝ) (hy : 0 < y) (x : ℝ) :
    finiteRepairHistorySeed a b ha hb history (rowPoint y hy x) = vacuumDirectRow a y x +
      ∑' j : ℤ, (Real.sqrt y : ℂ) *
        (finiteRepairHistoryThermalMeasure a b ha hb history j (2 * Real.pi * y) univ : ℂ) *
          cuspFourierMode j x := by
  rw [(hasSum_finiteRepairHistorySeed_output a b ha hb history y hy x).tsum_eq]
  ring

end GapFamily.Construction
