import BTZEntropy.Contract
import BTZEntropy.Construction.FixedFamilySupport
import GapFamily.Construction.RealInitialConstructionEndpoint

/-!
# Actual data for a fixed clearing cutoff

The geometry is fixed before the real charge parameter and marker. A datum retains
the actual initial cells, their signed density, the modular reference, and
the selector used at every subsequent tail slot. The public spectrum is
defined from those same permanent unit nodes.
-/

noncomputable section

open Set Filter MeasureTheory Real
open scoped BigOperators

namespace BTZEntropy.Construction

open GapFamily GapFamily.Construction GapFamily.Analytic

/-- Common finite geometry for every charge and marker in a fixed family.
The clearing cutoff may be enlarged beyond the requested cutoff `B`. -/
structure FixedFamilyGeometry (B : ℝ) where
  clearing : ℝ
  radius : ℝ
  upper : ℝ
  start : ℕ
  cutoff_le : B ≤ clearing
  cutoff_lt_start : B < (start : ℝ)
  start_pos : 1 ≤ start
  radius_nonneg : 0 ≤ radius
  start_le_radius : (start : ℝ) ≤ radius
  radius_le_upper : radius ≤ upper

namespace FixedFamilyGeometry

variable {B : ℝ} (g : FixedFamilyGeometry B)

theorem upper_nonneg : 0 ≤ g.upper := g.radius_nonneg.trans g.radius_le_upper

def repairCutoff : ℝ := 2 * g.upper + 4

theorem repairCutoff_one : 1 ≤ g.repairCutoff := by
  have := g.upper_nonneg
  dsimp [repairCutoff]
  linarith

end FixedFamilyGeometry

/-- Finite cells and a local tail selector, with exactly the analytic
premises needed to construct the spectrum. No spectral existence or
infinite convergence conclusion is stored as a field. -/
structure FixedFamilyDatum {B : ℝ} (g : FixedFamilyGeometry B) (a : ℝ) (δ : ℝ) where
  marker_nonneg : 0 ≤ δ
  marker_lt : δ < B
  charge_large : 100 ≤ shift (gapFamilyCharge a)
  initialDegree : ℕ
  tailDegree : ℕ → ℕ
  density : ℤ → ℝ → ℝ
  reference : ReferenceOutput (shift (gapFamilyCharge a))
  initialCell : ∀ J : realInitialRows g.radius,
    InitialReferenceCell J (max g.clearing |(J : ℝ)|) g.upper initialDegree (density J)
  tail : RealTailLocalData (shift (gapFamilyCharge a)) g.upper g.start tailDegree
  density_thermal : ∀ (j : ℤ) (t : ℝ), 0 < t →
    Integrable (fun E => exp (-t * E) * density j E) (referenceMeasure j)
  density_zero : ∀ j : ℤ, ∀ᵐ E ∂referenceMeasure j,
    E < max g.clearing |(j : ℝ)| → density j E = 0
  reference_output : ∀ (j : ℤ) (t : ℝ), 0 < t →
    reference.thermalOutput j t = unitMarkerThermalMeasure δ j t +
      (referenceMeasure j).withDensityᵥ (fun E => exp (-t * E) * density j E)
  reference_error : ∀ (j : ℤ) (E : ℝ), max g.radius |(j : ℝ)| ≤ E →
    |density j E - vacuumLeading (shift (gapFamilyCharge a)) E j| ≤
      exp (7 * sqrt (shift (gapFamilyCharge a) * E)) / 2
  initial_error : ∀ (j : ℤ) (E : ℝ), |(j : ℝ)| ≤ E →
    (∑ J, |if g.repairCutoff < E then
      (initialCell J).exteriorNumerator g.repairCutoff g.repairCutoff_one j E else 0|) ≤
      exp (7 * sqrt (shift (gapFamilyCharge a) * E)) / 8

namespace FixedFamilyDatum

variable {B : ℝ} {g : FixedFamilyGeometry B} {a : ℝ} {δ : ℝ}
  (d : FixedFamilyDatum g a δ)

include d in
theorem marker_le_clearing : δ ≤ g.clearing := d.marker_lt.le.trans g.cutoff_le

include d in
theorem marker_lt_start : δ < (g.start : ℝ) := d.marker_lt.trans g.cutoff_lt_start

theorem initialCell_right_lt_cutoff (J : realInitialRows g.radius) :
    (d.initialCell J).right < g.repairCutoff :=
  realInitialRepairCell_right_lt_band (realInitialRows g.radius) g.clearing g.upper
    d.initialDegree d.density d.initialCell g.upper_nonneg J

/-- The literal initial repair state, retaining every selected initial node
and the complete finite history of the same cell repairs. -/
def initialState : FiniteRepairState :=
  realInitialRepairState (realInitialRows g.radius) g.clearing g.upper
    d.initialDegree d.density d.initialCell g.repairCutoff g.repairCutoff_one
    d.initialCell_right_lt_cutoff

theorem initial_nodes_cutoff (p : ℝ × ℤ) (hp : p ∈ d.initialState.nodes) : B < p.1 :=
  realInitialRepairState_node_strict (realInitialRows g.radius) g.clearing g.upper
    d.initialDegree d.density d.initialCell g.repairCutoff g.repairCutoff_one
    d.initialCell_right_lt_cutoff g.cutoff_le p hp

theorem initial_nodes_bounds (p : ℝ × ℤ) (hp : p ∈ d.initialState.nodes) :
    δ ≤ p.1 ∧ |(p.2 : ℝ)| ≤ p.1 := by
  have h := realInitialRepairState_node_spectrum_bounds (realInitialRows g.radius)
    g.clearing g.upper d.initialDegree d.density d.initialCell g.repairCutoff
    g.repairCutoff_one d.initialCell_right_lt_cutoff d.marker_le_clearing p hp
  exact ⟨h.1.le, h.2⟩

theorem initial_hasReferenceOutput : d.initialState.HasReferenceOutput d.reference δ :=
  realInitialRepairState_hasReferenceOutput (realInitialRows g.radius) g.clearing
    g.upper d.initialDegree d.density d.initialCell g.repairCutoff g.repairCutoff_one
    d.initialCell_right_lt_cutoff d.density_thermal d.density_zero
    (shift (gapFamilyCharge a)) δ d.reference d.reference_output

theorem initial_thermalIntegrable : d.initialState.ThermalIntegrable :=
  realInitialRepairState_thermalIntegrable (realInitialRows g.radius) g.clearing
    g.upper d.initialDegree d.density d.initialCell g.repairCutoff g.repairCutoff_one
    d.initialCell_right_lt_cutoff d.density_thermal

theorem initial_cleared : d.initialState.Cleared :=
  realInitialRepairState_cleared (realInitialRows g.radius) g.clearing g.upper
    d.initialDegree d.density d.initialCell g.repairCutoff g.repairCutoff_one
    d.initialCell_right_lt_cutoff

theorem initial_front : FrontInvariant g.start FiniteRepairState.front d.initialState := by
  intro j
  exact (max_le_max g.start_le_radius le_rfl).trans
    (max_le_realInitialRepairFront_of_cover (realInitialRows g.radius) g.clearing
      g.upper d.initialDegree d.density d.initialCell g.radius g.radius_le_upper
      (fun j hj => (mem_realInitialRows g.radius_nonneg j).mpr hj) j)

theorem initial_front_upper (j : ℤ) :
    d.initialState.front j ≤ max (g.upper + 1) (max ((g.start : ℝ) + 1) |(j : ℝ)|) :=
  realInitialRepairState_front_le_layer_start (realInitialRows g.radius) g.clearing
    g.upper d.initialDegree d.density d.initialCell g.repairCutoff g.repairCutoff_one
    d.initialCell_right_lt_cutoff
    ⟨0, (mem_realInitialRows g.radius_nonneg 0).mpr (by simpa using g.radius_nonneg)⟩
    g.start j

theorem initial_error_bound (j : ℤ) (E : ℝ) (hE : d.initialState.front j ≤ E) :
    |d.initialState.numerator j E - vacuumLeading (shift (gapFamilyCharge a)) E j| ≤
      (5 / 8 : ℝ) * exp (7 * sqrt (shift (gapFamilyCharge a) * E)) := by
  have h := realInitialRepairState_error_le_five_eighths (realInitialRows g.radius)
    g.clearing g.upper d.initialDegree d.density d.initialCell g.repairCutoff
    g.repairCutoff_one d.initialCell_right_lt_cutoff (shift (gapFamilyCharge a))
    g.radius g.radius_le_upper
    (fun j hj => (mem_realInitialRows g.radius_nonneg j).mpr hj)
    d.reference_error d.initial_error j E hE
  dsimp only [initialState]
  convert h using 1 <;> ring

/-- The actual finite state after `n` complete tail layers. -/
def state (n : ℕ) : FiniteRepairState := d.tail.state d.initialState n

/-- The actual state between two slots of a layer. -/
def partialState (n r : ℕ) : FiniteRepairState := d.tail.partialState d.initialState n r

/-- Permanent finite blocks from the same selected cells and recurrence. -/
def permanentData : PermanentSpectrumData δ :=
  d.tail.permanentSpectrumData δ d.marker_nonneg d.marker_lt_start.le
    d.initialState d.initial_nodes_bounds

/-- The spectrum uses the actual permanent node fibres and their counts. -/
def spectrum : Spectrum := d.permanentData.spectrum (gapFamilyCharge a)

theorem permanentAtomList_eq (n : ℕ) :
    d.permanentData.permanentAtomList (g.start + n) = (δ, 0) :: (d.state n).nodes :=
  d.tail.permanentSpectrumData_permanentAtomList δ d.marker_nonneg d.marker_lt_start.le
    d.initialState d.initial_nodes_bounds n

/-- Complete finite-stage output, clearance, and envelope for this same
selector. These identities are available to compact-test comparison. -/
theorem state_spec (n : ℕ) :
    (d.state n).HasReferenceOutput d.reference δ ∧ (d.state n).ThermalIntegrable ∧
      (d.state n).Cleared ∧
      FrontInvariant (g.start + n) FiniteRepairState.front (d.state n) ∧
      ∀ (j : ℤ) (E : ℝ), (d.state n).front j ≤ E →
        |(d.state n).numerator j E - vacuumLeading (shift (gapFamilyCharge a)) E j| ≤
          exp (7 * sqrt (shift (gapFamilyCharge a) * E)) :=
  d.tail.state_spec d.reference δ d.initialState d.initial_hasReferenceOutput
    d.initial_thermalIntegrable d.initial_cleared d.initial_front_upper d.initial_front
    (fun j E _ hE => d.initial_error_bound j E hE) n

/-- Full admissibility and the fixed-cutoff support condition are proved for
the literal spectrum; the marker does not discard the cell history. -/
theorem realizesFixedCutoff : RealizesFixedCutoff B a δ d.spectrum := by
  have h := d.tail.permanentSpectrumData_pureAdmissible_and_hasUnitScalarGap
    d.reference d.initialState d.marker_nonneg d.marker_lt_start d.initial_nodes_bounds
    (fun p hp => d.marker_lt.trans (d.initial_nodes_cutoff p hp)) d.charge_large
    (by exact_mod_cast g.start_pos) d.initial_hasReferenceOutput d.initial_thermalIntegrable
    d.initial_cleared d.initial_front d.initial_front_upper
    (fun j E _ hE => d.initial_error_bound j E hE)
  refine ⟨?_, ?_⟩
  · simpa only [RealizesGap, spectrum, permanentData, shift_gapFamilyCharge] using h
  · intro p hp hne
    apply realPermanentSpectrumData_support_energy_gt_cutoff d.tail δ B (gapFamilyCharge a)
      d.marker_nonneg d.marker_lt_start.le d.initialState d.initial_nodes_bounds
      d.initial_nodes_cutoff g.cutoff_lt_start p hp
    simpa only [shift_gapFamilyCharge] using hne

end FixedFamilyDatum

end BTZEntropy.Construction
