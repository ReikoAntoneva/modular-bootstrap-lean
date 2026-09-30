import BTZEntropy.Construction.FixedFamilyReference
import BTZEntropy.Construction.FixedFamilySelector
import BTZEntropy.Construction.FixedBandGeometry
import BTZEntropy.Construction.FixedBandInitialCell
import BTZEntropy.Construction.FixedBandBudgetEndpoint
import BTZEntropy.Construction.FixedBandTailData
import GapFamily.GapFamilyLimit

/-!
# Inhabited fixed-cutoff families with actual cell data

The clearing band, processing endpoint, and first tail layer stay fixed as
the charge grows. One charge threshold works for every marker in `[0,B)`.
The admitted class fixes the actual reference and moment degrees and
retains every node selector satisfying the common proved local bounds.
-/

noncomputable section

open Set Filter MeasureTheory Real
open scoped BigOperators

namespace BTZEntropy.Construction

open GapFamily GapFamily.Construction GapFamily.Analytic

/-- The common local admission condition for the explicit fixed geometry.
It fixes the actual reference and degrees, and retains the quantitative
bounds of the same selected initial and tail cells. -/
def fixedFamilyAdmission (B : ℝ) (a : ℝ) (δ : ℝ)
    (d : FixedFamilyDatum (fixedFamilyGeometry B) a δ) : Prop :=
  d.UsesFixedReference (fixedFamilyGeometry_clearing_one B) ∧
    d.HasBounds (fixedFamilyBounds (fixedFamilyGeometry B))

/-- Above one threshold, every marker in the entire fixed interval has
actual initial cells and a local tail selector obeying the common bounds.
This constructs data; no existence of a spectrum is assumed. -/
theorem eventually_actualFixedFamilyDatum (B : ℝ) :
    ∀ᶠ a : ℝ in atTop, ∀ δ ∈ Ico (0 : ℝ) B,
      ∃ d : FixedFamilyDatum (fixedFamilyGeometry B) a δ, fixedFamilyAdmission B a δ d := by
  let g := fixedFamilyGeometry B
  have hb : 1 ≤ g.clearing := fixedFamilyGeometry_clearing_one B
  have hU : 1 ≤ g.upper := by have := fixedFamilyGeometry_upper_sixteen B; linarith
  have hc := eventually_fixedBandInitialCell hb
    (fixedFamilyGeometry_clearing_threshold B) (fixedFamilyGeometry_upper_sixteen B)
    (fixedFamilyGeometry_upper_gain B) (fixedFamilyGeometry_radius_le_upper_div_sixteen B)
    (fixedFamilyGeometry_negative_scale B)
  have ht := eventually_fixedBandTailLocalData_fixedCutoff
    (fixedFamilyGeometry_start_ten B) g.upper_nonneg
  obtain ⟨A, _, _, hbudget⟩ := exists_fixedBand_initialRepair_bound
    (realInitialRows g.radius) hb (fixedFamilyGeometry_ratio_one B) hU
    (fixedFamilyGeometry_upper_eq_ratio B) (by norm_num : (0 : ℝ) < 1 / 8)
  filter_upwards [hc, ht, eventually_ge_atTop A, eventually_ge_atTop (100 : ℝ)]
    with a hc ht hA ha100
  rw [← shift_gapFamilyCharge a] at hc ht hA ha100
  obtain ⟨ha, hba, hcells⟩ := hc
  intro δ hδ
  have hδb : δ ≤ g.clearing := hδ.2.le.trans g.cutoff_le
  let cells : ∀ J : realInitialRows g.radius,
      InitialReferenceCell J (max g.clearing |(J : ℝ)|) g.upper
        (fixedBandDegree (shift (gapFamilyCharge a)) g.upper)
        (fixedCutoffReferenceDensity (shift (gapFamilyCharge a)) g.clearing δ ha hb J) :=
    fun J => Classical.choice (hcells δ hδ.1 hδb J (by
      rw [← fixedFamilyGeometry_radius_eq B]
      exact (mem_realInitialRows g.radius_nonneg J).mp J.property))
  let tail := Classical.choice ht
  let d : FixedFamilyDatum g a δ := {
    marker_nonneg := hδ.1
    marker_lt := hδ.2
    charge_large := ha100
    initialDegree := fixedBandDegree (shift (gapFamilyCharge a)) g.upper
    tailDegree := realTailMomentDegree canonicalTailMomentMultiplier (shift (gapFamilyCharge a))
    density := fixedCutoffReferenceDensity (shift (gapFamilyCharge a)) g.clearing δ ha hb
    reference := ReferenceOutput.fixedCutoff (shift (gapFamilyCharge a)) g.clearing δ ha hb hδ.1 hδb
    initialCell := cells
    tail := tail
    density_thermal := fun j _ hpos =>
      fixedCutoffReferenceDensity_thermal_integrable (shift (gapFamilyCharge a))
        g.clearing δ ha hb hδ.1 hδb j hpos
    density_zero := fixedCutoffReferenceDensity_ae_eq_zero_below_cutoff
      (shift (gapFamilyCharge a)) g.clearing δ ha hb
    reference_output := fun j _ hpos =>
      fixedCutoffReferenceThermalMeasure_eq_marker_add_density
        (shift (gapFamilyCharge a)) g.clearing δ ha hb hδ.1 hδb j hpos
    reference_error := by
      intro j E hE
      apply fixedCutoffReferenceDensity_uniform_error (shift (gapFamilyCharge a))
        g.clearing δ ha hb hδ.1 hδb E j
        (fixedFamilyGeometry_clearing_threshold B) hba
      · rw [← fixedFamilyGeometry_radius_eq B]
        exact (le_max_left _ _).trans hE
      · exact (le_max_right _ _).trans hE
    initial_error := by
      intro j E hE
      have h := hbudget (shift (gapFamilyCharge a)) hA ha δ hδ.1 hδb cells j E hE
      exact h.trans_eq (by ring) }
  have hmodel : d.UsesFixedReference hb := ⟨rfl, rfl, rfl, rfl⟩
  exact ⟨d, hmodel, d.hasBounds_of_usesFixedReference hb hmodel
    (fixedFamilyGeometry_ratio_one B) hba⟩

/-- A single real charge threshold for all admitted markers and cells. -/
theorem exists_actualFixedFamilyThreshold (B : ℝ) :
    ∃ a₀ : ℝ, 1 ≤ a₀ ∧ ∀ a : ℝ, a₀ ≤ a → ∀ δ ∈ Ico (0 : ℝ) B,
      ∃ d : FixedFamilyDatum (fixedFamilyGeometry B) a δ, fixedFamilyAdmission B a δ d := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_actualFixedFamilyDatum B)
  exact ⟨max N 1, le_max_right _ _, fun a ha => hN a ((le_max_left _ _).trans ha)⟩

def fixedFamilyThreshold (B : ℝ) : ℝ := Classical.choose (exists_actualFixedFamilyThreshold B)

theorem fixedFamilyThreshold_pos (B : ℝ) : 1 ≤ fixedFamilyThreshold B :=
  (Classical.choose_spec (exists_actualFixedFamilyThreshold B)).1

theorem fixedFamilyThreshold_spec (B : ℝ) (a : ℝ) (ha : fixedFamilyThreshold B ≤ a)
    (δ : ℝ) (hδ : δ ∈ Ico (0 : ℝ) B) :
    ∃ d : FixedFamilyDatum (fixedFamilyGeometry B) a δ, fixedFamilyAdmission B a δ d :=
  (Classical.choose_spec (exists_actualFixedFamilyThreshold B)).2 a ha δ hδ

/-- Selectors are simultaneous choices of the actual cell data, retaining
the state history and the permanent spectrum of each admitted entry. -/
abbrev ActualFixedFamilySelector (B : ℝ) :=
  FixedFamilySelector (fixedFamilyGeometry B) (fixedFamilyThreshold B)

def fixedFamilySelectors (B : ℝ) : Set (ActualFixedFamilySelector B) :=
  FixedFamilySelector.admitted (fixedFamilyAdmission B)

def fixedFamilySpectrum (B : ℝ) : ActualFixedFamilySelector B → ℝ → ℝ → Spectrum :=
  FixedFamilySelector.spectrum

theorem fixedFamilySelectors_nonempty (B : ℝ) : (fixedFamilySelectors B).Nonempty :=
  FixedFamilySelector.admitted_nonempty (fixedFamilyAdmission B) (fixedFamilyThreshold_spec B)

/-- Membership exposes the quantitative and exact-reference conditions of
the same datum used by the spectrum and its state history. -/
theorem fixedFamily_selected_admission {B : ℝ} {σ : ActualFixedFamilySelector B}
    (hσ : σ ∈ fixedFamilySelectors B) {a : ℝ} (ha : fixedFamilyThreshold B ≤ a)
    {δ : ℝ} (hδ : δ ∈ Ico (0 : ℝ) B) :
    fixedFamilyAdmission B a δ (σ a ha δ hδ) := hσ a ha δ hδ

theorem fixedFamily_selected_hasBounds {B : ℝ} {σ : ActualFixedFamilySelector B}
    (hσ : σ ∈ fixedFamilySelectors B) {a : ℝ} (ha : fixedFamilyThreshold B ≤ a)
    {δ : ℝ} (hδ : δ ∈ Ico (0 : ℝ) B) :
    (σ a ha δ hδ).HasBounds (fixedFamilyBounds (fixedFamilyGeometry B)) :=
  (fixedFamily_selected_admission hσ ha hδ).2

/-- The literal finite initial packet has the common square-root charge
mass scale, including its actual repeated-node multiplicities. -/
theorem fixedFamily_selected_initial_count_le {B : ℝ} {σ : ActualFixedFamilySelector B}
    (hσ : σ ∈ fixedFamilySelectors B) {a : ℝ} (ha : fixedFamilyThreshold B ≤ a)
    {δ : ℝ} (hδ : δ ∈ Ico (0 : ℝ) B) :
    ((σ a ha δ hδ).initialState.nodes.length : ℝ) ≤
      ((realInitialRows (fixedFamilyGeometry B).radius).card : ℝ) *
        fixedFamilyInitialMassBound (fixedFamilyGeometry B) a := by
  simpa [fixedFamilyBounds] using
    (fixedFamily_selected_hasBounds hσ ha hδ).initial_nodes_length_le

/-- A genuine fixed-cutoff family, uniform in every marker and every
admitted selector, with the complete data and bounds retained. -/
theorem actual_uniformFixedCutoffFamily (B : ℝ) (hB : 0 < B) :
    UniformFixedCutoffFamily B (fixedFamilySelectors B) (fixedFamilySpectrum B) :=
  FixedFamilySelector.uniformFixedCutoffFamily hB (fixedFamilyThreshold_pos B)
    (fixedFamilySelectors B) (fixedFamilySelectors_nonempty B)

end BTZEntropy.Construction
