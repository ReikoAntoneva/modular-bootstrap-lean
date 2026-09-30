import GapFamily.Construction.FixedCutoffReference
import GapFamily.Construction.FixedCutoffMarkerTransferThermal
import GapFamily.Construction.FixedCutoffReferenceExteriorBound
import GapFamily.Analytic.Poincare.Repair.PoincareExteriorMeasureOutput
import GapFamily.Analytic.Poincare.Repair.PoincareExteriorRegularity

/-!
# Ordinary density of the fixed-cutoff reference

The exact marker transfer has no continuum below its repair cutoff `2B`.
Its exterior density is the actual canonical repair numerator, including the
ordinary anchor band. Gluing at the atom-free endpoint gives the complete
thermal output and retains the unit marker also at zero prescribed gap.
-/

noncomputable section

open MeasureTheory Set
open scoped Classical BigOperators

namespace GapFamily.Construction

open Analytic

variable (a B δ : ℝ) (ha : 2 ≤ a) (hB : 1 ≤ B) (hδ : 0 ≤ δ) (hδB : δ ≤ B)

include hB hδ hδB in
theorem fixedCutoffMarkerTransfer_inside (J : ℤ) :
    ∀ᵐ E ∂(fixedCutoffMarkerTransfer B δ J).variation, E < 2 * B :=
  (fixedCutoffMarkerTransfer_physicalSupport B δ hδ hδB J).mono
    (fun _ h => by linarith [h.2])

/-- The complete transfer below its cutoff consists of its two weighted
markers; the threshold endpoint is included. -/
theorem fixedCutoffMarkerRepairThermalMeasure_restrict_below
    (j : ℤ) {t : ℝ} (ht : 0 < t) :
    (fixedCutoffMarkerRepairThermalMeasure B δ hB hδ hδB j t).restrict (Iio (2 * B)) =
      (if j = 0 then VectorMeasure.dirac δ (Real.exp (-t * δ)) else 0) -
        (if j = 0 then VectorMeasure.dirac B (Real.exp (-t * B)) else 0) := by
  unfold fixedCutoffMarkerRepairThermalMeasure fixedCutoffMarkerRepairInput
  rw [canonicalLocalRepairOutput_eq_input_below_cutoff_with_threshold
    (fixedCutoffMarkerTransfer B δ) (2 * B) (by linarith)
    (fixedCutoffMarkerTransfer_repairSupport B δ hB hδ hδB)
    (fun J _ => fixedCutoffMarkerTransfer_inside B δ hB hδ hδB J) j ht]
  have hinput : (if j ∈ lowBandSpinSet (2 * B) then
      thermalSignedInputMeasure (fixedCutoffMarkerTransfer B δ j) t else 0) =
      thermalSignedInputMeasure (fixedCutoffMarkerTransfer B δ j) t := by
    by_cases hj : j ∈ lowBandSpinSet (2 * B)
    · simp [hj]
    · have hj0 : j ≠ 0 := by
        intro h
        subst j
        exact hj ((zero_mem_lowBandSpinSet (2 * B)).mpr (by linarith))
      rw [ite_eq_right hj,
        thermalSignedInputMeasure_fixedCutoffMarkerTransfer B δ hδ hδB j ht]
      simp [hj0]
  rw [hinput]
  exact fixedCutoffMarkerTransfer_thermal_with_threshold (lowBandSpinSet (2 * B))
    ((zero_mem_lowBandSpinSet (2 * B)).mpr (by linarith)) B δ hδ hδB j ht

/-- No atom lies at the gluing endpoint `2B`. -/
theorem fixedCutoffMarkerRepairThermalMeasure_cutoff_atom
    (j : ℤ) {t : ℝ} (ht : 0 < t) :
    fixedCutoffMarkerRepairThermalMeasure B δ hB hδ hδB j t {2 * B} = 0 := by
  rw [fixedCutoffMarkerRepairThermalMeasure_singleton B δ hB hδ hδB j ht]
  have hδne : 2 * B ≠ δ := by linarith
  have hBne : 2 * B ≠ B := by linarith
  simp [hδne, hBne]

/-- The literal exterior density has zero extension below the repair cutoff. -/
def fixedCutoffMarkerRepairDensity (B δ : ℝ) (hB : 1 ≤ B) (j : ℤ) (e : ℝ) : ℝ :=
  (Ioi (2 * B)).indicator (fun e =>
    (canonicalRepairExteriorNumerator (fixedCutoffMarkerTransfer B δ)
      (2 * B) (by linarith) j e).re) e

/-- The actual reference density excludes precisely the prescribed marker. -/
def fixedCutoffReferenceDensity (a B δ : ℝ) (ha : 2 ≤ a) (hB : 1 ≤ B)
    (j : ℤ) (e : ℝ) : ℝ :=
  canonicalMarkerReferenceDensity a B ha hB j e +
    fixedCutoffMarkerRepairDensity B δ hB j e

theorem fixedCutoffMarkerRepairDensity_eq_zero_of_le (j : ℤ) {e : ℝ}
    (he : e ≤ 2 * B) : fixedCutoffMarkerRepairDensity B δ hB j e = 0 :=
  indicator_of_notMem (not_lt.mpr he) _

theorem fixedCutoffReferenceDensity_eq_original_of_le (j : ℤ) {e : ℝ}
    (he : e ≤ 2 * B) :
    fixedCutoffReferenceDensity a B δ ha hB j e =
      canonicalMarkerReferenceDensity a B ha hB j e := by
  rw [fixedCutoffReferenceDensity,
    fixedCutoffMarkerRepairDensity_eq_zero_of_le B δ hB j he, add_zero]

include hδ hδB in
theorem fixedCutoffMarkerRepairDensity_thermal_integrable (j : ℤ)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun e => Real.exp (-t * e) * fixedCutoffMarkerRepairDensity B δ hB j e)
      (referenceMeasure j) := by
  have h := (integrable_canonicalRepairExteriorNumerator_thermal
    (fixedCutoffMarkerTransfer B δ) (2 * B) (by linarith)
    (fixedCutoffMarkerTransfer_repairSupport B δ hB hδ hδB) j ht).indicator
      (s := Ioi (2 * B)) measurableSet_Ioi
  convert h using 1
  ext e
  by_cases he : e ∈ Ioi (2 * B) <;> simp [fixedCutoffMarkerRepairDensity, he]

include hδ hδB in
theorem fixedCutoffReferenceDensity_thermal_integrable (j : ℤ)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun e => Real.exp (-t * e) * fixedCutoffReferenceDensity a B δ ha hB j e)
      (referenceMeasure j) := by
  simpa only [fixedCutoffReferenceDensity, mul_add, Pi.add_apply] using!
    (canonicalMarkerReferenceDensity_thermal_integrable a B ha hB j ht).add
      (fixedCutoffMarkerRepairDensity_thermal_integrable B δ hB hδ hδB j ht)

include hδ hδB in
theorem fixedCutoffReferenceDensity_integrable (W : ℝ) (j : ℤ) :
    Integrable (fixedCutoffReferenceDensity a B δ ha hB j)
      ((referenceMeasure j).restrict (Ioo |(j : ℝ)| W)) := by
  exact (canonicalMarkerReferenceDensity_integrable a B W ha hB j).add
    ((integrableOn_re_canonicalRepairExteriorNumerator (fixedCutoffMarkerTransfer B δ)
      (2 * B) (by linarith) (fixedCutoffMarkerTransfer_repairSupport B δ hB hδ hδB)
      j W).indicator measurableSet_Ioi)

include hδ hδB in
theorem fixedCutoffReferenceDensity_aestronglyMeasurable (j : ℤ) :
    AEStronglyMeasurable (fixedCutoffReferenceDensity a B δ ha hB j)
      (referenceMeasure j) := by
  exact (canonicalMarkerReferenceDensity_stronglyMeasurable a B ha hB j).aestronglyMeasurable.add
    ((Complex.continuous_re.comp_aestronglyMeasurable
      (aestronglyMeasurable_canonicalRepairExteriorNumerator
        (fixedCutoffMarkerTransfer B δ) (2 * B) (by linarith)
        (fixedCutoffMarkerTransfer_repairSupport B δ hB hδ hδB) j)).indicator measurableSet_Ioi)

include hδ hδB in
/-- The physical zero extension is an everywhere strongly measurable density. -/
theorem fixedCutoffReferenceDensity_indicator_stronglyMeasurable (j : ℤ) :
    StronglyMeasurable ((Ioi |(j : ℝ)|).indicator
      (fixedCutoffReferenceDensity a B δ ha hB j)) := by
  have hc := (canonicalMarkerReferenceDensity_stronglyMeasurable a B ha hB j).indicator
    (s := Ioi |(j : ℝ)|) measurableSet_Ioi
  have hr := (measurable_indicator_re_canonicalRepairExteriorNumerator
    (fixedCutoffMarkerTransfer B δ) (2 * B) (by linarith)
    (fixedCutoffMarkerTransfer_repairSupport B δ hB hδ hδB) j).stronglyMeasurable.indicator
      (s := Ioi (2 * B)) measurableSet_Ioi
  convert hc.add hr using 1
  ext e
  by_cases hphysical : e ∈ Ioi |(j : ℝ)| <;>
    by_cases hcut : e ∈ Ioi (2 * B) <;>
    simp [fixedCutoffReferenceDensity, fixedCutoffMarkerRepairDensity, hphysical, hcut]

/-- The same density vanishes almost everywhere below the larger of the
clearing cutoff and the physical spin edge. -/
theorem fixedCutoffReferenceDensity_ae_eq_zero_below_cutoff (j : ℤ) :
    ∀ᵐ e ∂referenceMeasure j, e < max B |(j : ℝ)| →
      fixedCutoffReferenceDensity a B δ ha hB j e = 0 := by
  have hgap : ∀ᵐ e ∂referenceMeasure j, e < B →
      canonicalMarkerReferenceDensity a B ha hB j e = 0 :=
    (ae_restrict_iff' measurableSet_Iio).mp
      (canonicalMarkerReferenceDensity_ae_eq_zero_below_cutoff a B ha hB j)
  filter_upwards [hgap, referenceMeasure_ae_above_edge j] with e he hedge hmax
  have heB : e < B := (lt_max_iff.mp hmax).resolve_right (not_lt.mpr hedge.le)
  have hcut : e ∉ Ioi (2 * B) := by
    change ¬2 * B < e
    linarith
  simp [fixedCutoffReferenceDensity, fixedCutoffMarkerRepairDensity, he heB, hcut]

private theorem fixedCutoff_restricted_density_eq_indicator (μ : Measure ℝ)
    (s : Set ℝ) (hs : MeasurableSet s) (f : ℝ → ℝ)
    (hf : Integrable f (μ.restrict s)) :
    (μ.restrict s).withDensityᵥ f = μ.withDensityᵥ (s.indicator f) := by
  ext u hu
  rw [withDensityᵥ_apply hf hu,
    withDensityᵥ_apply ((integrable_indicator_iff hs).mpr hf) hu,
    setIntegral_indicator hs, Measure.restrict_restrict hu]

/-- The entire repaired output is its literal marker difference plus the
ordinary exterior density, with no omitted endpoint measure. -/
theorem fixedCutoffMarkerRepairThermalMeasure_eq_marker_sub_add_density
    (j : ℤ) {t : ℝ} (ht : 0 < t) :
    fixedCutoffMarkerRepairThermalMeasure B δ hB hδ hδB j t =
      ((if j = 0 then VectorMeasure.dirac δ (Real.exp (-t * δ)) else 0) -
        (if j = 0 then VectorMeasure.dirac B (Real.exp (-t * B)) else 0)) +
      (referenceMeasure j).withDensityᵥ
        (fun e => Real.exp (-t * e) * fixedCutoffMarkerRepairDensity B δ hB j e) := by
  have hsplit := VectorMeasure.restrict_add_restrict_compl
    (v := fixedCutoffMarkerRepairThermalMeasure B δ hB hδ hδB j t)
    (measurableSet_Iic (a := 2 * B))
  rw [compl_Iic, signedMeasure_restrict_Iic_eq,
    fixedCutoffMarkerRepairThermalMeasure_restrict_below B δ hB hδ hδB j ht,
    fixedCutoffMarkerRepairThermalMeasure_cutoff_atom B δ hB hδ hδB j ht,
    VectorMeasure.dirac_zero, add_zero] at hsplit
  rw [← hsplit]
  congr 1
  change (correctedThermalFiniteOutputMeasure (lowBandSpinSet (2 * B))
    (canonicalLocalRepairInput (fixedCutoffMarkerTransfer B δ) (2 * B) (by linarith)
      (fixedCutoffMarkerTransfer_repairSupport B δ hB hδ hδB)) j t).restrict
        (Ioi (2 * B)) = _
  rw [canonicalLocalRepairOutput_restrict_exterior
    (fixedCutoffMarkerTransfer B δ) (2 * B) (by linarith)
    (fixedCutoffMarkerTransfer_repairSupport B δ hB hδ hδB)
    (fun J _ => fixedCutoffMarkerTransfer_inside B δ hB hδ hδB J) j ht,
    fixedCutoff_restricted_density_eq_indicator _ _ measurableSet_Ioi _
      (integrable_canonicalRepairExteriorNumerator_thermal
        (fixedCutoffMarkerTransfer B δ) (2 * B) (by linarith)
        (fixedCutoffMarkerTransfer_repairSupport B δ hB hδ hδB) j ht).restrict]
  congr 1
  ext e
  by_cases he : e ∈ Ioi (2 * B) <;> simp [fixedCutoffMarkerRepairDensity, he]

/-- The same modular seed's full ordinary output is exactly its one scalar
unit marker and its integrable continuum, including prescribed zero gap. -/
theorem fixedCutoffReferenceThermalMeasure_eq_marker_add_density
    (j : ℤ) {t : ℝ} (ht : 0 < t) :
    fixedCutoffReferenceThermalMeasure a B δ ha hB hδ hδB j t =
      (if j = 0 then VectorMeasure.dirac δ (Real.exp (-t * δ)) else 0) +
      (referenceMeasure j).withDensityᵥ
        (fun e => Real.exp (-t * e) * fixedCutoffReferenceDensity a B δ ha hB j e) := by
  rw [fixedCutoffReferenceThermalMeasure,
    canonicalMarkerReferenceThermalMeasure_eq_marker_add_density a B ha hB j ht,
    fixedCutoffMarkerRepairThermalMeasure_eq_marker_sub_add_density B δ hB hδ hδB j ht]
  have hsplit : (fun e => Real.exp (-t * e) * fixedCutoffReferenceDensity a B δ ha hB j e) =
      (fun e => Real.exp (-t * e) * canonicalMarkerReferenceDensity a B ha hB j e) +
      (fun e => Real.exp (-t * e) * fixedCutoffMarkerRepairDensity B δ hB j e) := by
    funext e
    simp only [fixedCutoffReferenceDensity, Pi.add_apply, mul_add]
  rw [hsplit, withDensityᵥ_add
    (canonicalMarkerReferenceDensity_thermal_integrable a B ha hB j ht)
    (fixedCutoffMarkerRepairDensity_thermal_integrable B δ hB hδ hδB j ht)]
  abel

/-- Past all compact direct input, the reference has the vacuum reference
kernel plus the literal repair exterior kernel. -/
theorem fixedCutoffReferenceDensity_eq_exteriorNumerator (j : ℤ) {e : ℝ}
    (he : 6 * B < e) :
    fixedCutoffReferenceDensity a B δ ha hB j e =
      canonicalMarkerReferenceKernelNumerator a B ha hB j e +
        (canonicalRepairExteriorNumerator (fixedCutoffMarkerTransfer B δ)
          (2 * B) (by linarith) j e).re := by
  rw [fixedCutoffReferenceDensity,
    canonicalMarkerReferenceDensity_eq_kernelNumerator a B ha hB j (by linarith),
    fixedCutoffMarkerRepairDensity, indicator_of_mem (show e ∈ Ioi (2 * B) by
      change 2 * B < e
      linarith)]

/-- Beyond the actual direct anchor band the density is precisely the kernel
numerator used by the uniform exterior estimates. -/
theorem fixedCutoffReferenceDensity_eq_kernelNumerator (j : ℤ) {e : ℝ}
    (he : 6 * B < e) (hphysical : |(j : ℝ)| ≤ e) :
    fixedCutoffReferenceDensity a B δ ha hB j e =
      fixedCutoffReferenceKernelNumerator a B δ ha hB hδ hδB j e := by
  rw [fixedCutoffReferenceDensity_eq_exteriorNumerator a B δ ha hB j he,
    canonicalRepairExteriorNumerator_re_eq (fixedCutoffMarkerTransfer B δ)
      (2 * B) (by linarith) (fixedCutoffMarkerTransfer_repairSupport B δ hB hδ hδB)
      j e hphysical]
  have hanchor : scalarAnchorNumerator (2 * B)
      (scalarAnchorResponsePhysical (fun J : lowBandSpinSet (2 * B) => (J : ℤ))
        (2 * B) (by linarith)) e = 0 := by
    apply indicator_of_notMem
    change e ∉ Icc (2 * (2 * B)) (3 * (2 * B))
    intro h
    linarith [h.2]
  simp only [hanchor, ite_self, mul_zero, zero_add,
    fixedCutoffReferenceKernelNumerator, fixedCutoffMarkerRepairInput]

include hδ hδB in
/-- The fixed-cutoff density satisfies the universal exterior approximation
with constants chosen before the prescribed marker position. -/
theorem fixedCutoffReferenceDensity_uniform_error (e : ℝ) (j : ℤ)
    (hnB : (fixedCutoffReferenceBandThreshold : ℝ) ≤ B) (hBa : B ≤ a)
    (hRe : (fixedCutoffReferenceRadius : ℝ) * B ≤ e) (hje : |(j : ℝ)| ≤ e) :
    |fixedCutoffReferenceDensity a B δ ha hB j e - vacuumLeading a e j| ≤
      Real.exp (7 * Real.sqrt (a * e)) / 2 := by
  have hR : (6 : ℝ) < fixedCutoffReferenceRadius := by
    exact_mod_cast fixedCutoffReferenceRadius_gt_six
  have h6 : 6 * B < e :=
    (mul_lt_mul_of_pos_right hR (by linarith : 0 < B)).trans_le hRe
  rw [fixedCutoffReferenceDensity_eq_kernelNumerator a B δ ha hB hδ hδB j h6 hje]
  exact fixedCutoffReferenceKernelNumerator_uniform_error a B δ ha hB hδ hδB
    e j hnB hBa hRe hje

include hδ hδB in
/-- The positive exterior keeps the quantitative vacuum edge factor. -/
theorem fixedCutoffReferenceDensity_lower (e : ℝ) (j : ℤ)
    (hnB : (fixedCutoffReferenceBandThreshold : ℝ) ≤ B) (hBa : B ≤ a)
    (hRe : (fixedCutoffReferenceRadius : ℝ) * B ≤ e) (hedge : |(j : ℝ)| + 1 ≤ e) :
    (Real.pi ^ 4 / 625) * (e ^ 2 - (j : ℝ) ^ 2) * Real.exp (8 * Real.sqrt (a * e)) ≤
      fixedCutoffReferenceDensity a B δ ha hB j e := by
  have ha100 : 100 ≤ a := by
    have ht : (100 : ℝ) ≤ fixedCutoffReferenceBandThreshold := by
      exact_mod_cast fixedCutoffReferenceBandThreshold_ge_hundred
    exact ht.trans (hnB.trans hBa)
  apply referenceDensity_lower_of_vacuum_error j ha100 hedge
    (fixedCutoffReferenceDensity a B δ ha hB j)
  exact (fixedCutoffReferenceDensity_uniform_error a B δ ha hB hδ hδB e j hnB hBa hRe
    (by linarith)).trans (by have := Real.exp_pos (7 * Real.sqrt (a * e)); linarith)

include hδ hδB in
/-- Each low-spin row is positive past the uniformly enlarged cutoff. -/
theorem fixedCutoffReferenceDensity_pos_above (j : ℤ)
    (hnB : (fixedCutoffReferenceBandThreshold : ℝ) ≤ B) (hBa : B ≤ a)
    (hj : |(j : ℝ)| ≤ (fixedCutoffReferenceRadius : ℝ) * B)
    {e : ℝ} (he : (fixedCutoffReferenceRadius : ℝ) * B + 1 ≤ e) :
    0 < fixedCutoffReferenceDensity a B δ ha hB j e := by
  have hedge : |(j : ℝ)| + 1 ≤ e := by linarith
  have hedgesq := one_le_energy_sq_sub_spin_sq j hedge
  exact lt_of_lt_of_le (by positivity)
    (fixedCutoffReferenceDensity_lower a B δ ha hB hδ hδB e j hnB hBa (by linarith) hedge)

end GapFamily.Construction
