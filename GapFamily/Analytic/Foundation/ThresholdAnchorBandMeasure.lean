import GapFamily.Analytic.Foundation.ReferenceMeasure

/-!
# The ordinary scalar reference measure on the anchor band

The exterior band carries the actual measure `dE/E`. Its finite mass and
atomlessness are separate from the signed numerator used to build the threshold anchor.
-/

noncomputable section

open Set MeasureTheory

namespace GapFamily.Analytic

/-- The compact scalar exterior band used for the threshold anchor. -/
def scalarAnchorBand (B : ℝ) : Set ℝ := Icc (2 * B) (3 * B)

/-- The actual physical scalar reference measure restricted to the anchor band. -/
def scalarAnchorReference (B : ℝ) : Measure ℝ :=
  (referenceMeasure 0).restrict (scalarAnchorBand B)

theorem measurableSet_scalarAnchorBand (B : ℝ) : MeasurableSet (scalarAnchorBand B) :=
  measurableSet_Icc

theorem isCompact_scalarAnchorBand (B : ℝ) : IsCompact (scalarAnchorBand B) :=
  isCompact_Icc

theorem scalarAnchorReference_ae_mem (B : ℝ) :
    ∀ᵐ E ∂scalarAnchorReference B, E ∈ scalarAnchorBand B :=
  ae_restrict_mem (measurableSet_scalarAnchorBand B)

theorem scalarAnchorReference_ae_bounds (B : ℝ) :
    ∀ᵐ E ∂scalarAnchorReference B, 2 * B ≤ E ∧ E ≤ 3 * B :=
  scalarAnchorReference_ae_mem B

theorem scalarAnchorReference_ae_pos (B : ℝ) (hB : 0 < B) :
    ∀ᵐ E ∂scalarAnchorReference B, 0 < E := by
  filter_upwards [scalarAnchorReference_ae_bounds B] with E hE
  linarith [hE.1]

/-- Restriction stays strictly inside the physical scalar half-line. -/
theorem scalarAnchorReference_eq (B : ℝ) (hB : 0 < B) :
    scalarAnchorReference B = (volume.restrict (scalarAnchorBand B)).withDensity
      (fun E => ENNReal.ofReal (1 / E)) := by
  rw [scalarAnchorReference, referenceMeasure_zero,
    restrict_withDensity (measurableSet_scalarAnchorBand B),
    Measure.restrict_restrict (measurableSet_scalarAnchorBand B)]
  have hs : scalarAnchorBand B ∩ Ioi 0 = scalarAnchorBand B := by
    apply inter_eq_left.mpr
    intro E hE
    have hE' : 2 * B ≤ E := hE.1
    change 0 < E
    linarith
  rw [hs]

/-- The base anchor reference measure has no atoms. -/
instance instNullSingletonClassScalarAnchorReference (B : ℝ) :
    NullSingletonClass (scalarAnchorReference B) := by
  unfold scalarAnchorReference
  infer_instance

/-- The full band mass is at most one half, uniformly in positive scale. -/
theorem scalarAnchorReference_measure_le (B : ℝ) (hB : 0 < B) :
    scalarAnchorReference B univ ≤ ENNReal.ofReal (1 / 2 : ℝ) := by
  rw [scalarAnchorReference_eq B hB, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  calc
    _ ≤ ∫⁻ E, ENNReal.ofReal (1 / (2 * B)) ∂volume.restrict (scalarAnchorBand B) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (measurableSet_scalarAnchorBand B)] with E hE
      exact ENNReal.ofReal_le_ofReal (one_div_le_one_div_of_le (by positivity) hE.1)
    _ = ENNReal.ofReal (1 / (2 * B)) * ENNReal.ofReal (3 * B - 2 * B) := by
      simp [lintegral_const, scalarAnchorBand, Real.volume_Icc]
    _ = ENNReal.ofReal (1 / 2 : ℝ) := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / (2 * B))]
      congr 1
      field_simp
      ring

/-- The full band mass is bounded below by one third at every positive scale. -/
theorem scalarAnchorReference_measure_ge (B : ℝ) (hB : 0 < B) :
    ENNReal.ofReal (1 / 3 : ℝ) ≤ scalarAnchorReference B univ := by
  rw [scalarAnchorReference_eq B hB, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  calc
    _ = ENNReal.ofReal (1 / (3 * B)) * ENNReal.ofReal (3 * B - 2 * B) := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / (3 * B))]
      congr 1
      field_simp
      ring
    _ = ∫⁻ E, ENNReal.ofReal (1 / (3 * B)) ∂volume.restrict (scalarAnchorBand B) := by
      simp [lintegral_const, scalarAnchorBand, Real.volume_Icc]
    _ ≤ _ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (measurableSet_scalarAnchorBand B)] with E hE
      have hE0 : 0 < E := by linarith [hE.1]
      exact ENNReal.ofReal_le_ofReal (one_div_le_one_div_of_le hE0 hE.2)

/-- The positive-scale anchor band has ordinary finite reference mass. -/
theorem isFiniteMeasure_scalarAnchorReference (B : ℝ) (hB : 0 < B) :
    IsFiniteMeasure (scalarAnchorReference B) :=
  ⟨lt_of_le_of_lt (scalarAnchorReference_measure_le B hB) ENNReal.ofReal_lt_top⟩

/-- The same uniform mass upper bound expressed as an ordinary real number. -/
theorem scalarAnchorReference_mass_le (B : ℝ) (hB : 0 < B) :
    (scalarAnchorReference B).real univ ≤ 1 / 2 := by
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (scalarAnchorReference_measure_le B hB)
  simpa only [measureReal_def, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2)] using h

/-- The same uniform positive lower bound expressed as ordinary real mass. -/
theorem scalarAnchorReference_mass_ge (B : ℝ) (hB : 0 < B) :
    1 / 3 ≤ (scalarAnchorReference B).real univ := by
  have hfin : scalarAnchorReference B univ ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (scalarAnchorReference_measure_le B hB)
  have h := ENNReal.toReal_mono hfin (scalarAnchorReference_measure_ge B hB)
  simpa only [measureReal_def, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 3)] using h

theorem scalarAnchorReference_mass_pos (B : ℝ) (hB : 0 < B) :
    0 < (scalarAnchorReference B).real univ :=
  lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 3) (scalarAnchorReference_mass_ge B hB)

/-- A numerator continuous only on the compact anchor band is ordinarily
integrable against its actual physical reference measure. -/
theorem scalarAnchorReference_continuousOn_integrable (B : ℝ) (hB : 0 < B)
    {f : ℝ → ℝ} (hf : ContinuousOn f (scalarAnchorBand B)) :
    Integrable f (scalarAnchorReference B) := by
  let _ := isFiniteMeasure_scalarAnchorReference B hB
  have hfin : referenceMeasure 0 (scalarAnchorBand B) ≠ ⊤ := by
    simpa only [scalarAnchorReference, Measure.restrict_apply MeasurableSet.univ,
      univ_inter] using (measure_lt_top (scalarAnchorReference B) univ).ne
  exact hf.integrableOn_of_subset_isCompact (isCompact_scalarAnchorBand B)
    (measurableSet_scalarAnchorBand B) Subset.rfl hfin

/-- Bandwise continuity is sufficient for ordinary measurable integration. -/
theorem scalarAnchorReference_continuousOn_aestronglyMeasurable (B : ℝ) (hB : 0 < B)
    {f : ℝ → ℝ} (hf : ContinuousOn f (scalarAnchorBand B)) :
    AEStronglyMeasurable f (scalarAnchorReference B) :=
  (scalarAnchorReference_continuousOn_integrable B hB hf).aestronglyMeasurable

end GapFamily.Analytic
