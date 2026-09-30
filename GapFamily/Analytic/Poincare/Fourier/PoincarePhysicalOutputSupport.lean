import GapFamily.Analytic.Foundation.SignedPhysicalSupport
import GapFamily.Analytic.Foundation.FiniteSeedThreshold

/-! Actual support of physical signed input and its complete corrected thermal output. -/

noncomputable section

namespace GapFamily.Analytic

open Set MeasureTheory

/-- A lower bound almost everywhere for the variation excludes all lower energies. -/
theorem signedVariation_Iio_eq_zero_of_ae_ge (ν : SignedMeasure ℝ) (a : ℝ)
    (hν : ∀ᵐ E ∂ν.variation, a ≤ E) : ν.variation (Iio a) = 0 := by
  rw [measure_eq_zero_iff_ae_notMem]
  exact hν.mono fun E hE ↦ not_lt.mpr hE

/-- Every subset below an almost-everywhere energy bound has zero signed mass. -/
theorem signedMeasure_apply_eq_zero_of_ae_ge (ν : SignedMeasure ℝ) (a : ℝ)
    (hν : ∀ᵐ E ∂ν.variation, a ≤ E) (s : Set ℝ) (hs : s ⊆ Iio a) :
    ν s = 0 := by
  apply enorm_eq_zero.mp
  apply le_antisymm _ (by positivity)
  calc
    ‖ν s‖ₑ ≤ ν.variation s := VectorMeasure.enorm_measure_le_variation ν s
    _ ≤ ν.variation (Iio a) := measure_mono hs
    _ = 0 := signedVariation_Iio_eq_zero_of_ae_ge ν a hν

/-- Restricting to a measurable set below the physical lower bound gives zero. -/
theorem signedMeasure_restrict_eq_zero_of_ae_ge (ν : SignedMeasure ℝ) (a : ℝ)
    (hν : ∀ᵐ E ∂ν.variation, a ≤ E) (s : Set ℝ) (hset : MeasurableSet s)
    (hs : s ⊆ Iio a) : ν.restrict s = 0 := by
  apply VectorMeasure.variation_eq_zero.mp
  rw [VectorMeasure.variation_restrict hset, Measure.restrict_eq_zero]
  exact measure_mono_null hs (signedVariation_Iio_eq_zero_of_ae_ge ν a hν)

/-- Compact physical support excludes every atom below the spin threshold. -/
theorem signedPhysicalSupport_singleton_eq_zero (ν : SignedMeasure ℝ) (J : ℤ) (B : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ B) (e : ℝ)
    (he : e < |(J : ℝ)|) : ν {e} = 0 := by
  apply signedMeasure_apply_eq_zero_of_ae_ge ν |(J : ℝ)| (hs.mono fun _ hE ↦ hE.1)
  exact singleton_subset_iff.mpr he

/-- The ordinary reference measure vanishes on and below its physical edge. -/
theorem referenceMeasure_apply_eq_zero_below_edge (j : ℤ) (s : Set ℝ)
    (hs : s ⊆ Iic |(j : ℝ)|) : (referenceMeasure j) s = 0 := by
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [referenceMeasure_ae_above_edge j] with e he
  intro hes
  exact (not_le_of_gt he) (hs hes)

/-- The actual continuum vanishes on every measurable set at or below the output edge. -/
theorem correctedThermalContinuumMeasure_apply_eq_zero_below_edge
    (ν : SignedMeasure ℝ) (J j : ℤ) (B : ℝ)
    (hν : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ B) {t : ℝ} (ht : 0 < t)
    (s : Set ℝ) (hset : MeasurableSet s) (hs : s ⊆ Iic |(j : ℝ)|) :
    correctedThermalContinuumMeasure ν J j t s = 0 := by
  rw [correctedThermalContinuumMeasure_apply ν J j B hν ht s hset,
    Measure.restrict_eq_zero.mpr (referenceMeasure_apply_eq_zero_below_edge j s hs),
    integral_zero_measure]

/-- Positive thermal tilting preserves the physical lower support of the direct input. -/
theorem thermalSignedInputMeasure_apply_eq_zero_below_edge
    (ν : SignedMeasure ℝ) (J : ℤ) (B : ℝ)
    (hν : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ B) {t : ℝ} (ht : 0 < t)
    (s : Set ℝ) (hset : MeasurableSet s) (hs : s ⊆ Iio |(J : ℝ)|) :
    thermalSignedInputMeasure ν t s = 0 := by
  rw [thermalSignedInputMeasure_apply ν J B hν ht]
  have hr := signedMeasure_restrict_eq_zero_of_ae_ge ν |(J : ℝ)|
    (hν.mono fun _ hE => hE.1) s hset hs
  rw [hr]
  simp

/-- Every component of a physical row output vanishes below the output spin edge. -/
theorem correctedThermalRowOutputMeasure_apply_eq_zero_below_edge
    (ν : SignedMeasure ℝ) (J j : ℤ) (B : ℝ)
    (hν : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ B) {t : ℝ} (ht : 0 < t)
    (s : Set ℝ) (hset : MeasurableSet s) (hs : s ⊆ Iio |(j : ℝ)|) :
    correctedThermalRowOutputMeasure ν J j t s = 0 := by
  have hcont : (∫ e in s, correctedThermalRowDensity ν J j t e ∂referenceMeasure j) = 0 := by
    rw [← correctedThermalContinuumMeasure_apply ν J j B hν ht s hset]
    exact correctedThermalContinuumMeasure_apply_eq_zero_below_edge ν J j B hν ht s hset
      (hs.trans Iio_subset_Iic_self)
  have hinput : (if j = J then ∫ᵛ E in s, Real.exp (-t * E) ∂<•ν else 0) = 0 := by
    split_ifs with hj
    · subst j
      rw [← thermalSignedInputMeasure_apply ν J B hν ht]
      exact thermalSignedInputMeasure_apply_eq_zero_below_edge ν J B hν ht s hset hs
    · rfl
  rw [correctedThermalRowOutputMeasure_apply ν J j B hν ht s hset,
    hcont, hinput, add_zero, zero_add]
  apply ite_eq_right
  intro h
  have hzero := hs h.2
  simp only [h.1, Int.cast_zero, abs_zero, mem_Iio, lt_self_iff_false] at hzero

/-- Complete finite signed output has no mass on any measurable set below its physical edge. -/
theorem correctedThermalFiniteOutputMeasure_apply_eq_zero_below_edge
    (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ) (j : ℤ) (B : ℝ)
    (hν : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ B)
    {t : ℝ} (ht : 0 < t) (s : Set ℝ) (hset : MeasurableSet s)
    (hs : s ⊆ Iio |(j : ℝ)|) :
    correctedThermalFiniteOutputMeasure S ν j t s = 0 := by
  rw [correctedThermalFiniteOutputMeasure_apply]
  apply Finset.sum_eq_zero
  intro J hJ
  exact correctedThermalRowOutputMeasure_apply_eq_zero_below_edge (ν J) J j B (hν J hJ)
    ht s hset hs

/-- Vanishing below the output edge holds as an equality of actual signed measures. -/
theorem correctedThermalFiniteOutputMeasure_restrict_below_edge
    (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ) (j : ℤ) (B : ℝ)
    (hν : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ B)
    {t : ℝ} (ht : 0 < t) :
    (correctedThermalFiniteOutputMeasure S ν j t).restrict (Iio |(j : ℝ)|) = 0 := by
  ext s hs
  rw [VectorMeasure.restrict_apply _ measurableSet_Iio hs, _root_.zero_apply]
  exact correctedThermalFiniteOutputMeasure_apply_eq_zero_below_edge S ν j B hν ht
    (s ∩ Iio |(j : ℝ)|) (hs.inter measurableSet_Iio) inter_subset_right

/-- The variation of the complete finite signed output is supported in the closed physical cone. -/
theorem correctedThermalFiniteOutputMeasure_ae_physical
    (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ) (j : ℤ) (B : ℝ)
    (hν : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ B)
    {t : ℝ} (ht : 0 < t) :
    ∀ᵐ E ∂(correctedThermalFiniteOutputMeasure S ν j t).variation, |(j : ℝ)| ≤ E := by
  have hr : (correctedThermalFiniteOutputMeasure S ν j t).variation.restrict
      (Iio |(j : ℝ)|) = 0 := by
    rw [← VectorMeasure.variation_restrict measurableSet_Iio,
      correctedThermalFiniteOutputMeasure_restrict_below_edge S ν j B hν ht,
      VectorMeasure.variation_zero]
  have hzero := Measure.restrict_eq_zero.mp hr
  exact (measure_eq_zero_iff_ae_notMem.mp hzero).mono fun E hE => le_of_not_gt hE

/-- Physical finite signed input cannot produce mass at negative energy. -/
theorem correctedThermalFiniteOutputMeasure_apply_eq_zero_negative
    (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ) (j : ℤ) (B : ℝ)
    (hν : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ B)
    {t : ℝ} (ht : 0 < t) (s : Set ℝ) (hset : MeasurableSet s) (hs : s ⊆ Iio (0 : ℝ)) :
    correctedThermalFiniteOutputMeasure S ν j t s = 0 :=
  correctedThermalFiniteOutputMeasure_apply_eq_zero_below_edge S ν j B hν ht s hset
    (hs.trans (Iio_subset_Iio (abs_nonneg _)))

/-- The negative-energy restriction of the actual physical repair output is zero. -/
theorem correctedThermalFiniteOutputMeasure_restrict_negative
    (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ) (j : ℤ) (B : ℝ)
    (hν : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ B)
    {t : ℝ} (ht : 0 < t) :
    (correctedThermalFiniteOutputMeasure S ν j t).restrict (Iio (0 : ℝ)) = 0 := by
  ext s hs
  rw [VectorMeasure.restrict_apply _ measurableSet_Iio hs, _root_.zero_apply]
  exact correctedThermalFiniteOutputMeasure_apply_eq_zero_negative S ν j B hν ht
    (s ∩ Iio (0 : ℝ)) (hs.inter measurableSet_Iio) inter_subset_right

/-- Adding the actual physical repair leaves the entire negative-energy vacuum measure unchanged. -/
theorem add_correctedThermalFiniteOutputMeasure_restrict_negative
    (σ : SignedMeasure ℝ) (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ) (j : ℤ) (B : ℝ)
    (hν : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ B)
    {t : ℝ} (ht : 0 < t) :
    (σ + correctedThermalFiniteOutputMeasure S ν j t).restrict (Iio (0 : ℝ)) =
      σ.restrict (Iio (0 : ℝ)) := by
  ext s hs
  rw [VectorMeasure.restrict_apply _ measurableSet_Iio hs,
    VectorMeasure.restrict_apply _ measurableSet_Iio hs, _root_.add_apply,
    correctedThermalFiniteOutputMeasure_apply_eq_zero_negative S ν j B hν ht
      (s ∩ Iio (0 : ℝ)) (hs.inter measurableSet_Iio) inter_subset_right, add_zero]

end GapFamily.Analytic
