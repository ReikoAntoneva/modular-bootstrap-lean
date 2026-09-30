import GapFamily.Analytic.Foundation.MomentCancellation
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! The square-root energy coordinate for an actual finite signed input.
The coordinate measure is a genuine pushforward. Physical support makes its
energy pushforward equal to the original input and preserves total mass of
variation, while compact support supplies ordinary change-of-variable integrals.
-/

noncomputable section

namespace GapFamily.Analytic

open MeasureTheory Set

def sqrtEnergyCoordinate (J : ℤ) (E : ℝ) : ℝ := Real.sqrt (E - |(J : ℝ)|)

def sqrtCoordinateEnergy (J : ℤ) (x : ℝ) : ℝ := |(J : ℝ)| + x ^ 2

def signedSqrtCoordinate (J : ℤ) (ν : SignedMeasure ℝ) : SignedMeasure ℝ :=
  ν.map (sqrtEnergyCoordinate J)

theorem continuous_sqrtEnergyCoordinate (J : ℤ) : Continuous (sqrtEnergyCoordinate J) :=
  Real.continuous_sqrt.comp (continuous_id.sub continuous_const)

theorem continuous_sqrtCoordinateEnergy (J : ℤ) : Continuous (sqrtCoordinateEnergy J) :=
  continuous_const.add (continuous_id.pow 2)

theorem sqrtCoordinateEnergy_sqrtEnergyCoordinate (J : ℤ) {E : ℝ}
    (hE : |(J : ℝ)| ≤ E) :
    sqrtCoordinateEnergy J (sqrtEnergyCoordinate J E) = E := by
  simp only [sqrtCoordinateEnergy, sqrtEnergyCoordinate, Real.sq_sqrt (sub_nonneg.mpr hE)]
  ring

theorem sqrtEnergyCoordinate_sqrtCoordinateEnergy (J : ℤ) {x : ℝ} (hx : 0 ≤ x) :
    sqrtEnergyCoordinate J (sqrtCoordinateEnergy J x) = x := by
  simp [sqrtEnergyCoordinate, sqrtCoordinateEnergy, Real.sqrt_sq hx]

theorem signedSqrtCoordinate_variation_le (J : ℤ) (ν : SignedMeasure ℝ) :
    (signedSqrtCoordinate J ν).variation ≤ ν.variation.map (sqrtEnergyCoordinate J) :=
  VectorMeasure.variation_map_le

theorem signedSqrtCoordinate_ae_mem (J : ℤ) (ν : SignedMeasure ℝ) {L V : ℝ}
    (hν : ∀ᵐ E ∂ν.variation, E ∈ Icc L V) :
    ∀ᵐ x ∂(signedSqrtCoordinate J ν).variation,
      x ∈ Icc (Real.sqrt (L - |(J : ℝ)|)) (Real.sqrt (V - |(J : ℝ)|)) := by
  apply (ae_mono (signedSqrtCoordinate_variation_le J ν))
  apply (ae_map_iff (continuous_sqrtEnergyCoordinate J).measurable.aemeasurable
    measurableSet_Icc).mpr
  exact hν.mono fun E hE =>
    ⟨Real.sqrt_le_sqrt (sub_le_sub_right hE.1 _),
      Real.sqrt_le_sqrt (sub_le_sub_right hE.2 _)⟩

theorem signedSqrtCoordinate_ae_nonneg (J : ℤ) (ν : SignedMeasure ℝ) :
    ∀ᵐ x ∂(signedSqrtCoordinate J ν).variation, 0 ≤ x := by
  apply (ae_mono (signedSqrtCoordinate_variation_le J ν))
  apply (ae_map_iff (continuous_sqrtEnergyCoordinate J).measurable.aemeasurable
    measurableSet_Ici).mpr
  exact Filter.Eventually.of_forall fun E => Real.sqrt_nonneg _

private theorem signedMeasure_apply_congr_ae (ν : SignedMeasure ℝ) {s t : Set ℝ}
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hst : s =ᵐ[ν.variation] t) :
    ν s = ν t := by
  change (∀ᵐ x ∂ν.variation, s x = t x) at hst
  rw [← SignedMeasure.totalVariation_eq_variation, SignedMeasure.totalVariation,
    ae_add_measure_iff] at hst
  rw [ν.apply_eq_posPart_real_sub_negPart_real hs,
    ν.apply_eq_posPart_real_sub_negPart_real ht,
    measureReal_congr hst.1, measureReal_congr hst.2]

/-- Pushing the actual coordinate measure back to energy recovers every
physical signed input, with no density or atomlessness assumption. -/
theorem signedSqrtCoordinate_map_energy (J : ℤ) (ν : SignedMeasure ℝ)
    (hν : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E) :
    (signedSqrtCoordinate J ν).map (sqrtCoordinateEnergy J) = ν := by
  apply VectorMeasure.ext
  intro s hs
  rw [VectorMeasure.map_apply _ (continuous_sqrtCoordinateEnergy J).measurable hs,
    signedSqrtCoordinate, VectorMeasure.map_apply _
      (continuous_sqrtEnergyCoordinate J).measurable
      ((continuous_sqrtCoordinateEnergy J).measurable hs)]
  apply signedMeasure_apply_congr_ae ν
    ((continuous_sqrtEnergyCoordinate J).measurable
      ((continuous_sqrtCoordinateEnergy J).measurable hs)) hs
  exact hν.mono fun E hE => by
    simp only [mem_preimage, sqrtCoordinateEnergy_sqrtEnergyCoordinate J hE]

private theorem signedMeasure_map_variation_mass_le (ν : SignedMeasure ℝ)
    (f : ℝ → ℝ) (hf : Measurable f) :
    (ν.map f).variation.real univ ≤ ν.variation.real univ := by
  have hle := VectorMeasure.variation_map_le (μ := ν) (φ := f)
  have h := hle univ
  rw [Measure.map_apply hf MeasurableSet.univ, preimage_univ] at h
  apply ENNReal.toReal_mono _ h
  rw [← SignedMeasure.totalVariation_eq_variation]
  exact measure_ne_top _ _

theorem signedSqrtCoordinate_variation_mass_le (J : ℤ) (ν : SignedMeasure ℝ) :
    (signedSqrtCoordinate J ν).variation.real univ ≤ ν.variation.real univ :=
  signedMeasure_map_variation_mass_le ν _ (continuous_sqrtEnergyCoordinate J).measurable

/-- The square-root change of coordinate loses no total variation on physical
inputs, including inputs with signed atoms. -/
theorem signedSqrtCoordinate_variation_mass_eq (J : ℤ) (ν : SignedMeasure ℝ)
    (hν : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E) :
    (signedSqrtCoordinate J ν).variation.real univ = ν.variation.real univ := by
  apply le_antisymm (signedSqrtCoordinate_variation_mass_le J ν)
  have h := signedMeasure_map_variation_mass_le (signedSqrtCoordinate J ν)
    (sqrtCoordinateEnergy J) (continuous_sqrtCoordinateEnergy J).measurable
  rwa [signedSqrtCoordinate_map_energy J ν hν] at h

theorem signedSqrtCoordinate_totalVariation_mass_eq (J : ℤ) (ν : SignedMeasure ℝ)
    (hν : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E) :
    (signedSqrtCoordinate J ν).totalVariation.real univ = ν.totalVariation.real univ := by
  simpa only [SignedMeasure.totalVariation_eq_variation] using
    signedSqrtCoordinate_variation_mass_eq J ν hν

theorem signedIntegral_sqrtCoordinate {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (J : ℤ) (ν : SignedMeasure ℝ) {f : ℝ → F}
    (hf : StronglyMeasurable f)
    (hi : ν.Integrable (f ∘ sqrtEnergyCoordinate J)) :
    (∫ᵛ x, f x ∂<•signedSqrtCoordinate J ν) =
      ∫ᵛ E, f (sqrtEnergyCoordinate J E) ∂<•ν :=
  VectorMeasure.integral_map (continuous_sqrtEnergyCoordinate J).measurable
    hf.aestronglyMeasurable hi

/-- A continuous observable of the coordinate has an ordinary signed integral
on any compact energy input, and its change of variable is exact. -/
theorem signedIntegral_sqrtCoordinate_of_continuous {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (J : ℤ) (ν : SignedMeasure ℝ) {f : ℝ → F} {L V : ℝ}
    (hf : Continuous f) (hν : ∀ᵐ E ∂ν.variation, E ∈ Icc L V) :
    (∫ᵛ x, f x ∂<•signedSqrtCoordinate J ν) =
      ∫ᵛ E, f (sqrtEnergyCoordinate J E) ∂<•ν := by
  let := signedMeasure_isFiniteMeasure_variation ν
  apply signedIntegral_sqrtCoordinate J ν hf.stronglyMeasurable
  exact integrable_of_continuousOn_interval_of_ae_mem
    (hf.comp (continuous_sqrtEnergyCoordinate J)).continuousOn hν

theorem signedSqrtCoordinate_integrable_of_continuous {F : Type*} [NormedAddCommGroup F]
    (J : ℤ) (ν : SignedMeasure ℝ) {f : ℝ → F} {L V : ℝ}
    (hf : Continuous f) (hν : ∀ᵐ E ∂ν.variation, E ∈ Icc L V) :
    (signedSqrtCoordinate J ν).Integrable f := by
  let := signedMeasure_isFiniteMeasure_variation (signedSqrtCoordinate J ν)
  exact integrable_of_continuousOn_interval_of_ae_mem hf.continuousOn
    (signedSqrtCoordinate_ae_mem J ν hν)

/-- The original energy integral is the energy observable integrated against
the actual square-root coordinate measure. -/
theorem signedIntegral_energy_sqrtCoordinate_of_continuous {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (J : ℤ) (ν : SignedMeasure ℝ) {f : ℝ → F} {L V : ℝ}
    (hf : Continuous f) (hL : |(J : ℝ)| ≤ L)
    (hν : ∀ᵐ E ∂ν.variation, E ∈ Icc L V) :
    (∫ᵛ x, f (sqrtCoordinateEnergy J x) ∂<•signedSqrtCoordinate J ν) =
      ∫ᵛ E, f E ∂<•ν := by
  calc
    _ = ∫ᵛ E, f (sqrtCoordinateEnergy J (sqrtEnergyCoordinate J E)) ∂<•ν :=
      signedIntegral_sqrtCoordinate_of_continuous J ν
        (f := fun x : ℝ => f (sqrtCoordinateEnergy J x))
        (hf.comp (continuous_sqrtCoordinateEnergy J)) hν
    _ = _ := VectorMeasure.integral_congr_ae (hν.mono fun E hE => congrArg f
      (sqrtCoordinateEnergy_sqrtEnergyCoordinate J (hL.trans hE.1)))

theorem signedSqrtCoordinate_moment (J : ℤ) (ν : SignedMeasure ℝ) {L V : ℝ}
    (hν : ∀ᵐ E ∂ν.variation, E ∈ Icc L V) (k : ℕ) :
    (∫ᵛ x : ℝ, x ^ k ∂<•signedSqrtCoordinate J ν) =
      ∫ᵛ E, Real.sqrt (E - |(J : ℝ)|) ^ k ∂<•ν :=
  signedIntegral_sqrtCoordinate_of_continuous J ν (continuous_id.pow k) hν

@[simp] theorem signedSqrtCoordinate_univ (J : ℤ) (ν : SignedMeasure ℝ) :
    signedSqrtCoordinate J ν univ = ν univ := by
  simp [signedSqrtCoordinate, VectorMeasure.map_apply _
    (continuous_sqrtEnergyCoordinate J).measurable MeasurableSet.univ]

end GapFamily.Analytic
