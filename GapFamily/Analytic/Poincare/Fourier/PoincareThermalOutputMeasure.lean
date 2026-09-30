import GapFamily.Analytic.Kernel.CorrectedKernelCompactInput
import GapFamily.Analytic.Kernel.FullKernelSmoothingSignedMeasure
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec

/-! The literal finite thermal signed output of one compact physical input row.
The direct input is tilted as a signed measure. The induced output is an
ordinary density against the open physical reference measure, while the scalar
threshold is an actual separate Dirac measure.
-/
noncomputable section
namespace GapFamily.Analytic

open MeasureTheory Set
open scoped Classical BigOperators

/-- A positive thermal tilt is integrable against every finite physical input. -/
theorem signedIntegrable_thermalInput (ν : SignedMeasure ℝ) (J : ℤ) (B : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ B) {t : ℝ} (ht : 0 < t) :
    ν.Integrable (fun E => Real.exp (-t * E)) := by
  let := signedMeasure_isFiniteMeasure_variation ν
  apply (integrable_const (1 : ℝ) (μ := ν.variation)).mono'
    (by fun_prop)
  filter_upwards [hs] with E hE
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht.le)
    ((abs_nonneg (J : ℝ)).trans hE.1)

/-- The original signed input with its actual positive thermal weight. -/
def thermalSignedInputMeasure (ν : SignedMeasure ℝ) (t : ℝ) : SignedMeasure ℝ :=
  ν.withDensity (fun E => Real.exp (-t * E))
    (ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)).flip

theorem thermalSignedInputMeasure_apply (ν : SignedMeasure ℝ) (J : ℤ) (B : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ B) {t : ℝ} (ht : 0 < t)
    (s : Set ℝ) :
    thermalSignedInputMeasure ν t s = ∫ᵛ E in s, Real.exp (-t * E) ∂<•ν :=
  VectorMeasure.withDensity_apply (signedIntegrable_thermalInput ν J B hs ht)

theorem thermalSignedInputMeasure_univ (ν : SignedMeasure ℝ) (t : ℝ) :
    thermalSignedInputMeasure ν t univ = ∫ᵛ E, Real.exp (-t * E) ∂<•ν :=
  VectorMeasure.withDensity_apply_univ

/-- Direct atoms retain their original location and acquire precisely the thermal weight. -/
theorem thermalSignedInputMeasure_singleton (ν : SignedMeasure ℝ) (J : ℤ) (B : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ B) {t : ℝ} (ht : 0 < t)
    (e : ℝ) :
    thermalSignedInputMeasure ν t {e} = Real.exp (-t * e) * ν {e} := by
  rw [thermalSignedInputMeasure_apply ν J B hs ht, VectorMeasure.integral_singleton]
  simp [smul_eq_mul, mul_comm]

/-- The real thermal density of the genuine corrected signed response. -/
def correctedThermalRowDensity (ν : SignedMeasure ℝ) (J j : ℤ) (t e : ℝ) : ℝ :=
  Real.exp (-t * e) * (correctedSignedRowResponse ν J j e).re

/-- Compact physical input makes the literal thermal output an ordinary L1 density. -/
theorem integrable_correctedThermalRowDensity (ν : SignedMeasure ℝ) (J j : ℤ) (B : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ B) {t : ℝ} (ht : 0 < t) :
    Integrable (correctedThermalRowDensity ν J j t) (referenceMeasure j) := by
  change Integrable (fun e : ℝ => Real.exp (-t * e) *
    (correctedSignedRowResponse ν J j e).re) (referenceMeasure j)
  have hi := (integrable_thermal_correctedSignedRowResponse ν J j B hs ht).re
  change Integrable (fun e : ℝ =>
    (Complex.exp (-(t : ℂ) * (e : ℂ)) * correctedSignedRowResponse ν J j e).re)
    (referenceMeasure j) at hi
  simpa only [← Complex.ofReal_neg, ← Complex.ofReal_mul,
    ← Complex.ofReal_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] using hi

/-- The ordinary induced measure is constructed from the actual real density. -/
def correctedThermalContinuumMeasure (ν : SignedMeasure ℝ) (J j : ℤ) (t : ℝ) :
    SignedMeasure ℝ :=
  (referenceMeasure j).withDensityᵥ (correctedThermalRowDensity ν J j t)

theorem correctedThermalContinuumMeasure_apply (ν : SignedMeasure ℝ) (J j : ℤ) (B : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ B) {t : ℝ} (ht : 0 < t)
    (s : Set ℝ) (hset : MeasurableSet s) :
    correctedThermalContinuumMeasure ν J j t s =
      ∫ e in s, correctedThermalRowDensity ν J j t e ∂referenceMeasure j :=
  withDensityᵥ_apply (integrable_correctedThermalRowDensity ν J j B hs ht) hset

/-- Induced output has neither scalar-threshold atoms nor nonzero-edge atoms. -/
theorem correctedThermalContinuumMeasure_singleton (ν : SignedMeasure ℝ) (J j : ℤ) (B : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ B) {t : ℝ} (ht : 0 < t) (e : ℝ) :
    correctedThermalContinuumMeasure ν J j t {e} = 0 := by
  rw [correctedThermalContinuumMeasure_apply ν J j B hs ht _ (measurableSet_singleton e)]
  simp

/-- Total variation is the ordinary absolute thermal kernel mass. -/
theorem correctedThermalContinuumMeasure_totalVariation
    (ν : SignedMeasure ℝ) (J j : ℤ) (B : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ B) {t : ℝ} (ht : 0 < t) :
    (correctedThermalContinuumMeasure ν J j t).variation.real univ =
      ∫ e : ℝ, ‖Complex.exp (-(t : ℂ) * (e : ℂ)) *
        correctedSignedRowResponse ν J j e‖ ∂referenceMeasure j := by
  have hi := integrable_correctedThermalRowDensity ν J j B hs ht
  rw [Measure.real, correctedThermalContinuumMeasure, Measure.variation_withDensityᵥ hi,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← integral_norm_eq_lintegral_enorm hi.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards with e
  have hr : ((correctedSignedRowResponse ν J j e).re : ℂ) =
      correctedSignedRowResponse ν J j e := by
    apply Complex.ext
    · rfl
    · simp only [Complex.ofReal_im, correctedSignedRowResponse_im ν J j B hs e]
  rw [← Complex.norm_real, correctedThermalRowDensity, Complex.ofReal_mul, hr]
  simp only [Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg]

/-- The continuum is a finite thermal measure after summing every output spin. -/
theorem summable_correctedThermalContinuumMeasure_totalVariation
    (ν : SignedMeasure ℝ) (J : ℤ) (B : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ B) {t : ℝ} (ht : 0 < t) :
    Summable (fun j : ℤ =>
      (correctedThermalContinuumMeasure ν J j t).variation.real univ) := by
  simpa only [correctedThermalContinuumMeasure_totalVariation ν J _ B hs ht] using
    summable_integral_norm_thermal_correctedSignedRowResponse ν J B hs ht

/-- The complete output in one spin: tilted direct input, ordinary continuum,
and the separately tracked scalar threshold atom. -/
def correctedThermalRowOutputMeasure (ν : SignedMeasure ℝ) (J j : ℤ) (t : ℝ) :
    SignedMeasure ℝ :=
  (if j = J then thermalSignedInputMeasure ν t else 0) +
    correctedThermalContinuumMeasure ν J j t +
      (if j = 0 then VectorMeasure.dirac (0 : ℝ)
        ((PoincareScalarFourier.scalarThresholdCoefficient J).re * ν univ) else 0)

/-- Exact ordinary measure identity on every measurable output set. -/
theorem correctedThermalRowOutputMeasure_apply (ν : SignedMeasure ℝ) (J j : ℤ) (B : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ B) {t : ℝ} (ht : 0 < t)
    (s : Set ℝ) (hset : MeasurableSet s) :
    correctedThermalRowOutputMeasure ν J j t s =
      (if j = J then ∫ᵛ E in s, Real.exp (-t * E) ∂<•ν else 0) +
      (∫ e in s, correctedThermalRowDensity ν J j t e ∂referenceMeasure j) +
      (if j = 0 ∧ (0 : ℝ) ∈ s then
        (PoincareScalarFourier.scalarThresholdCoefficient J).re * ν univ else 0) := by
  unfold correctedThermalRowOutputMeasure
  rw [_root_.add_apply, _root_.add_apply,
    correctedThermalContinuumMeasure_apply ν J j B hs ht s hset]
  congr 1
  · congr 1
    by_cases hj : j = J
    · rw [ite_eq_left hj, ite_eq_left hj]
      exact thermalSignedInputMeasure_apply ν J B hs ht s
    · simp only [ite_eq_right hj, _root_.zero_apply]
  · by_cases h0 : j = 0
    · rw [ite_eq_left h0]
      by_cases hs0 : (0 : ℝ) ∈ s
      · rw [VectorMeasure.dirac_apply_of_mem hset hs0, ite_eq_left ⟨h0, hs0⟩]
      · rw [VectorMeasure.dirac_apply_of_notMem hs0, ite_eq_right (by simp [hs0])]
    · simp only [_root_.zero_apply, h0, false_and, ite_false]

/-- Total thermal mass is the sum of the three corresponding ordinary integrals. -/
theorem correctedThermalRowOutputMeasure_univ (ν : SignedMeasure ℝ) (J j : ℤ) (B : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ B) {t : ℝ} (ht : 0 < t) :
    correctedThermalRowOutputMeasure ν J j t univ =
      (if j = J then ∫ᵛ E, Real.exp (-t * E) ∂<•ν else 0) +
      (∫ e, Real.exp (-t * e) * (correctedSignedRowResponse ν J j e).re ∂referenceMeasure j) +
      (if j = 0 then (PoincareScalarFourier.scalarThresholdCoefficient J).re * ν univ else 0) := by
  simpa only [correctedThermalRowDensity, VectorMeasure.restrict_univ, Measure.restrict_univ,
    mem_univ, and_true] using
    correctedThermalRowOutputMeasure_apply ν J j B hs ht univ MeasurableSet.univ

/-- Every atom is a direct input atom or the explicitly specified scalar threshold atom. -/
theorem correctedThermalRowOutputMeasure_singleton (ν : SignedMeasure ℝ) (J j : ℤ) (B : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ B) {t : ℝ} (ht : 0 < t) (e : ℝ) :
    correctedThermalRowOutputMeasure ν J j t {e} =
      (if j = J then Real.exp (-t * e) * ν {e} else 0) +
      (if j = 0 ∧ e = 0 then
        (PoincareScalarFourier.scalarThresholdCoefficient J).re * ν univ else 0) := by
  rw [correctedThermalRowOutputMeasure_apply ν J j B hs ht _ (measurableSet_singleton e)]
  simp [smul_eq_mul, mul_comm, eq_comm]

/-- Direct and threshold masses change only two spins, so the actual complete
output has finite thermal total variation over all spins. -/
theorem summable_correctedThermalRowOutputMeasure_totalVariation
    (ν : SignedMeasure ℝ) (J : ℤ) (B : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ B) {t : ℝ} (ht : 0 < t) :
    Summable (fun j : ℤ =>
      (correctedThermalRowOutputMeasure ν J j t).variation.real univ) := by
  apply (summable_correctedThermalContinuumMeasure_totalVariation ν J B hs ht).congr_cofinite
  filter_upwards [Filter.eventually_cofinite_ne J,
    Filter.eventually_cofinite_ne (0 : ℤ)] with j hj h0
  simp only [correctedThermalRowOutputMeasure, hj, h0, ite_false, zero_add, add_zero]

/-- The actual output of finitely many compact physical input spin rows. -/
def correctedThermalFiniteOutputMeasure (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ)
    (j : ℤ) (t : ℝ) : SignedMeasure ℝ :=
  ∑ J ∈ S, correctedThermalRowOutputMeasure (ν J) J j t

theorem correctedThermalFiniteOutputMeasure_apply (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ)
    (j : ℤ) (t : ℝ) (s : Set ℝ) :
    correctedThermalFiniteOutputMeasure S ν j t s =
      ∑ J ∈ S, correctedThermalRowOutputMeasure (ν J) J j t s := by
  simp [correctedThermalFiniteOutputMeasure]

/-- Finite signed superposition preserves the literal direct, continuum and
threshold thermal masses. -/
theorem correctedThermalFiniteOutputMeasure_univ (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ)
    (j : ℤ) (B : ℝ)
    (hs : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ B)
    {t : ℝ} (ht : 0 < t) :
    correctedThermalFiniteOutputMeasure S ν j t univ =
      ∑ J ∈ S,
        ((if j = J then ∫ᵛ E, Real.exp (-t * E) ∂<•(ν J) else 0) +
        (∫ e, Real.exp (-t * e) * (correctedSignedRowResponse (ν J) J j e).re
          ∂referenceMeasure j) +
        (if j = 0 then
          (PoincareScalarFourier.scalarThresholdCoefficient J).re * ν J univ else 0)) := by
  rw [correctedThermalFiniteOutputMeasure_apply]
  apply Finset.sum_congr rfl
  intro J hJ
  exact correctedThermalRowOutputMeasure_univ (ν J) J j B (hs J hJ) ht

/-- The finite output has summable total variation across the entire spin lattice. -/
theorem summable_correctedThermalFiniteOutputMeasure_totalVariation
    (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ) (B : ℝ)
    (hs : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ B)
    {t : ℝ} (ht : 0 < t) :
    Summable (fun j : ℤ =>
      (correctedThermalFiniteOutputMeasure S ν j t).variation.real univ) := by
  have hm := summable_sum (s := S) (fun J hJ =>
    summable_correctedThermalRowOutputMeasure_totalVariation (ν J) J B (hs J hJ) ht)
  apply hm.of_nonneg_of_le (fun _ => ENNReal.toReal_nonneg)
  intro j
  let μ : ℤ → SignedMeasure ℝ := fun J => correctedThermalRowOutputMeasure (ν J) J j t
  have hfinite (J : ℤ) : (μ J).variation univ ≠ ⊤ := by
    let := signedMeasure_isFiniteMeasure_variation (μ J)
    exact measure_ne_top _ _
  have hle := (VectorMeasure.variation_finsetSum_le S μ) univ
  rw [Measure.finsetSum_apply] at hle
  have hreal := ENNReal.toReal_mono
    (ENNReal.sum_ne_top.mpr (fun J _ => hfinite J)) hle
  simpa only [correctedThermalFiniteOutputMeasure, μ, Measure.real,
    ENNReal.toReal_sum (fun J _ => hfinite J)] using hreal

end GapFamily.Analytic
