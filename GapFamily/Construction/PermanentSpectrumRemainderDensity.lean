import GapFamily.Construction.ThermalEnvelope
import GapFamily.Construction.PermanentSpectrumRemainderTail
import GapFamily.Analytic.Cusp.Fourier.CuspFourierProfileCore
import GapFamily.Analytic.Poincare.Poincare

/-! Ordinary all-spin point values of tail densities dominated by the actual
positive thermal envelope. -/

noncomputable section
namespace GapFamily.Construction
open Set Filter MeasureTheory Real UpperHalfPlane
open GapFamily.Analytic
open scoped Topology

/-- The ordinary thermal integral of one actual physical tail density. -/
def tailDensityThermalRow (T t : ℝ) (q : ℤ → ℝ → ℝ) (j : ℤ) : ℝ :=
  ∫ E in Ici (max T |(j : ℝ)|), exp (-t * E) * q j E ∂referenceMeasure j

/-- The actual threshold-height Fourier-Laplace point value, with every spin
and every physical energy integrated ordinarily. -/
def tailDensityPointValue (T : ℝ) (q : ℤ → ℝ → ℝ) (τ : UpperHalfPlane) : ℂ :=
  (sqrt τ.im : ℂ) * ∑' j : ℤ,
    (tailDensityThermalRow T (2 * π * τ.im) q j : ℂ) * cuspFourierMode j τ.re

private theorem thermal_density_norm_le (a T C t : ℝ) (q : ℤ → ℝ → ℝ) (j : ℤ)
    (hq : ∀ᵐ E ∂(referenceMeasure j).restrict (Ici (max T |(j : ℝ)|)),
      |q j E| ≤ C * tailEnvelopeNumerator a E j) :
    ∀ᵐ E ∂(referenceMeasure j).restrict (Ici (max T |(j : ℝ)|)),
      ‖exp (-t * E) * q j E‖ ≤ C * (exp (-t * E) * tailEnvelopeNumerator a E j) := by
  filter_upwards [hq] with E hE
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos _)]
  calc
    _ ≤ exp (-t * E) * (C * tailEnvelopeNumerator a E j) :=
      mul_le_mul_of_nonneg_left hE (exp_nonneg _)
    _ = _ := by ring

/-- Envelope domination proves ordinary row integrability, not merely a bound
on a totalized integral. -/
theorem integrable_tailDensityThermalRow (a T C : ℝ) (q : ℤ → ℝ → ℝ) (j : ℤ)
    (ha : 100 ≤ a) (hT : 1 ≤ T) {t : ℝ} (ht : 0 < t)
    (hm : AEStronglyMeasurable (q j)
      ((referenceMeasure j).restrict (Ici (max T |(j : ℝ)|))))
    (hq : ∀ᵐ E ∂(referenceMeasure j).restrict (Ici (max T |(j : ℝ)|)),
      |q j E| ≤ C * tailEnvelopeNumerator a E j) :
    IntegrableOn (fun E => exp (-t * E) * q j E)
      (Ici (max T |(j : ℝ)|)) (referenceMeasure j) :=
  ((integrable_thermal_tailEnvelopeNumerator a T j ha hT ht).const_mul C).mono'
    (((continuous_const.mul continuous_id).rexp.aestronglyMeasurable).mul hm)
    (thermal_density_norm_le a T C t q j hq)

/-- The signed row's ordinary integral is dominated by the same positive
envelope measure used for all-spin thermal summability. -/
theorem norm_tailDensityThermalRow_le (a T C : ℝ) (q : ℤ → ℝ → ℝ) (j : ℤ)
    (ha : 100 ≤ a) (hT : 1 ≤ T) {t : ℝ} (ht : 0 < t)
    (hq : ∀ᵐ E ∂(referenceMeasure j).restrict (Ici (max T |(j : ℝ)|)),
      |q j E| ≤ C * tailEnvelopeNumerator a E j) :
    ‖tailDensityThermalRow T t q j‖ ≤
      C * ∫ E, exp (-t * E) ∂tailEnvelopeMeasure a T j := by
  rw [integral_tailEnvelopeMeasure a T j (by linarith), ← integral_const_mul]
  exact norm_integral_le_of_norm_le
    ((integrable_thermal_tailEnvelopeNumerator a T j ha hT ht).const_mul C)
    (thermal_density_norm_le a T C t q j hq)

/-- The literal Fourier-Laplace spin series is absolutely summable. -/
theorem summable_norm_tailDensityPointValue_term (a T C : ℝ) (q : ℤ → ℝ → ℝ)
    (ha : 100 ≤ a) (hT : 1 ≤ T)
    (hq : ∀ j : ℤ, ∀ᵐ E ∂(referenceMeasure j).restrict (Ici (max T |(j : ℝ)|)),
      |q j E| ≤ C * tailEnvelopeNumerator a E j) (τ : UpperHalfPlane) :
    Summable (fun j : ℤ =>
      ‖(tailDensityThermalRow T (2 * π * τ.im) q j : ℂ) * cuspFourierMode j τ.re‖) := by
  have ht : 0 < 2 * π * τ.im := by positivity
  apply ((summable_integral_thermal_tailEnvelopeMeasure a T ha hT ht).mul_left C).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro j
  simpa only [norm_mul, norm_cuspFourierMode, mul_one, Complex.norm_real] using
    norm_tailDensityThermalRow_le a T C q j ha hT ht (hq j)

/-- The pointwise ordinary remainder is bounded by the finite all-spin thermal
mass, with exactly the threshold square-root height factor. -/
theorem norm_tailDensityPointValue_le (a T C : ℝ) (q : ℤ → ℝ → ℝ)
    (ha : 100 ≤ a) (hT : 1 ≤ T)
    (hq : ∀ j : ℤ, ∀ᵐ E ∂(referenceMeasure j).restrict (Ici (max T |(j : ℝ)|)),
      |q j E| ≤ C * tailEnvelopeNumerator a E j) (τ : UpperHalfPlane) :
    ‖tailDensityPointValue T q τ‖ ≤ sqrt τ.im * C *
      ∑' j : ℤ, ∫ E, exp (-(2 * π * τ.im) * E) ∂tailEnvelopeMeasure a T j := by
  have ht : 0 < 2 * π * τ.im := by positivity
  have hn := summable_norm_tailDensityPointValue_term a T C q ha hT hq τ
  rw [tailDensityPointValue, norm_mul, Complex.norm_of_nonneg (sqrt_nonneg _)]
  calc
    _ ≤ sqrt τ.im * ∑' j : ℤ,
        ‖(tailDensityThermalRow T (2 * π * τ.im) q j : ℂ) * cuspFourierMode j τ.re‖ :=
      mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hn) (sqrt_nonneg _)
    _ ≤ sqrt τ.im * ∑' j : ℤ,
        C * ∫ E, exp (-(2 * π * τ.im) * E) ∂tailEnvelopeMeasure a T j := by
      apply mul_le_mul_of_nonneg_left _ (sqrt_nonneg _)
      apply hn.tsum_le_tsum _
        ((summable_integral_thermal_tailEnvelopeMeasure a T ha hT ht).mul_left C)
      intro j
      simpa only [norm_mul, norm_cuspFourierMode, mul_one, Complex.norm_real] using
        norm_tailDensityThermalRow_le a T C q j ha hT ht (hq j)
    _ = _ := by rw [tsum_mul_left]; exact (mul_assoc _ _ _).symm

/-- The envelope cutoff remains its literal physical density integral. -/
theorem integral_restrict_Ici_tailEnvelopeMeasure
    (a T R : ℝ) (j : ℤ) (ha : 2 ≤ a) (f : ℝ → ℝ) :
    (∫ E in Ici R, f E ∂tailEnvelopeMeasure a T j) =
      ∫ E in Ici (max R (max T |(j : ℝ)|)),
        f E * tailEnvelopeNumerator a E j ∂referenceMeasure j := by
  rw [tailEnvelopeMeasure, restrict_withDensity measurableSet_Ici,
    Measure.restrict_restrict measurableSet_Ici, Ici_inter_Ici,
    integral_withDensity_eq_integral_toReal_smul
      (measurable_tailEnvelopeNumerator a j).ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ici] with E hE
  rw [ENNReal.toReal_ofReal (tailEnvelopeNumerator_nonneg a E j ha
    ((le_max_right T |(j : ℝ)|).trans ((le_max_right R _).trans hE))),
    smul_eq_mul, mul_comm]

/-- A density vanishing below the moving cutoff has exactly the same ordinary
thermal integral after restricting to that cutoff. -/
theorem integral_thermal_density_Ici_cutoff
    (j : ℤ) (A R t : ℝ) (q : ℝ → ℝ)
    (hq : ∀ᵐ E ∂(referenceMeasure j).restrict (Ici A), E < R → q E = 0) :
    (∫ E in Ici A, exp (-t * E) * q E ∂referenceMeasure j) =
      ∫ E in Ici (max R A), exp (-t * E) * q E ∂referenceMeasure j := by
  calc
    _ = ∫ E in Ici A, (Ici R).indicator (fun E => exp (-t * E) * q E) E
        ∂referenceMeasure j := by
      apply integral_congr_ae
      filter_upwards [hq] with E hE
      by_cases hER : R ≤ E
      · rw [Set.indicator_of_mem (show E ∈ Ici R from hER)]
      · rw [Set.indicator_of_notMem (show E ∉ Ici R from hER),
          hE (lt_of_not_ge hER), mul_zero]
    _ = _ := by
      rw [integral_indicator measurableSet_Ici,
        Measure.restrict_restrict measurableSet_Ici, Ici_inter_Ici]

/-- The row bound retains the moving energy cutoff rather than replacing it
by the full envelope. -/
theorem norm_tailDensityThermalRow_le_cutoff (a T C R : ℝ) (q : ℤ → ℝ → ℝ) (j : ℤ)
    (ha : 100 ≤ a) (hT : 1 ≤ T) {t : ℝ} (ht : 0 < t)
    (hq : ∀ᵐ E ∂(referenceMeasure j).restrict (Ici (max T |(j : ℝ)|)),
      |q j E| ≤ C * tailEnvelopeNumerator a E j)
    (hz : ∀ᵐ E ∂(referenceMeasure j).restrict (Ici (max T |(j : ℝ)|)),
      E < R → q j E = 0) :
    ‖tailDensityThermalRow T t q j‖ ≤
      C * ∫ E in Ici R, exp (-t * E) ∂tailEnvelopeMeasure a T j := by
  rw [tailDensityThermalRow, integral_thermal_density_Ici_cutoff j _ R t _ hz,
    integral_restrict_Ici_tailEnvelopeMeasure a T R j (by linarith), ← integral_const_mul]
  have hsub : Ici (max R (max T |(j : ℝ)|)) ⊆ Ici (max T |(j : ℝ)|) := by
    intro E hE
    exact (le_max_right R (max T |(j : ℝ)|)).trans (show max R (max T |(j : ℝ)|) ≤ E from hE)
  exact norm_integral_le_of_norm_le
    ((IntegrableOn.mono_set (integrable_thermal_tailEnvelopeNumerator a T j ha hT ht) hsub).const_mul C)
    (ae_restrict_of_ae_restrict_of_subset hsub (thermal_density_norm_le a T C t q j hq))

/-- The actual all-spin ordinary point remainder keeps the full strength of
the vanishing thermal envelope tail. -/
theorem norm_tailDensityPointValue_le_cutoff (a T C R : ℝ) (q : ℤ → ℝ → ℝ)
    (ha : 100 ≤ a) (hT : 1 ≤ T)
    (hq : ∀ j : ℤ, ∀ᵐ E ∂(referenceMeasure j).restrict (Ici (max T |(j : ℝ)|)),
      |q j E| ≤ C * tailEnvelopeNumerator a E j)
    (hz : ∀ j : ℤ, ∀ᵐ E ∂(referenceMeasure j).restrict (Ici (max T |(j : ℝ)|)),
      E < R → q j E = 0) (τ : UpperHalfPlane) :
    ‖tailDensityPointValue T q τ‖ ≤
      sqrt τ.im * C * tailEnvelopeThermalTail a T (2 * π * τ.im) R := by
  have ht : 0 < 2 * π * τ.im := by positivity
  have hn := summable_norm_tailDensityPointValue_term a T C q ha hT hq τ
  rw [tailDensityPointValue, norm_mul, Complex.norm_of_nonneg (sqrt_nonneg _)]
  calc
    _ ≤ sqrt τ.im * ∑' j : ℤ,
        ‖(tailDensityThermalRow T (2 * π * τ.im) q j : ℂ) * cuspFourierMode j τ.re‖ :=
      mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hn) (sqrt_nonneg _)
    _ ≤ sqrt τ.im * ∑' j : ℤ,
        C * ∫ E in Ici R, exp (-(2 * π * τ.im) * E) ∂tailEnvelopeMeasure a T j := by
      apply mul_le_mul_of_nonneg_left _ (sqrt_nonneg _)
      apply hn.tsum_le_tsum _
        ((summable_integral_thermal_tailEnvelopeMeasure_cutoff a T R ha hT ht).mul_left C)
      intro j
      simpa only [norm_mul, norm_cuspFourierMode, mul_one, Complex.norm_real] using
        norm_tailDensityThermalRow_le_cutoff a T C R q j ha hT ht (hq j) (hz j)
    _ = _ := by rw [tsum_mul_left]; exact (mul_assoc _ _ _).symm

/-- A uniformly envelope-bounded sequence whose ordinary density retreats to
infinite energy has zero pointwise all-spin remainder. -/
theorem tendsto_tailDensityPointValue_of_cutoff (a T C : ℝ)
    (q : ℕ → ℤ → ℝ → ℝ) (R : ℕ → ℝ)
    (ha : 100 ≤ a) (hT : 1 ≤ T) (hR : Tendsto R atTop atTop)
    (hq : ∀ n : ℕ, ∀ j : ℤ,
      ∀ᵐ E ∂(referenceMeasure j).restrict (Ici (max T |(j : ℝ)|)),
        |q n j E| ≤ C * tailEnvelopeNumerator a E j)
    (hz : ∀ n : ℕ, ∀ j : ℤ,
      ∀ᵐ E ∂(referenceMeasure j).restrict (Ici (max T |(j : ℝ)|)),
        E < R n → q n j E = 0) (τ : UpperHalfPlane) :
    Tendsto (fun n => tailDensityPointValue T (q n) τ) atTop (𝓝 0) := by
  have ht : 0 < 2 * π * τ.im := by positivity
  have htail : Tendsto (fun n => sqrt τ.im * C *
      tailEnvelopeThermalTail a T (2 * π * τ.im) (R n)) atTop (𝓝 0) := by
    simpa using ((tendsto_tailEnvelopeThermalTail a T ha hT ht).comp hR).const_mul
      (sqrt τ.im * C)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [sub_zero]
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun n => norm_tailDensityPointValue_le_cutoff a T C (R n) (q n) ha hT (hq n) (hz n) τ)
    htail

end GapFamily.Construction
