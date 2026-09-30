import GapFamily.Construction.ThermalEnvelopeBound
import GapFamily.Construction.TailCellReference
import GapFamily.Analytic.Kernel.HigherKernelThermalSpin

/-!
# The positive physical tail envelope

This is the ordinary positive measure controlling every unprocessed tail row.
Its thermal mass is finite after summing over all integer spins.
-/

noncomputable section

open Set MeasureTheory Real
open scoped ENNReal
open GapFamily.Analytic

namespace GapFamily.Construction

/-- The C10 envelope is restricted above both the tail cutoff and the physical
spin threshold, and uses the actual reference measure. -/
def tailEnvelopeMeasure (a T : ℝ) (j : ℤ) : Measure ℝ :=
  ((referenceMeasure j).restrict (Ici (max T |(j : ℝ)|))).withDensity
    (fun E => ENNReal.ofReal (tailEnvelopeNumerator a E j))

instance instNullSingletonClassTailEnvelopeMeasure (a T : ℝ) (j : ℤ) :
    NullSingletonClass (tailEnvelopeMeasure a T j) := by
  unfold tailEnvelopeMeasure
  infer_instance

@[simp] theorem tailEnvelopeMeasure_singleton (a T : ℝ) (j : ℤ) (E : ℝ) :
    tailEnvelopeMeasure a T j {E} = 0 := measure_singleton E

/-- Ordinary envelope integration is exactly its physical numerator integral. -/
theorem integral_tailEnvelopeMeasure (a T : ℝ) (j : ℤ) (ha : 2 ≤ a)
    (f : ℝ → ℝ) :
    (∫ E, f E ∂tailEnvelopeMeasure a T j) =
      ∫ E in Ici (max T |(j : ℝ)|),
        f E * tailEnvelopeNumerator a E j ∂referenceMeasure j := by
  rw [tailEnvelopeMeasure, integral_withDensity_eq_integral_toReal_smul
    (measurable_tailEnvelopeNumerator a j).ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ici] with E hE
  rw [ENNReal.toReal_ofReal (tailEnvelopeNumerator_nonneg a E j ha
    ((le_max_right T |(j : ℝ)|).trans hE)), smul_eq_mul, mul_comm]

/-- Above its cutoff, the envelope restriction is the literal numerator
density on the physical cell. -/
theorem tailEnvelopeMeasure_restrict_Ioo (a T : ℝ) (j : ℤ) {L V : ℝ}
    (hT : T ≤ L) (hj : |(j : ℝ)| ≤ L) :
    (tailEnvelopeMeasure a T j).restrict (Ioo L V) =
      ((referenceMeasure j).restrict (Ioo L V)).withDensity
        (fun E => ENNReal.ofReal (tailEnvelopeNumerator a E j)) := by
  rw [tailEnvelopeMeasure, restrict_withDensity measurableSet_Ioo,
    Measure.restrict_restrict measurableSet_Ioo]
  congr 2
  apply inter_eq_left.mpr
  intro E hE
  exact (max_le hT hj).trans hE.1.le

/-- The exact local density formula used in weighted cell estimates. -/
theorem integral_restrict_tailEnvelopeMeasure (a T : ℝ) (j : ℤ) (ha : 2 ≤ a)
    {L V : ℝ} (hT : T ≤ L) (hj : |(j : ℝ)| ≤ L) (f : ℝ → ℝ) :
    (∫ E in Ioo L V, f E ∂tailEnvelopeMeasure a T j) =
      ∫ E in Ioo L V, f E * tailEnvelopeNumerator a E j ∂referenceMeasure j := by
  rw [tailEnvelopeMeasure_restrict_Ioo a T j hT hj,
    integral_withDensity_eq_integral_toReal_smul
      (measurable_tailEnvelopeNumerator a j).ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with E hE
  rw [ENNReal.toReal_ofReal (tailEnvelopeNumerator_nonneg a E j ha (hj.trans hE.1.le)),
    smul_eq_mul, mul_comm]

/-- Its local ordinary mass is the numerator integral on the same physical cell. -/
theorem tailEnvelopeMeasure_real_Ioo (a T : ℝ) (j : ℤ) (ha : 2 ≤ a)
    {L V : ℝ} (hT : T ≤ L) (hj : |(j : ℝ)| ≤ L) :
    (tailEnvelopeMeasure a T j).real (Ioo L V) =
      ∫ E in Ioo L V, tailEnvelopeNumerator a E j ∂referenceMeasure j := by
  simpa only [setIntegral_const, smul_eq_mul, mul_one, one_mul] using
    integral_restrict_tailEnvelopeMeasure a T j ha hT hj (fun _ => 1)

/-- The actual numerator is ordinarily integrable on every bounded physical
cell above energy one, including a cell opening at its spin threshold. -/
theorem integrableOn_tailEnvelopeNumerator (a : ℝ) (j : ℤ) {L V : ℝ}
    (hL : 1 ≤ L) (hj : |(j : ℝ)| ≤ L) (hLV : L ≤ V) :
    IntegrableOn (fun E => tailEnvelopeNumerator a E j) (Ioo L V) (referenceMeasure j) := by
  let _ := tailCell_reference_isFiniteMeasure j hL hj hLV
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuous_tailEnvelopeNumerator a j).continuousOn
  apply Integrable.of_bound (C := C) (measurable_tailEnvelopeNumerator a j).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with E hE
  exact hC E ⟨hE.1.le, hE.2.le⟩

/-- Every bounded physical cell above energy one carries finite envelope mass. -/
theorem tailEnvelopeMeasure_isFiniteMeasure_restrict (a T : ℝ) (j : ℤ)
    (ha : 2 ≤ a) {L V : ℝ} (hL : 1 ≤ L) (hT : T ≤ L)
    (hj : |(j : ℝ)| ≤ L) (hLV : L ≤ V) :
    IsFiniteMeasure ((tailEnvelopeMeasure a T j).restrict (Ioo L V)) := by
  rw [tailEnvelopeMeasure_restrict_Ioo a T j hT hj]
  apply isFiniteMeasure_withDensity
  apply (lintegral_ofReal_ne_top_iff_integrable
    (measurable_tailEnvelopeNumerator a j).aestronglyMeasurable ?_).mpr
  · exact integrableOn_tailEnvelopeNumerator a j hL hj hLV
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with E hE
    exact tailEnvelopeNumerator_nonneg a E j ha (hj.trans hE.1.le)

/-- The thermal numerator has an ordinary convergent integral on its actual
tail support. -/
theorem integrable_thermal_tailEnvelopeNumerator (a T : ℝ) (j : ℤ)
    (ha : 100 ≤ a) (hT : 1 ≤ T) {t : ℝ} (ht : 0 < t) :
    Integrable (fun E => exp (-t * E) * tailEnvelopeNumerator a E j)
      ((referenceMeasure j).restrict (Ici (max T |(j : ℝ)|))) := by
  apply ((integrable_energy_exp_sqrt_referenceMeasure j (4 * π * sqrt a) ht).const_mul 3).integrableOn.mono'
  · exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.mul
      (measurable_tailEnvelopeNumerator a j)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ici] with E hE
    have hjE : |(j : ℝ)| ≤ E := (le_max_right T _).trans hE
    have hE1 : 1 ≤ E := hT.trans ((le_max_left T _).trans hE)
    rw [Real.norm_of_nonneg (mul_nonneg (exp_nonneg _)
      (tailEnvelopeNumerator_nonneg a E j (by linarith) hjE))]
    exact thermal_tailEnvelopeNumerator_le a E t j ha hE1 hjE

/-- Every positive thermal weight is integrable against the ordinary positive
tail envelope measure. -/
theorem integrable_thermal_tailEnvelopeMeasure (a T : ℝ) (j : ℤ)
    (ha : 100 ≤ a) (hT : 1 ≤ T) {t : ℝ} (ht : 0 < t) :
    Integrable (fun E => exp (-t * E)) (tailEnvelopeMeasure a T j) := by
  rw [tailEnvelopeMeasure, integrable_withDensity_iff_integrable_smul'
    (measurable_tailEnvelopeNumerator a j).ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply (integrable_thermal_tailEnvelopeNumerator a T j ha hT ht).congr
  filter_upwards [ae_restrict_mem measurableSet_Ici] with E hE
  rw [ENNReal.toReal_ofReal (tailEnvelopeNumerator_nonneg a E j (by linarith)
    ((le_max_right T _).trans hE)), smul_eq_mul, mul_comm]

/-- A uniform all-spin majorant for the ordinary thermal envelope mass. -/
theorem integral_thermal_tailEnvelopeMeasure_le (a T : ℝ) (j : ℤ)
    (ha : 100 ≤ a) (hT : 1 ≤ T) {t : ℝ} (ht : 0 < t) :
    (∫ E, exp (-t * E) ∂tailEnvelopeMeasure a T j) ≤
      3 * ∫ E, E * exp ((4 * π * sqrt a) * sqrt E - t * E) ∂referenceMeasure j := by
  rw [integral_tailEnvelopeMeasure a T j (by linarith)]
  calc
    _ ≤ ∫ E in Ici (max T |(j : ℝ)|),
        3 * (E * exp ((4 * π * sqrt a) * sqrt E - t * E)) ∂referenceMeasure j := by
      apply integral_mono_ae (integrable_thermal_tailEnvelopeNumerator a T j ha hT ht)
        ((integrable_energy_exp_sqrt_referenceMeasure j (4 * π * sqrt a) ht).const_mul 3).integrableOn
      filter_upwards [ae_restrict_mem measurableSet_Ici] with E hE
      exact thermal_tailEnvelopeNumerator_le a E t j ha
        (hT.trans ((le_max_left T _).trans hE)) ((le_max_right T _).trans hE)
    _ ≤ ∫ E, 3 * (E * exp ((4 * π * sqrt a) * sqrt E - t * E)) ∂referenceMeasure j := by
      apply setIntegral_le_integral
        ((integrable_energy_exp_sqrt_referenceMeasure j (4 * π * sqrt a) ht).const_mul 3)
      filter_upwards [referenceMeasure_ae_above_edge j] with E hE
      exact mul_nonneg (by norm_num) (mul_nonneg ((abs_nonneg _).trans hE.le) (exp_nonneg _))
    _ = _ := integral_const_mul _ _

/-- The ordinary positive envelope has finite thermal mass after summing
every integer spin, for every positive inverse temperature. -/
theorem summable_integral_thermal_tailEnvelopeMeasure (a T : ℝ)
    (ha : 100 ≤ a) (hT : 1 ≤ T) {t : ℝ} (ht : 0 < t) :
    Summable (fun j : ℤ => ∫ E, exp (-t * E) ∂tailEnvelopeMeasure a T j) := by
  apply ((summable_integral_energy_exp_sqrt_referenceMeasure
    (4 * π * sqrt a) ht).mul_left 3).of_nonneg_of_le
  · intro j
    exact integral_nonneg (fun E => exp_nonneg _)
  · intro j
    exact integral_thermal_tailEnvelopeMeasure_le a T j ha hT ht

/-- Equivalent extended-nonnegative formulation: the total all-spin thermal
mass is finite as an actual sum of positive measure integrals. -/
theorem tsum_lintegral_thermal_tailEnvelopeMeasure_lt_top (a T : ℝ)
    (ha : 100 ≤ a) (hT : 1 ≤ T) {t : ℝ} (ht : 0 < t) :
    (∑' j : ℤ, ∫⁻ E, ENNReal.ofReal (exp (-t * E))
      ∂tailEnvelopeMeasure a T j) < ∞ := by
  have heq : ∀ j : ℤ, (∫⁻ E, ENNReal.ofReal (exp (-t * E))
      ∂tailEnvelopeMeasure a T j) =
      ENNReal.ofReal (∫ E, exp (-t * E) ∂tailEnvelopeMeasure a T j) := by
    intro j
    exact (ofReal_integral_eq_lintegral_ofReal
      (integrable_thermal_tailEnvelopeMeasure a T j ha hT ht)
      (Filter.Eventually.of_forall fun E => exp_nonneg _)).symm
  simp_rw [heq]
  exact (summable_integral_thermal_tailEnvelopeMeasure a T ha hT ht).tsum_ofReal_lt_top

end GapFamily.Construction
