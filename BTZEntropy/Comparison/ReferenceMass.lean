import GapFamily.Construction.ThermalEnvelopeBound
import GapFamily.Analytic.Kernel.HigherKernelSmoothing
import Mathlib.Data.Int.Interval

/-!
# Finite-energy mass of the actual integer-spin leading reference

The bound keeps the exact exponential rate `4 * π * sqrt (a * X)`.
The spin-edge singularity is integrated with the exact first energy moment
of the physical reference measure. No pointwise bound on that singularity
and no additional exponential factor are introduced.
-/

noncomputable section

open MeasureTheory Set Real
open GapFamily.Analytic GapFamily.Construction
open scoped BigOperators

namespace BTZEntropy.Comparison

/-- The leading primary mass in one actual integer-spin row above a fixed cutoff. -/
def leadingRowMass (a T X : ℝ) (j : ℤ) : ℝ :=
  ∫ E in Ioo (max T |(j : ℝ)|) X, vacuumLeading a E j ∂referenceMeasure j

/-- The total leading primary mass includes every integer spin. -/
def leadingMass (a T X : ℝ) : ℝ := ∑' j : ℤ, leadingRowMass a T X j

private theorem continuous_leadingRow (a : ℝ) (j : ℤ) :
    Continuous (fun E => vacuumLeading a E j) := by
  have he : Continuous (fun E : ℝ => exp (7 * sqrt (a * E))) := by fun_prop
  have h := (continuous_tailEnvelopeNumerator a j).sub he
  convert h using 1
  ext E
  simp [tailEnvelopeNumerator]

/-- The sharp numerator bound is uniform throughout a bounded physical band. -/
theorem vacuumLeading_le_energy_envelope {a T X E : ℝ} (j : ℤ)
    (ha : 2 ≤ a) (hT : 1 ≤ T) (hE : E ∈ Ioo (max T |(j : ℝ)|) X) :
    vacuumLeading a E j ≤ (2 * exp (4 * π * sqrt (a * X))) * E := by
  have hE1 : 1 ≤ E := hT.trans ((le_max_left _ _).trans hE.1.le)
  have hj : |(j : ℝ)| ≤ E := (le_max_right _ _).trans hE.1.le
  calc
    _ ≤ 2 * exp (4 * π * sqrt (a * E)) := vacuumLeading_le_exp a E j ha hj
    _ ≤ 2 * exp (4 * π * sqrt (a * X)) := by
      gcongr
      exact hE.2.le
    _ ≤ _ := by nlinarith [exp_pos (4 * π * sqrt (a * X))]

/-- Ordinary integrability covers scalar spin and every opening spin edge. -/
theorem integrable_leadingRow {a T X : ℝ} (j : ℤ) (ha : 2 ≤ a) (hT : 1 ≤ T) :
    IntegrableOn (fun E => vacuumLeading a E j)
      (Ioo (max T |(j : ℝ)|) X) (referenceMeasure j) := by
  have hi := (show IntegrableOn (fun E : ℝ => E) (Ioo |(j : ℝ)| X)
    (referenceMeasure j) from lowBand_energy_integrable j X).mono_set
    (Ioo_subset_Ioo_left (le_max_right T |(j : ℝ)|))
  apply (hi.const_mul (2 * exp (4 * π * sqrt (a * X)))).mono'
    (continuous_leadingRow a j).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with E hE
  rw [Real.norm_of_nonneg (vacuumLeading_nonneg a E j ha
    ((le_max_right _ _).trans hE.1.le))]
  exact vacuumLeading_le_energy_envelope j ha hT hE

theorem leadingRowMass_nonneg {a T X : ℝ} (j : ℤ) (ha : 2 ≤ a) :
    0 ≤ leadingRowMass a T X j := by
  apply setIntegral_nonneg measurableSet_Ioo
  intro E hE
  exact vacuumLeading_nonneg a E j ha ((le_max_right _ _).trans hE.1.le)

/-- One row costs only one power of the energy cutoff, including its edge. -/
theorem leadingRowMass_le {a T X : ℝ} (j : ℤ)
    (ha : 2 ≤ a) (hT : 1 ≤ T) (hX : 0 ≤ X) :
    leadingRowMass a T X j ≤ 2 * X * exp (4 * π * sqrt (a * X)) := by
  have hsub : Ioo (max T |(j : ℝ)|) X ⊆ Ioo |(j : ℝ)| X :=
    Ioo_subset_Ioo_left (le_max_right _ _)
  have hi := (show IntegrableOn (fun E : ℝ => E) (Ioo |(j : ℝ)| X)
    (referenceMeasure j) from lowBand_energy_integrable j X).mono_set hsub
  calc
    _ ≤ ∫ E in Ioo (max T |(j : ℝ)|) X,
        (2 * exp (4 * π * sqrt (a * X))) * E ∂referenceMeasure j := by
      apply setIntegral_mono_on (integrable_leadingRow j ha hT)
        (hi.const_mul _) measurableSet_Ioo
      exact fun E hE => vacuumLeading_le_energy_envelope j ha hT hE
    _ = (2 * exp (4 * π * sqrt (a * X))) *
        ∫ E in Ioo (max T |(j : ℝ)|) X, E ∂referenceMeasure j := integral_const_mul _ _
    _ ≤ (2 * exp (4 * π * sqrt (a * X))) *
        ∫ E in Ioo |(j : ℝ)| X, E ∂referenceMeasure j := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply setIntegral_mono_set (lowBand_energy_integrable j X) ?_
        (Filter.Eventually.of_forall fun E hE => hsub hE)
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with E hE
      exact (abs_nonneg (j : ℝ)).trans hE.1.le
    _ ≤ (2 * exp (4 * π * sqrt (a * X))) * X :=
      mul_le_mul_of_nonneg_left (lowBand_integral_energy_le j X hX) (by positivity)
    _ = _ := by ring

/-- No row whose spin lies beyond the energy cutoff contributes. -/
theorem leadingRowMass_eq_zero {a T X : ℝ} (j : ℤ) (hj : X ≤ |(j : ℝ)|) :
    leadingRowMass a T X j = 0 := by
  simp [leadingRowMass, Ioo_eq_empty_of_le (hj.trans (le_max_right _ _))]

theorem leadingRowMass_eq_zero_of_not_mem {a T X : ℝ} (j : ℤ)
    (hj : j ∉ Finset.Icc (-⌈X⌉) ⌈X⌉) : leadingRowMass a T X j = 0 := by
  apply leadingRowMass_eq_zero
  by_contra h
  have habs : |(j : ℝ)| < X := lt_of_not_ge h
  have hceil : X ≤ (⌈X⌉ : ℝ) := Int.le_ceil X
  apply hj
  simp only [Finset.mem_Icc]
  constructor
  · have hl : -(⌈X⌉ : ℝ) ≤ (j : ℝ) := by
      have := (abs_lt.mp habs).1
      linarith
    exact_mod_cast hl
  · have hu : (j : ℝ) ≤ (⌈X⌉ : ℝ) := by
      have := (abs_lt.mp habs).2
      linarith
    exact_mod_cast hu

/-- The all-spin sum is literally finite at every finite energy cutoff. -/
theorem leadingMass_eq_sum (a T X : ℝ) :
    leadingMass a T X = ∑ j ∈ Finset.Icc (-⌈X⌉) ⌈X⌉, leadingRowMass a T X j := by
  exact tsum_eq_sum (fun j hj => leadingRowMass_eq_zero_of_not_mem j hj)

theorem leadingRowMass_summable (a T X : ℝ) :
    Summable (fun j : ℤ => leadingRowMass a T X j) := by
  apply summable_of_hasFiniteSupport
  apply (Finset.finite_toSet (Finset.Icc (-⌈X⌉) ⌈X⌉)).subset
  intro j hj
  by_contra h
  exact hj (leadingRowMass_eq_zero_of_not_mem j h)

/-- All integer spins cost only a quadratic energy prefactor. -/
theorem leadingMass_le {a T X : ℝ}
    (ha : 2 ≤ a) (hT : 1 ≤ T) (hX : 0 ≤ X) :
    leadingMass a T X ≤ 6 * (1 + X) ^ 2 * exp (4 * π * sqrt (a * X)) := by
  have hceil : 0 ≤ ⌈X⌉ := Int.ceil_nonneg hX
  have hcard : ((Finset.Icc (-⌈X⌉) ⌈X⌉).card : ℝ) = 2 * (⌈X⌉ : ℝ) + 1 := by
    have hh := Int.card_Icc_of_le (a := -⌈X⌉) (b := ⌈X⌉) (by omega)
    have hz : ((Finset.Icc (-⌈X⌉) ⌈X⌉).card : ℤ) = 2 * ⌈X⌉ + 1 := by omega
    exact_mod_cast hz
  have hceil_le : (⌈X⌉ : ℝ) ≤ X + 1 := (Int.ceil_lt_add_one X).le
  rw [leadingMass_eq_sum]
  calc
    _ ≤ ∑ _j ∈ Finset.Icc (-⌈X⌉) ⌈X⌉,
        2 * X * exp (4 * π * sqrt (a * X)) :=
      Finset.sum_le_sum fun j _ => leadingRowMass_le j ha hT hX
    _ = (2 * (⌈X⌉ : ℝ) + 1) * (2 * X * exp (4 * π * sqrt (a * X))) := by
      rw [Finset.sum_const, nsmul_eq_mul, hcard]
    _ ≤ (2 * (X + 1) + 1) * (2 * X * exp (4 * π * sqrt (a * X))) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      linarith
    _ ≤ _ := by
      have hp : (2 * (X + 1) + 1) * (2 * X) ≤ 6 * (1 + X) ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hp (exp_pos (4 * π * sqrt (a * X))).le]

end BTZEntropy.Comparison
