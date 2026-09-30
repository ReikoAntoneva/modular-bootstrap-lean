import BTZEntropy.Comparison.ReferenceMass
import GapFamily.Analytic.Foundation.VacuumRemainder

/-! Ordinary leading-reference mass down to zero energy. The four-seed
vacuum cancellation retains a factor of energy, making the scalar integral
against `dE / E` finite as well as every nonzero-spin opening edge. -/

noncomputable section

open Set MeasureTheory Real
open GapFamily.Analytic GapFamily.Construction
open scoped BigOperators

namespace BTZEntropy.Comparison

theorem continuous_vacuumLeading_energy (a : ℝ) (j : ℤ) :
    Continuous (fun E => vacuumLeading a E j) := by
  have he : Continuous (fun E : ℝ => exp (7 * sqrt (a * E))) := by fun_prop
  have h := (continuous_tailEnvelopeNumerator a j).sub he
  convert h using 1
  ext E
  simp [tailEnvelopeNumerator]

/-- The denominator-one term of the actual null-subtracted vacuum retains
its linear energy zero uniformly on every physical low band. -/
theorem vacuumLeading_le_lowBand_energy {a T E : ℝ} (ha : 2 ≤ a)
    (j : ℤ) (hphysical : |(j : ℝ)| ≤ E) (hET : E ≤ T) :
    vacuumLeading a E j ≤
      (32 * π ^ 2 * a * exp (4 * π * sqrt (a * T))) * E := by
  have ha0 : 0 ≤ a := by linarith
  have hE0 : 0 ≤ E := (abs_nonneg _).trans hphysical
  have hterm := norm_vacuumHigherTerm_le a E j ha hphysical 0
  norm_num only [Nat.cast_zero, Nat.cast_one, zero_add, one_pow, div_one] at hterm
  calc
    _ ≤ ‖vacuumHigherTerm a E j 0‖ :=
      (le_abs_self _).trans (Complex.abs_re_le_norm _)
    _ ≤ 32 * π ^ 2 * (a * E) * exp (4 * π * sqrt (a * E)) := hterm
    _ ≤ 32 * π ^ 2 * (a * E) * exp (4 * π * sqrt (a * T)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left
        (sqrt_le_sqrt (mul_le_mul_of_nonneg_left hET ha0)) (by positivity)
    _ = _ := by ring

/-- Ordinary integrability starts at the true spin edge, including the
scalar origin; there is no positive lower cutoff premise. -/
theorem integrableOn_vacuumLeading_lowBand {a T : ℝ} (ha : 2 ≤ a) (j : ℤ) :
    IntegrableOn (fun E => vacuumLeading a E j) (Ioo |(j : ℝ)| T)
      (referenceMeasure j) := by
  apply ((lowBand_energy_integrable j T).const_mul
    (32 * π ^ 2 * a * exp (4 * π * sqrt (a * T)))).mono'
    (continuous_vacuumLeading_energy a j).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with E hE
  rw [Real.norm_of_nonneg (vacuumLeading_nonneg a E j ha hE.1.le)]
  exact vacuumLeading_le_lowBand_energy ha j hE.1.le hE.2.le

theorem leadingRowMass_zero_le {a T : ℝ} (ha : 2 ≤ a) (hT : 0 ≤ T) (j : ℤ) :
    leadingRowMass a 0 T j ≤
      32 * π ^ 2 * a * T * exp (4 * π * sqrt (a * T)) := by
  have ha0 : 0 ≤ a := by linarith
  rw [leadingRowMass, max_eq_right (abs_nonneg _)]
  calc
    _ ≤ ∫ E in Ioo |(j : ℝ)| T,
        (32 * π ^ 2 * a * exp (4 * π * sqrt (a * T))) * E ∂referenceMeasure j := by
      apply setIntegral_mono_on (integrableOn_vacuumLeading_lowBand ha j)
        ((lowBand_energy_integrable j T).const_mul _) measurableSet_Ioo
      exact fun E hE => vacuumLeading_le_lowBand_energy ha j hE.1.le hE.2.le
    _ = (32 * π ^ 2 * a * exp (4 * π * sqrt (a * T))) *
        ∫ E in Ioo |(j : ℝ)| T, E ∂referenceMeasure j := integral_const_mul _ _
    _ ≤ (32 * π ^ 2 * a * exp (4 * π * sqrt (a * T))) * T :=
      mul_le_mul_of_nonneg_left (lowBand_integral_energy_le j T hT) (by positivity)
    _ = _ := by ring

/-- Summing all actual integer spins adds only a quadratic band factor.
The estimate includes the complete zero-cutoff reference mass. -/
theorem leadingMass_zero_le {a T : ℝ} (ha : 2 ≤ a) (hT : 0 ≤ T) :
    leadingMass a 0 T ≤
      96 * π ^ 2 * a * (1 + T) ^ 2 * exp (4 * π * sqrt (a * T)) := by
  have ha0 : 0 ≤ a := by linarith
  have hceil : 0 ≤ ⌈T⌉ := Int.ceil_nonneg hT
  have hcard : ((Finset.Icc (-⌈T⌉) ⌈T⌉).card : ℝ) = 2 * (⌈T⌉ : ℝ) + 1 := by
    have hh := Int.card_Icc_of_le (a := -⌈T⌉) (b := ⌈T⌉) (by omega)
    have hz : ((Finset.Icc (-⌈T⌉) ⌈T⌉).card : ℤ) = 2 * ⌈T⌉ + 1 := by omega
    exact_mod_cast hz
  have hceil_le : (⌈T⌉ : ℝ) ≤ T + 1 := (Int.ceil_lt_add_one T).le
  rw [leadingMass_eq_sum]
  calc
    _ ≤ ∑ _j ∈ Finset.Icc (-⌈T⌉) ⌈T⌉,
        32 * π ^ 2 * a * T * exp (4 * π * sqrt (a * T)) :=
      Finset.sum_le_sum (fun j _ => leadingRowMass_zero_le ha hT j)
    _ = (2 * (⌈T⌉ : ℝ) + 1) *
        (32 * π ^ 2 * a * T * exp (4 * π * sqrt (a * T))) := by
      rw [Finset.sum_const, nsmul_eq_mul, hcard]
    _ ≤ (2 * (T + 1) + 1) *
        (32 * π ^ 2 * a * T * exp (4 * π * sqrt (a * T))) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      linarith
    _ = ((2 * (T + 1) + 1) * T) *
        (32 * π ^ 2 * a * exp (4 * π * sqrt (a * T))) := by ring
    _ ≤ (3 * (1 + T) ^ 2) *
        (32 * π ^ 2 * a * exp (4 * π * sqrt (a * T))) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      nlinarith
    _ = _ := by ring

/-- The polynomial charge factor can be absorbed without introducing a
linear exponential rate. The remaining constants depend only on the band. -/
theorem leadingMass_zero_le_exp_sqrt {a T : ℝ} (ha : 2 ≤ a) (hT : 0 ≤ T) :
    leadingMass a 0 T ≤ 96 * π ^ 2 * (1 + T) ^ 2 *
      exp ((4 * π * sqrt T + 2) * sqrt a) := by
  have ha0 : 0 ≤ a := by linarith
  have hs : sqrt a ≤ exp (sqrt a) := by linarith [add_one_le_exp (sqrt a)]
  have haexp : a ≤ exp (2 * sqrt a) := by
    calc
      a = sqrt a * sqrt a := (mul_self_sqrt ha0).symm
      _ ≤ exp (sqrt a) * exp (sqrt a) :=
        mul_le_mul hs hs (sqrt_nonneg _) (exp_pos _).le
      _ = exp (2 * sqrt a) := by rw [← exp_add]; congr 1; ring
  have hprod : a * exp (4 * π * sqrt (a * T)) ≤
      exp ((4 * π * sqrt T + 2) * sqrt a) := by
    calc
      _ ≤ exp (2 * sqrt a) * exp (4 * π * sqrt (a * T)) :=
        mul_le_mul_of_nonneg_right haexp (exp_pos _).le
      _ = _ := by
        rw [← exp_add, sqrt_mul ha0]
        congr 1
        ring
  calc
    _ ≤ 96 * π ^ 2 * a * (1 + T) ^ 2 * exp (4 * π * sqrt (a * T)) :=
      leadingMass_zero_le ha hT
    _ = (96 * π ^ 2 * (1 + T) ^ 2) *
        (a * exp (4 * π * sqrt (a * T))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hprod (by positivity)

/-- Fixed low-band geometry gives charge-independent constants for the
ordinary reference mass, including the complete scalar neighborhood. -/
theorem exists_leadingMass_zero_bound (T : ℝ) (hT : 0 ≤ T) :
    ∃ A D : ℝ, 0 < A ∧ 0 < D ∧ ∀ a : ℝ, 2 ≤ a →
      leadingMass a 0 T ≤ A * exp (D * sqrt a) := by
  refine ⟨96 * π ^ 2 * (1 + T) ^ 2, 4 * π * sqrt T + 2,
    by positivity, by positivity, ?_⟩
  exact fun a ha => leadingMass_zero_le_exp_sqrt ha hT

end BTZEntropy.Comparison
