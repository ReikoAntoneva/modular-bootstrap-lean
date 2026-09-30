import GapFamily.Construction.ThermalEnvelope

/-! The all-spin ordinary thermal mass left beyond an energy cutoff.
Its exponential decay follows from the same envelope at half temperature. -/

noncomputable section
open Set MeasureTheory Real Filter
open scoped Topology

namespace GapFamily.Construction

/-- The actual positive envelope mass remaining above `R`, summed over every
integer spin. Each row is an ordinary real integral. -/
def tailEnvelopeThermalTail (a T t R : ℝ) : ℝ :=
  ∑' j : ℤ, ∫ E in Ici R, exp (-t * E) ∂tailEnvelopeMeasure a T j

/-- Every cutoff row remains ordinarily integrable. -/
theorem integrableOn_thermal_tailEnvelopeMeasure (a T R : ℝ) (j : ℤ)
    (ha : 100 ≤ a) (hT : 1 ≤ T) {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun E => exp (-t * E)) (Ici R) (tailEnvelopeMeasure a T j) :=
  (integrable_thermal_tailEnvelopeMeasure a T j ha hT ht).integrableOn

/-- Restricting the positive thermal rows preserves their all-spin summability. -/
theorem summable_integral_thermal_tailEnvelopeMeasure_cutoff (a T R : ℝ)
    (ha : 100 ≤ a) (hT : 1 ≤ T) {t : ℝ} (ht : 0 < t) :
    Summable (fun j : ℤ => ∫ E in Ici R, exp (-t * E) ∂tailEnvelopeMeasure a T j) := by
  apply (summable_integral_thermal_tailEnvelopeMeasure a T ha hT ht).of_nonneg_of_le
  · intro j
    exact integral_nonneg fun E => exp_nonneg _
  · intro j
    exact setIntegral_le_integral
      (integrable_thermal_tailEnvelopeMeasure a T j ha hT ht)
      (Eventually.of_forall fun E => exp_nonneg _)

theorem tailEnvelopeThermalTail_nonneg (a T t R : ℝ) :
    0 ≤ tailEnvelopeThermalTail a T t R := by
  exact tsum_nonneg fun j => integral_nonneg fun E => exp_nonneg _

/-- On each actual row, the cutoff supplies one half of the exponential
decay and leaves an integrable half-temperature majorant. -/
theorem integral_thermal_tailEnvelopeMeasure_cutoff_le (a T R : ℝ) (j : ℤ)
    (ha : 100 ≤ a) (hT : 1 ≤ T) {t : ℝ} (ht : 0 < t) :
    (∫ E in Ici R, exp (-t * E) ∂tailEnvelopeMeasure a T j) ≤
      exp (-(t / 2) * R) *
        ∫ E, exp (-(t / 2) * E) ∂tailEnvelopeMeasure a T j := by
  have ht2 : 0 < t / 2 := by linarith
  have hi := integrable_thermal_tailEnvelopeMeasure a T j ha hT ht2
  calc
    _ ≤ ∫ E in Ici R, exp (-(t / 2) * R) * exp (-(t / 2) * E)
        ∂tailEnvelopeMeasure a T j := by
      apply integral_mono_ae
        (integrableOn_thermal_tailEnvelopeMeasure a T R j ha hT ht)
        (hi.const_mul _).integrableOn
      filter_upwards [ae_restrict_mem measurableSet_Ici] with E hE
      rw [← exp_add]
      apply exp_le_exp.mpr
      have hmul : t * R ≤ t * E := mul_le_mul_of_nonneg_left hE ht.le
      nlinarith
    _ ≤ ∫ E, exp (-(t / 2) * R) * exp (-(t / 2) * E)
        ∂tailEnvelopeMeasure a T j :=
      setIntegral_le_integral (hi.const_mul _)
        (Eventually.of_forall fun E => mul_nonneg (exp_nonneg _) (exp_nonneg _))
    _ = _ := integral_const_mul _ _

/-- A finite ordinary all-spin thermal majorant controls the entire remaining
tail by an explicit exponentially vanishing factor. -/
theorem tailEnvelopeThermalTail_le (a T R : ℝ)
    (ha : 100 ≤ a) (hT : 1 ≤ T) {t : ℝ} (ht : 0 < t) :
    tailEnvelopeThermalTail a T t R ≤ exp (-(t / 2) * R) *
      ∑' j : ℤ, ∫ E, exp (-(t / 2) * E) ∂tailEnvelopeMeasure a T j := by
  have ht2 : 0 < t / 2 := by linarith
  calc
    _ ≤ ∑' j : ℤ, exp (-(t / 2) * R) *
        ∫ E, exp (-(t / 2) * E) ∂tailEnvelopeMeasure a T j :=
      (summable_integral_thermal_tailEnvelopeMeasure_cutoff a T R ha hT ht).tsum_le_tsum
        (fun j => integral_thermal_tailEnvelopeMeasure_cutoff_le a T R j ha hT ht)
        ((summable_integral_thermal_tailEnvelopeMeasure a T ha hT ht2).mul_left _)
    _ = _ := tsum_mul_left

/-- The entire ordinary all-spin thermal tail vanishes as the energy cutoff
tends to infinity. -/
theorem tendsto_tailEnvelopeThermalTail (a T : ℝ)
    (ha : 100 ≤ a) (hT : 1 ≤ T) {t : ℝ} (ht : 0 < t) :
    Tendsto (tailEnvelopeThermalTail a T t) atTop (𝓝 0) := by
  have harg : Tendsto (fun R : ℝ => -(t / 2) * R) atTop atBot :=
    tendsto_id.const_mul_atTop_of_neg (by linarith)
  have hdecay : Tendsto
      (fun R : ℝ => exp (-(t / 2) * R) *
        ∑' j : ℤ, ∫ E, exp (-(t / 2) * E) ∂tailEnvelopeMeasure a T j)
      atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_atBot.comp harg).mul_const
      (∑' j : ℤ, ∫ E, exp (-(t / 2) * E) ∂tailEnvelopeMeasure a T j)
  exact squeeze_zero (tailEnvelopeThermalTail_nonneg a T t)
    (fun R => tailEnvelopeThermalTail_le a T R ha hT ht) hdecay

theorem tendsto_tailEnvelopeThermalTail_nat (a T : ℝ)
    (ha : 100 ≤ a) (hT : 1 ≤ T) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n : ℕ => tailEnvelopeThermalTail a T t n) atTop (𝓝 0) :=
  (tendsto_tailEnvelopeThermalTail a T ha hT ht).comp tendsto_natCast_atTop_atTop

/-- The physical cutoffs `T + n` exhaust the same positive thermal envelope. -/
theorem tendsto_tailEnvelopeThermalTail_shift_nat (a T : ℝ)
    (ha : 100 ≤ a) (hT : 1 ≤ T) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n : ℕ => tailEnvelopeThermalTail a T t (T + n)) atTop (𝓝 0) :=
  (tendsto_tailEnvelopeThermalTail a T ha hT ht).comp
    (tendsto_atTop_add_const_left atTop T tendsto_natCast_atTop_atTop)

end GapFamily.Construction
