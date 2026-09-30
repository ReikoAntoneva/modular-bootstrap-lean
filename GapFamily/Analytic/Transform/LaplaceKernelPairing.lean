import GapFamily.Analytic.Transform.LaplaceTest
import GapFamily.Analytic.Kernel.FullKernel
import GapFamily.Analytic.Kernel.HigherKernelThermal
import Mathlib.MeasureTheory.Integral.Prod

/-! Ordinary absolute convergence of the actual energy-side finite Laplace
pairing. The two height differences control both scalar endpoints, and the
physical kernel bound controls the full two-energy tail. -/

noncomputable section
namespace GapFamily.Analytic
open MeasureTheory

theorem continuous_laplaceTest (k : ℕ) : Continuous (laplaceTest k) := by
  unfold laplaceTest
  fun_prop

theorem laplaceTest_le_exp_neg (k : ℕ) {E : ℝ} (hE : 0 ≤ E) :
    laplaceTest k E ≤ Real.exp (-E) := by
  apply (laplaceTest_le_exp k E).trans
  apply Real.exp_le_exp.mpr
  nlinarith [Nat.cast_nonneg (α := ℝ) k]

theorem laplaceTest_le_energy_exp_neg (k : ℕ) {E : ℝ} (hE : 0 ≤ E) :
    laplaceTest k E ≤ E * Real.exp (-E) := by
  apply (laplaceTest_le_energy k E).trans
  apply mul_le_mul_of_nonneg_left _ hE
  apply Real.exp_le_exp.mpr
  nlinarith [Nat.cast_nonneg (α := ℝ) k]

/-- Each endpoint-regularized test itself has finite ordinary reference mass. -/
theorem integrable_laplaceTest_referenceMeasure (j : ℤ) (k : ℕ) :
    Integrable (laplaceTest k) (referenceMeasure j) := by
  apply (integrable_energy_exp_referenceMeasure j (by norm_num : (0 : ℝ) < 1)).mono'
  · exact (continuous_laplaceTest k).aestronglyMeasurable
  · filter_upwards [referenceMeasure_ae_above_edge j] with E hE
    have hE0 : 0 < E := (abs_nonneg _).trans_lt hE
    rw [Real.norm_of_nonneg (laplaceTest_pos k hE0).le]
    simpa only [neg_one_mul] using laplaceTest_le_energy_exp_neg k hE0.le

/-- The identity-operator term in the finite energy pairing is an ordinary
integral, including when both tests are in the scalar sector. -/
theorem integrable_laplaceTest_product_referenceMeasure (j : ℤ) (k l : ℕ) :
    Integrable (fun E => laplaceTest k E * laplaceTest l E) (referenceMeasure j) := by
  apply (integrable_laplaceTest_referenceMeasure j k).mono'
  · exact ((continuous_laplaceTest k).mul (continuous_laplaceTest l)).aestronglyMeasurable
  · filter_upwards [referenceMeasure_ae_above_edge j] with E hE
    have hE0 : 0 < E := (abs_nonneg _).trans_lt hE
    have hk := (laplaceTest_pos k hE0).le
    have hl := (laplaceTest_pos l hE0).le
    rw [Real.norm_of_nonneg (mul_nonneg hk hl)]
    have hl1 : laplaceTest l E ≤ 1 := (laplaceTest_le_exp_neg l hE0.le).trans
      (Real.exp_le_one_iff.mpr (by linarith))
    nlinarith

theorem laplaceTest_mul_energy_le (k : ℕ) {E : ℝ} (hE : 0 ≤ E) :
    laplaceTest k E * E ≤ E * Real.exp (-(1 / 2 : ℝ) * E) := by
  calc
    _ ≤ Real.exp (-E) * E := mul_le_mul_of_nonneg_right (laplaceTest_le_exp_neg k hE) hE
    _ ≤ Real.exp (-(1 / 2 : ℝ) * E) * E := by
      gcongr
      linarith
    _ = _ := mul_comm _ _

theorem laplaceTest_mul_sqrt_le (k : ℕ) {E : ℝ} (hE : 0 ≤ E) :
    laplaceTest k E * Real.sqrt E ≤ E * Real.exp (-(1 / 2 : ℝ) * E) := by
  have hs : Real.sqrt E ≤ Real.exp (E / 2) := by
    have he := Real.add_one_le_exp (E / 2)
    have hsq := Real.sq_sqrt hE
    nlinarith [sq_nonneg (Real.sqrt E - 1)]
  calc
    _ ≤ (E * Real.exp (-E)) * Real.exp (E / 2) :=
      mul_le_mul (laplaceTest_le_energy_exp_neg k hE) hs (Real.sqrt_nonneg E)
        (by positivity)
    _ = _ := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

/-- A single product of ordinary integrable thermal envelopes dominates every
finite Laplace test pair of the actual corrected energy kernel. -/
theorem exists_laplaceTest_correctedKernel_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (j J : ℤ) (k l : ℕ) (e E : ℝ),
      |(j : ℝ)| < e → |(J : ℝ)| < E →
      ‖(laplaceTest k e : ℂ) * correctedKernel j J e E * (laplaceTest l E : ℂ)‖ ≤
        C * ((e * Real.exp (-(1 / 2 : ℝ) * e)) *
          (E * Real.exp (-(1 / 2 : ℝ) * E))) := by
  obtain ⟨C, hC, hbound⟩ := exists_correctedKernel_physical_bound
  refine ⟨2 * C, by positivity, ?_⟩
  intro j J k l e E he hE
  have he0 : 0 < e := (abs_nonneg _).trans_lt he
  have hE0 : 0 < E := (abs_nonneg _).trans_lt hE
  have hk := (laplaceTest_pos k he0).le
  have hl := (laplaceTest_pos l hE0).le
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg hk, Real.norm_of_nonneg hl]
  have hspin : |(j : ℝ)| * |(J : ℝ)| ≤ e * E :=
    mul_le_mul he.le hE.le (abs_nonneg _) he0.le
  have hker : ‖correctedKernel j J e E‖ ≤ C * (e * E + Real.sqrt e * Real.sqrt E) :=
    (hbound j J e E he.le hE.le).trans
      (mul_le_mul_of_nonneg_left (add_le_add hspin le_rfl) hC.le)
  calc
    _ ≤ laplaceTest k e * (C * (e * E + Real.sqrt e * Real.sqrt E)) * laplaceTest l E := by
      gcongr
    _ = C * ((laplaceTest k e * e) * (laplaceTest l E * E) +
        (laplaceTest k e * Real.sqrt e) * (laplaceTest l E * Real.sqrt E)) := by ring
    _ ≤ C * ((e * Real.exp (-(1 / 2 : ℝ) * e)) *
        (E * Real.exp (-(1 / 2 : ℝ) * E)) +
        (e * Real.exp (-(1 / 2 : ℝ) * e)) *
        (E * Real.exp (-(1 / 2 : ℝ) * E))) := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      apply add_le_add
      · exact mul_le_mul (laplaceTest_mul_energy_le k he0.le)
          (laplaceTest_mul_energy_le l hE0.le) (by positivity) (by positivity)
      · exact mul_le_mul (laplaceTest_mul_sqrt_le k he0.le)
          (laplaceTest_mul_sqrt_le l hE0.le) (by positivity) (by positivity)
    _ = _ := by ring

/-- Absolute product-measure integrability of the full energy pairing. This
certifies Fubini at both scalar origins and at both unbounded ends. -/
theorem integrable_laplaceTest_correctedKernel_pair (j J : ℤ) (k l : ℕ) :
    Integrable (fun p : ℝ × ℝ => (laplaceTest k p.1 : ℂ) *
      correctedKernel j J p.1 p.2 * (laplaceTest l p.2 : ℂ))
      ((referenceMeasure j).prod (referenceMeasure J)) := by
  obtain ⟨C, _, hC⟩ := exists_laplaceTest_correctedKernel_bound
  apply (((integrable_energy_exp_referenceMeasure j (by norm_num : (0 : ℝ) < 1 / 2)).mul_prod
    (integrable_energy_exp_referenceMeasure J (by norm_num : (0 : ℝ) < 1 / 2))).const_mul C).mono'
  · exact (((Complex.continuous_ofReal.comp ((continuous_laplaceTest k).comp continuous_fst)).mul
      (continuous_correctedKernel j J)).mul
      (Complex.continuous_ofReal.comp ((continuous_laplaceTest l).comp continuous_snd))).aestronglyMeasurable
  · have hp : ∀ᵐ p : ℝ × ℝ ∂(referenceMeasure j).prod (referenceMeasure J),
        |(j : ℝ)| < p.1 ∧ |(J : ℝ)| < p.2 := by
      apply (Measure.ae_prod_iff_ae_ae
        ((measurableSet_lt measurable_const measurable_fst).inter
          (measurableSet_lt measurable_const measurable_snd))).mpr
      filter_upwards [referenceMeasure_ae_above_edge j] with e he
      filter_upwards [referenceMeasure_ae_above_edge J] with E hE
      exact ⟨he, hE⟩
    filter_upwards [hp] with p hp
    exact hC j J k l p.1 p.2 hp.1 hp.2

/-- The actual identity-plus-corrected-kernel pairing of two real finite
Laplace tests, before any positivity theorem is asserted. -/
def laplaceEnergyPairing (j J : ℤ) (k l : ℕ) : ℂ :=
  (if j = J then
    ((∫ E, laplaceTest k E * laplaceTest l E ∂referenceMeasure j) : ℂ) else 0) +
  ∫ p : ℝ × ℝ, (laplaceTest k p.1 : ℂ) * correctedKernel j J p.1 p.2 *
    (laplaceTest l p.2 : ℂ) ∂((referenceMeasure j).prod (referenceMeasure J))

/-- Fubini identifies the ordinary product pairing with its iterated energy
integrals; this uses the proved product integrability, not default integrals. -/
theorem laplaceEnergyPairing_eq_iterated (j J : ℤ) (k l : ℕ) :
    laplaceEnergyPairing j J k l =
      (if j = J then
        ((∫ E, laplaceTest k E * laplaceTest l E ∂referenceMeasure j) : ℂ) else 0) +
      ∫ e, ∫ E, (laplaceTest k e : ℂ) * correctedKernel j J e E *
        (laplaceTest l E : ℂ) ∂referenceMeasure J ∂referenceMeasure j := by
  unfold laplaceEnergyPairing
  rw [integral_prod _ (integrable_laplaceTest_correctedKernel_pair j J k l)]

end GapFamily.Analytic
