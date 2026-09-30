import GapFamily.Construction.TailCellExistence
import GapFamily.Analytic.Foundation.SignedThermalDensity

/-! Thermal domination of the actual unit nodes on one short cell.
Only ordinary integrals of its signed continuum are used. -/

noncomputable section
open Set MeasureTheory Real Filter
open GapFamily.Analytic

namespace GapFamily.Construction

/-- The physical continuum restriction of a tail cell is supported at
nonnegative energy, including cells which start at their spin edge. -/
theorem TailCell.ae_nonneg {j : ℤ} {L : ℝ} {k : ℕ} {q : ℝ → ℝ}
    (cell : TailCell j L k q) (hL : 0 ≤ L) :
    ∀ᵐ E ∂(referenceMeasure j).restrict (Ioo L cell.right), 0 ≤ E := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with E hE
  exact hL.trans hE.1.le

/-- Positive integer mass and support within an interval of length at most
one give the exact factor exp(t) for the actual weighted unit-node count. -/
theorem TailCell.thermal_node_sum_le_of_envelope
    {j : ℤ} {L : ℝ} {k : ℕ} {q g : ℝ → ℝ}
    (cell : TailCell j L k q) (hL : 0 ≤ L) {t : ℝ} (ht : 0 ≤ t)
    (hg : IntegrableOn g (Ioo L cell.right) (referenceMeasure j))
    (hg0 : ∀ E ∈ Ioo L cell.right, 0 ≤ g E)
    (hbound : ∀ E ∈ Ioo L cell.right, |q E| ≤ g E) :
    (∑ i, exp (-t * cell.node i)) ≤
      exp t * ∫ E in Ioo L cell.right, exp (-t * E) * g E ∂referenceMeasure j := by
  have hmass : (cell.count : ℝ) ≤ ∫ E in Ioo L cell.right, g E ∂referenceMeasure j := by
    rw [← cell.mass_eq]
    apply setIntegral_mono_on cell.density_integrable hg measurableSet_Ioo
    exact fun E hE => (le_abs_self (q E)).trans (hbound E hE)
  have hweighted := signedDensity_integrable_thermal_mul hg (cell.ae_nonneg hL) ht
  calc
    (∑ i, exp (-t * cell.node i)) ≤ ∑ _i : Fin cell.count, exp (-t * L) := by
      apply Finset.sum_le_sum
      intro i hi
      exact exp_le_exp.mpr (mul_le_mul_of_nonpos_left (cell.node_mem i).1 (by linarith))
    _ = (cell.count : ℝ) * exp (-t * L) := by simp
    _ ≤ exp (-t * L) * ∫ E in Ioo L cell.right, g E ∂referenceMeasure j := by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right hmass (exp_pos _).le
    _ = ∫ E in Ioo L cell.right, exp (-t * L) * g E ∂referenceMeasure j :=
      (integral_const_mul _ _).symm
    _ ≤ ∫ E in Ioo L cell.right, exp t * (exp (-t * E) * g E) ∂referenceMeasure j := by
      apply setIntegral_mono_on (hg.const_mul _) (hweighted.const_mul _) measurableSet_Ioo
      intro E hE
      have hEupper : E ≤ L + 1 := hE.2.le.trans cell.right_mem.2
      have he : exp (-t * L) ≤ exp t * exp (-t * E) := by
        rw [← exp_add]
        apply exp_le_exp.mpr
        have hm := mul_le_mul_of_nonneg_left hEupper ht
        nlinarith
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right he (hg0 E hE)
    _ = _ := integral_const_mul _ _

/-- The absolute thermal continuum mass is controlled by the same ordinary
envelope integral used to bound the unit-node count. -/
theorem TailCell.thermal_density_le_of_envelope
    {j : ℤ} {L : ℝ} {k : ℕ} {q g : ℝ → ℝ}
    (cell : TailCell j L k q) (hL : 0 ≤ L) {t : ℝ} (ht : 0 ≤ t)
    (hg : IntegrableOn g (Ioo L cell.right) (referenceMeasure j))
    (hbound : ∀ E ∈ Ioo L cell.right, |q E| ≤ g E) :
    (∫ E in Ioo L cell.right, exp (-t * E) * |q E| ∂referenceMeasure j) ≤
      ∫ E in Ioo L cell.right, exp (-t * E) * g E ∂referenceMeasure j := by
  apply setIntegral_mono_on
    (signedDensity_integrable_thermal_mul cell.density_integrable.abs (cell.ae_nonneg hL) ht)
    (signedDensity_integrable_thermal_mul hg (cell.ae_nonneg hL) ht) measurableSet_Ioo
  intro E hE
  exact mul_le_mul_of_nonneg_left (hbound E hE) (exp_pos _).le

end GapFamily.Construction
