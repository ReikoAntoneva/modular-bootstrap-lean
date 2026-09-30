import GapFamily.Analytic.Kernel.FullKernelScalarColumnMoment

/-!
# Ordinary input-column bounds from energy moments

A complex function with an energy and square-root energy majorant has an
ordinary mass estimate on every physical low band. The estimate includes
the scalar reference measure, whose total mass is infinite.
-/

noncomputable section

open MeasureTheory Real Set

namespace GapFamily.Analytic

/-- Integrating an energy/square-root majorant gives a uniform ordinary mass
bound against the actual physical reference measure. -/
theorem integral_norm_le_of_energy_sqrt_bound (j : ℤ) (B : ℝ) (hB : 0 ≤ B)
    (f : ℝ → ℂ)
    (hf : Integrable f ((referenceMeasure j).restrict (Ioo |(j : ℝ)| B)))
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hpoint : ∀ᵐ e ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| B),
      ‖f e‖ ≤ a * e + b * sqrt e) :
    (∫ e, ‖f e‖ ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) ≤
      a * B + b * (B + 2 * sqrt B) := by
  have hE := lowBand_energy_integrable j B
  have hS := lowBand_sqrt_energy_integrable j B
  have hEm : (∫ e, e ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) ≤ B := by
    by_cases hj : |(j : ℝ)| ≤ B
    · rw [lowBand_integral_energy j hj]
      exact (Real.sqrt_le_left hB).mpr (by nlinarith [sq_nonneg (j : ℝ)])
    · simp [Ioo_eq_empty_of_le (le_of_not_ge hj), hB]
  calc
    _ ≤ ∫ e, a * e + b * sqrt e
        ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| B) :=
      integral_mono_ae hf.norm ((hE.const_mul a).add (hS.const_mul b)) hpoint
    _ = a * (∫ e, e ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) +
        b * (∫ e, sqrt e ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) := by
      rw [integral_add (hE.const_mul a) (hS.const_mul b),
        integral_const_mul, integral_const_mul]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hEm ha)
      (mul_le_mul_of_nonneg_left (lowBand_integral_sqrt_energy_le j B hB) hb)

/-- The ordinary `L¹` equivalence class obeys the same energy-moment bound. -/
theorem norm_toL1_le_of_energy_sqrt_bound (j : ℤ) (B : ℝ) (hB : 0 ≤ B)
    (f : ℝ → ℂ)
    (hf : MemLp f 1 ((referenceMeasure j).restrict (Ioo |(j : ℝ)| B)))
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hpoint : ∀ᵐ e ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| B),
      ‖f e‖ ≤ a * e + b * sqrt e) :
    ‖hf.toLp f‖ ≤ a * B + b * (B + 2 * sqrt B) := by
  have hi : Integrable f ((referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) :=
    memLp_one_iff_integrable.mp hf
  change ‖hi.toL1 f‖ ≤ _
  rw [L1.norm_of_fun_eq_integral_norm]
  exact integral_norm_le_of_energy_sqrt_bound j B hB f hi a b ha hb hpoint

end GapFamily.Analytic
