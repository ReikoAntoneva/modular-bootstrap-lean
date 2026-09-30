import GapFamily.Analytic.Kernel.FullKernelSmoothingMoment

/-!
# Hilbert bounds from scalar-column energy moments

An ordinary complex function dominated by a nonnegative linear combination
of energy and square-root energy has a uniform physical low-band `L²` bound.
The estimate includes the infinite-mass scalar reference measure.
-/

noncomputable section

open MeasureTheory Real Set

namespace GapFamily.Analytic

private theorem scalarColumn_real_L2_norm_sq_eq_integral {μ : Measure ℝ}
    (f : Lp ℝ 2 μ) : ‖f‖ ^ 2 = ∫ e, (f e) ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

/-- The physical low-band energy coordinate has Hilbert norm at most `B`. -/
theorem scalarColumn_norm_energy_toLp_le (j : ℤ) (B : ℝ) (hB : 0 ≤ B) :
    ‖(lowBand_energy_memLp j B hB).toLp (fun E : ℝ => E)‖ ≤ B := by
  apply (sq_le_sq₀ (norm_nonneg _) hB).mp
  rw [scalarColumn_real_L2_norm_sq_eq_integral]
  calc
    _ = ∫ E, E ^ 2 ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| B) := by
      apply integral_congr_ae
      filter_upwards [(lowBand_energy_memLp j B hB).coeFn_toLp] with E hE
      rw [hE]
    _ ≤ B ^ 2 := (lowBand_energy_sq_integrable_le j hB).2

/-- The square-root energy coordinate has Hilbert norm at most `sqrt B`. -/
theorem scalarColumn_norm_sqrt_energy_toLp_le (j : ℤ) (B : ℝ) (hB : 0 ≤ B) :
    ‖(lowBand_sqrt_energy_memLp j B).toLp (fun E : ℝ => sqrt E)‖ ≤ sqrt B := by
  apply (sq_le_sq₀ (norm_nonneg _) (sqrt_nonneg B)).mp
  rw [scalarColumn_real_L2_norm_sq_eq_integral, Real.sq_sqrt hB]
  calc
    _ = ∫ E, E ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| B) := by
      apply integral_congr_ae
      filter_upwards [(lowBand_sqrt_energy_memLp j B).coeFn_toLp,
        ae_restrict_mem measurableSet_Ioo] with E hE hband
      rw [hE, Real.sq_sqrt ((abs_nonneg (j : ℝ)).trans hband.1.le)]
    _ ≤ B := by
      by_cases hj : |(j : ℝ)| ≤ B
      · rw [lowBand_integral_energy j hj]
        exact (Real.sqrt_le_left hB).mpr (by nlinarith [sq_nonneg (j : ℝ)])
      · simp [Ioo_eq_empty_of_le (le_of_not_ge hj), hB]

/-- A pointwise energy/square-root majorant gives its corresponding Hilbert
bound without assuming finite reference mass. -/
theorem norm_toLp_le_of_energy_sqrt_bound (j : ℤ) (B : ℝ) (hB : 0 ≤ B)
    (f : ℝ → ℂ)
    (hf : MemLp f 2 ((referenceMeasure j).restrict (Ioo |(j : ℝ)| B)))
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hpoint : ∀ᵐ e ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| B),
      ‖f e‖ ≤ a * e + b * sqrt e) :
    ‖hf.toLp f‖ ≤ a * B + b * sqrt B := by
  let u := (lowBand_energy_memLp j B hB).toLp (fun E : ℝ => E)
  let v := (lowBand_sqrt_energy_memLp j B).toLp (fun E : ℝ => sqrt E)
  have hu : ‖u‖ ≤ B := scalarColumn_norm_energy_toLp_le j B hB
  have hv : ‖v‖ ≤ sqrt B := scalarColumn_norm_sqrt_energy_toLp_le j B hB
  calc
    _ ≤ ‖a • u + b • v‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [hf.coeFn_toLp, Lp.coeFn_add (a • u) (b • v),
        Lp.coeFn_smul a u, Lp.coeFn_smul b v,
        (lowBand_energy_memLp j B hB).coeFn_toLp,
        (lowBand_sqrt_energy_memLp j B).coeFn_toLp,
        ae_restrict_mem measurableSet_Ioo, hpoint] with e hf hadd hau hbv hu hv he hp
      have he0 := (abs_nonneg (j : ℝ)).trans he.1.le
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hadd hau hbv
      rw [hf, hadd, hau, hbv, hu, hv, Real.norm_of_nonneg (by positivity)]
      exact hp
    _ ≤ ‖a • u‖ + ‖b • v‖ := norm_add_le _ _
    _ = a * ‖u‖ + b * ‖v‖ := by
      rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
    _ ≤ a * B + b * sqrt B := by gcongr

end GapFamily.Analytic
