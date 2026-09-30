import GapFamily.Analytic.Kernel.FullKernelResponse

/-!
# Low-band Hilbert control by holomorphic response

On each nonzero integer spin row, the first energy moment controls the
reference mass. On the scalar row, the removable quotient preserves the
square-root zero needed to integrate against the infinite measure `de/e`.
-/

noncomputable section

open MeasureTheory Real Set
open scoped BigOperators

namespace GapFamily.Analytic

private theorem lowBand_energy_integral_le (j : ℤ) (b : ℝ) (hb : 0 ≤ b) :
    (∫ e, e ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| b)) ≤ b := by
  by_cases hj : |(j : ℝ)| ≤ b
  · rw [lowBand_integral_energy j hj]
    exact (Real.sqrt_le_left hb).mpr (by nlinarith [sq_nonneg (j : ℝ)])
  · simp [Ioo_eq_empty_of_le (le_of_not_ge hj), hb]

private theorem lowBand_sqrt_coordinate (j : ℤ) {b e : ℝ} (hb : 0 < b)
    (he : e ∈ Ioo |(j : ℝ)| b) :
    sqrt ((e - |(j : ℝ)|) / b) ∈ Icc (0 : ℝ) 1 ∧
      |(j : ℝ)| + b * sqrt ((e - |(j : ℝ)|) / b) ^ 2 = e := by
  have hq : 0 ≤ (e - |(j : ℝ)|) / b := div_nonneg (sub_nonneg.mpr he.1.le) hb.le
  refine ⟨⟨sqrt_nonneg _, ?_⟩, ?_⟩
  · apply (sqrt_le_one).mpr
    apply (div_le_one hb).mpr
    linarith [abs_nonneg (j : ℝ), he.2]
  · rw [sq_sqrt hq]
    field_simp
    ring

/-- A uniform scaled-response bound controls the ordinary squared norm of
every nonzero integer output row. -/
theorem integral_norm_sq_correctedKernelResponse_nonzero_le
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (b : ℝ) (hb : 0 < b)
    (f : LowBandHilbert J b) (j : ℤ) (hj : j ≠ 0) (M : ℝ)
    (hM : ∀ t ∈ Icc (0 : ℝ) 1, ‖correctedKernelScaledResponse J b f j t‖ ≤ M) :
    (∫ e, ‖correctedKernelResponse J b f j e‖ ^ 2
      ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| b)) ≤ b * M ^ 2 := by
  have hMn : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by simp))
  have hj1 : (1 : ℝ) ≤ |(j : ℝ)| := by exact_mod_cast Int.one_le_abs hj
  calc
    _ ≤ ∫ e, M ^ 2 * e ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| b) := by
      apply integral_mono_ae
        ((correctedKernelResponse_memLp_lowBand J b hb.le f j).integrable_norm_pow (by norm_num))
        ((lowBand_energy_integrable j b).const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with e he
      obtain ⟨ht, het⟩ := lowBand_sqrt_coordinate j hb he
      have hn : ‖correctedKernelResponse J b f j e‖ ≤ M := by
        simpa only [correctedKernelScaledResponse_ofReal J b hb f j _ ht.1, het] using
          hM _ ht
      calc
        _ ≤ M ^ 2 := by nlinarith [norm_nonneg (correctedKernelResponse J b f j e)]
        _ ≤ M ^ 2 * e := by nlinarith [sq_nonneg M, hj1.trans he.1.le]
    _ = M ^ 2 * ∫ e, e ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| b) :=
      integral_const_mul _ _
    _ ≤ M ^ 2 * b := mul_le_mul_of_nonneg_left (lowBand_energy_integral_le j b hb.le) (sq_nonneg M)
    _ = b * M ^ 2 := by ring

/-- The normalized scalar response controls the ordinary squared norm with
constant one, retaining its square-root zero at the scalar origin. -/
theorem integral_norm_sq_correctedKernelResponse_scalar_le
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (b : ℝ) (hb : 0 < b)
    (f : LowBandHilbert J b) (M : ℝ)
    (hM : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖correctedKernelScalarNormalizedResponse J b f t‖ ≤ M) :
    (∫ e, ‖correctedKernelResponse J b f 0 e‖ ^ 2
      ∂(referenceMeasure 0).restrict (Ioo 0 b)) ≤ M ^ 2 := by
  have hMn : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by simp))
  have hscalar : Ioo |((0 : ℤ) : ℝ)| b = Ioo 0 b := by simp
  calc
    _ ≤ ∫ e, (M ^ 2 / b) * e ∂(referenceMeasure 0).restrict (Ioo 0 b) := by
      apply integral_mono_ae
        (by simpa only [hscalar] using
          (correctedKernelResponse_memLp_lowBand J b hb.le f 0).integrable_norm_pow (by norm_num))
        (by simpa only [hscalar] using (lowBand_energy_integrable 0 b).const_mul (M ^ 2 / b))
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with e he
      have het : sqrt (e / b) ^ 2 = e / b := sq_sqrt (div_nonneg he.1.le hb.le)
      have htpos : 0 < sqrt (e / b) := sqrt_pos.mpr (div_pos he.1 hb)
      have ht : sqrt (e / b) ∈ Icc (0 : ℝ) 1 := by
        exact ⟨htpos.le, sqrt_le_one.mpr ((div_le_one hb).mpr he.2.le)⟩
      have henergy : b * sqrt (e / b) ^ 2 = e := by rw [het]; field_simp
      have heq : correctedKernelResponse J b f 0 e =
          correctedKernelScalarNormalizedResponse J b f (sqrt (e / b)) *
            (sqrt (e / b) : ℂ) := by
        rw [correctedKernelScalarNormalizedResponse_eq_div J b f _
          (by exact_mod_cast htpos.ne')]
        rw [div_mul_cancel₀ _ (by exact_mod_cast htpos.ne')]
        simpa only [Int.cast_zero, abs_zero, zero_add, henergy] using
          (correctedKernelScaledResponse_ofReal J b hb f 0 _ htpos.le).symm
      have hn : ‖correctedKernelResponse J b f 0 e‖ ≤ M * sqrt (e / b) := by
        rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos]
        exact mul_le_mul_of_nonneg_right (hM _ ht) htpos.le
      calc
        _ ≤ (M * sqrt (e / b)) ^ 2 := by
          nlinarith [norm_nonneg (correctedKernelResponse J b f 0 e)]
        _ = (M ^ 2 / b) * e := by rw [mul_pow, het]; ring
    _ = (M ^ 2 / b) * ∫ e, e ∂(referenceMeasure 0).restrict (Ioo 0 b) := integral_const_mul _ _
    _ = M ^ 2 := by
      have hi : (∫ e, e ∂(referenceMeasure 0).restrict (Ioo 0 b)) = b := by
        have hi := lowBand_integral_energy 0 (by simpa using hb.le : |((0 : ℤ) : ℝ)| ≤ b)
        norm_num at hi
        rw [Real.sqrt_sq hb.le] at hi
        exact hi
      rw [hi, div_mul_cancel₀ _ hb.ne']

/-- A common response bound on the unit interval controls the actual full
low-band Hilbert operator, with the scalar channel normalized at zero. -/
theorem norm_sq_correctedLowBandOperator_le_of_response_bound
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (b : ℝ) (hb : 1 ≤ b)
    (f : LowBandHilbert J b) (M : ℝ)
    (hscalar : ∀ i, J i = 0 → ∀ t ∈ Icc (0 : ℝ) 1,
      ‖correctedKernelScalarNormalizedResponse J b f t‖ ≤ M)
    (hresponse : ∀ i, J i ≠ 0 → ∀ t ∈ Icc (0 : ℝ) 1,
      ‖correctedKernelScaledResponse J b f (J i) t‖ ≤ M) :
    ‖correctedLowBandOperator J b f‖ ^ 2 ≤ (Fintype.card ι : ℝ) * b * M ^ 2 := by
  have hbpos : 0 < b := lt_of_lt_of_le zero_lt_one hb
  rw [lowBandHilbert_norm_sq_eq_integral]
  calc
    _ = ∑ i, ∫ e, ‖correctedKernelResponse J b f (J i) e‖ ^ 2
        ∂(referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| b) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply integral_congr_ae
      filter_upwards [correctedLowBandOperator_coeFn J b hbpos.le f i] with e he
      rw [he]
    _ ≤ ∑ _i : ι, b * M ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hj : J i = 0
      · simp only [hj, Int.cast_zero, abs_zero]
        exact (integral_norm_sq_correctedKernelResponse_scalar_le J b hbpos f M (hscalar i hj)).trans
          (by nlinarith [sq_nonneg M])
      · exact integral_norm_sq_correctedKernelResponse_nonzero_le J b hbpos f (J i) hj M
          (hresponse i hj)
    _ = (Fintype.card ι : ℝ) * b * M ^ 2 := by simp; ring

end GapFamily.Analytic
