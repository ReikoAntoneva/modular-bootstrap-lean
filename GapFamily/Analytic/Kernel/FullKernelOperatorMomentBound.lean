import GapFamily.Analytic.Kernel.FullKernelSmoothing

/-!
# Polynomial operator control from physical energy moments

The first and square-root energy moments bound the actual ordinary pairings.
Cauchy--Schwarz for the finite row sum then gives a linear cardinality loss.
-/

noncomputable section

open MeasureTheory Real Set
open scoped BigOperators ComplexConjugate

namespace GapFamily.Analytic

/-- The full physical kernel pairing has a quadratic band bound in the
actual row Hilbert norms, including the scalar row. -/
theorem norm_correctedKernel_lowBandPairing_le_moment
    (j J : ℤ) (B : ℝ) (hB : 0 ≤ B) (g : LowBandRow j B) (f : LowBandRow J B) :
    ‖lowBandKernelPairing j J B (fun p => correctedKernel j J p.1 p.2) g f‖ ≤
      correctedKernelBound * (B ^ 2 + B) * ‖g‖ * ‖f‖ := by
  have hC := correctedKernelBound_pos.le
  have hiE := (lowBand_energy_norm_integrable j B hB g).const_mul B
  have hiS := (lowBand_sqrt_energy_norm_integrable j B g).const_mul (sqrt B)
  rw [(correctedKernelRowResponse_pairing j J B g f).2]
  calc
    _ ≤ ∫ e, correctedKernelBound * ‖f‖ *
        (B * (e * ‖g e‖) + sqrt B * (sqrt e * ‖g e‖))
        ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| B) := by
      apply norm_integral_le_of_norm_le ((hiE.add hiS).const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with e he
      rw [norm_mul, RCLike.norm_conj]
      dsimp only [Pi.add_apply]
      calc
        _ ≤ ‖g e‖ * (correctedKernelBound * (e * B + sqrt e * sqrt B) * ‖f‖) :=
          mul_le_mul_of_nonneg_left (norm_correctedKernelRowResponse_le j J B hB f e he.1.le)
            (norm_nonneg _)
        _ = _ := by ring
    _ = correctedKernelBound * ‖f‖ *
        (B * (∫ e, e * ‖g e‖ ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) +
          sqrt B * (∫ e, sqrt e * ‖g e‖ ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| B))) := by
      rw [integral_const_mul, integral_add hiE hiS, integral_const_mul, integral_const_mul]
    _ ≤ correctedKernelBound * ‖f‖ * (B * (B * ‖g‖) + sqrt B * (sqrt B * ‖g‖)) := by
      gcongr
      · exact lowBand_energy_norm_integral_le j B hB g
      · exact lowBand_sqrt_energy_norm_integral_le j B hB g
    _ = correctedKernelBound * (B ^ 2 + (sqrt B) ^ 2) * ‖g‖ * ‖f‖ := by ring
    _ = _ := by rw [sq_sqrt hB]

/-- The full operator's sesquilinear form has a quadratic band bound and
only a linear loss in the number of rows. -/
theorem norm_inner_correctedLowBandOperator_le_moment
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B)
    (g f : LowBandHilbert J B) :
    ‖inner ℂ g (correctedLowBandOperator J B f)‖ ≤
      correctedKernelBound * (B ^ 2 + B) * (Fintype.card ι : ℝ) * ‖g‖ * ‖f‖ := by
  have hC := correctedKernelBound_pos.le
  have hA : 0 ≤ correctedKernelBound * (B ^ 2 + B) := by positivity
  rw [inner_correctedLowBandOperator]
  calc
    _ ≤ ∑ i, ‖∑ l, lowBandKernelPairing (J i) (J l) B
        (fun p => correctedKernel (J i) (J l) p.1 p.2) (g i) (f l)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ∑ l, ‖lowBandKernelPairing (J i) (J l) B
        (fun p => correctedKernel (J i) (J l) p.1 p.2) (g i) (f l)‖ :=
      Finset.sum_le_sum fun i _ => norm_sum_le _ _
    _ ≤ ∑ i, ∑ l, correctedKernelBound * (B ^ 2 + B) * ‖g i‖ * ‖f l‖ := by
      exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun l _ =>
        norm_correctedKernel_lowBandPairing_le_moment (J i) (J l) B hB (g i) (f l)
    _ = correctedKernelBound * (B ^ 2 + B) * (∑ i, ‖g i‖) * (∑ l, ‖f l‖) := by
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ ≤ correctedKernelBound * (B ^ 2 + B) *
        (sqrt (Fintype.card ι : ℝ) * ‖g‖) * (sqrt (Fintype.card ι : ℝ) * ‖f‖) := by
      gcongr
      · exact lowBandHilbert_sum_norm_le J B g
      · exact lowBandHilbert_sum_norm_le J B f
    _ = correctedKernelBound * (B ^ 2 + B) * (sqrt (Fintype.card ι : ℝ)) ^ 2 * ‖g‖ * ‖f‖ := by ring
    _ = _ := by rw [sq_sqrt (Nat.cast_nonneg _)]

/-- A polynomial norm bound for the actual full corrected operator; repeated
spin rows are allowed. -/
theorem norm_correctedLowBandOperator_le_moment
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) :
    ‖correctedLowBandOperator J B‖ ≤
      correctedKernelBound * (B ^ 2 + B) * (Fintype.card ι : ℝ) := by
  have hC := correctedKernelBound_pos.le
  apply ContinuousLinearMap.opNorm_le_of_re_inner_le (by positivity)
  intro f g hf hg
  rw [inner_re_symm]
  exact (Complex.re_le_norm _).trans
    (by simpa only [hf, hg, mul_one] using norm_inner_correctedLowBandOperator_le_moment J B hB g f)

end GapFamily.Analytic
