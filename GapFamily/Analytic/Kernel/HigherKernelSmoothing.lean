import GapFamily.Analytic.Kernel.HigherKernelResponse
import GapFamily.Analytic.Kernel.HigherKernelSmoothingNorm

/-!
# Ordinary low-band smoothing by the actual higher kernel

The physical estimate retains a factor of output energy. This factor makes
the scalar response ordinarily integrable against `dE/E`, and the exact
reference-energy moment controls every nonzero threshold as well.
The continued zero-order term and scalar rank-one correction are excluded.
-/

noncomputable section

open MeasureTheory Real Set
open scoped BigOperators ComplexConjugate

namespace GapFamily.Analytic

/-- The first reference-energy moment is bounded uniformly in every spin,
including scalar spin and the empty band. -/
theorem lowBand_integral_energy_le (j : ℤ) (B : ℝ) (hB : 0 ≤ B) :
    (∫ e, e ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) ≤ B := by
  by_cases hj : |(j : ℝ)| ≤ B
  · rw [lowBand_integral_energy j hj]
    exact (Real.sqrt_le_left hB).mpr (by nlinarith [sq_nonneg (j : ℝ)])
  · simp [Ioo_eq_empty_of_le (le_of_not_ge hj), hB]

/-- The actual physical row response retains its linear output-energy zero. -/
theorem norm_higherKernelRowResponse_physical_le (j J : ℤ) (B : ℝ)
    (hB : 0 < B) (f : LowBandRow J B) (e : ℝ) (he : |(j : ℝ)| ≤ e) :
    ‖higherKernelRowResponse j J B f e‖ ≤ 32 * π ^ 2 * e * B * ‖f‖ := by
  have he0 : 0 ≤ e := (abs_nonneg _).trans he
  calc
    _ ≤ ∫ E, (32 * π ^ 2 * e) * (E * ‖f E‖)
        ∂(referenceMeasure J).restrict (Ioo |(J : ℝ)| B) := by
      apply norm_integral_le_of_norm_le
        ((lowBand_energy_norm_integrable J B hB.le f).const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with E hE
      rw [norm_mul]
      calc
        _ ≤ (32 * π ^ 2 * (e * E)) * ‖f E‖ :=
          mul_le_mul_of_nonneg_right
            (norm_higherKernel_physical_le_mul j J e E he hE.1.le) (norm_nonneg _)
        _ = _ := by ring
    _ = (32 * π ^ 2 * e) *
        ∫ E, E * ‖f E‖ ∂(referenceMeasure J).restrict (Ioo |(J : ℝ)| B) :=
      integral_const_mul _ _
    _ ≤ (32 * π ^ 2 * e) * (B * ‖f‖) :=
      mul_le_mul_of_nonneg_left (lowBand_energy_norm_integral_le J B hB.le f)
        (by positivity)
    _ = _ := by ring

/-- Finite-spin Hilbert Cauchy bounds the actual physical response without
assuming that any scalar input has finite ordinary mass. -/
theorem norm_higherKernelResponse_physical_le {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 < B) (f : LowBandHilbert J B)
    (j : ℤ) (e : ℝ) (he : |(j : ℝ)| ≤ e) :
    ‖higherKernelResponse J B f j e‖ ≤
      32 * π ^ 2 * e * B * sqrt (Fintype.card ι) * ‖f‖ := by
  have he0 : 0 ≤ e := (abs_nonneg _).trans he
  calc
    _ ≤ ∑ i, ‖higherKernelRowResponse j (J i) B (f i) e‖ := norm_sum_le _ _
    _ ≤ ∑ i, (32 * π ^ 2 * e * B) * ‖f i‖ :=
      Finset.sum_le_sum fun i _ => norm_higherKernelRowResponse_physical_le
        j (J i) B hB (f i) e he
    _ = (32 * π ^ 2 * e * B) * ∑ i, ‖f i‖ := (Finset.mul_sum ..).symm
    _ ≤ (32 * π ^ 2 * e * B) * (sqrt (Fintype.card ι) * ‖f‖) :=
      mul_le_mul_of_nonneg_left (lowBandHilbert_sum_norm_le J B f) (by positivity)
    _ = _ := by ring

/-- The actual physical response is measurable as a restriction of the entire response. -/
theorem higherKernelResponse_real_continuous {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 < B) (f : LowBandHilbert J B) (j : ℤ) :
    Continuous (fun e : ℝ => higherKernelResponse J B f j e) := by
  simpa only [Function.comp_def] using
    (differentiable_higherKernelResponse J B hB f j).continuous.comp Complex.continuous_ofReal

/-- Genuine ordinary `L¹` smoothing on each open physical band. -/
theorem higherKernelResponse_integrable_lowBand {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 < B) (f : LowBandHilbert J B) (j : ℤ) :
    Integrable (fun e : ℝ => higherKernelResponse J B f j e)
      ((referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) := by
  let C : ℝ := 32 * π ^ 2 * B * sqrt (Fintype.card ι) * ‖f‖
  apply ((lowBand_energy_integrable j B).const_mul C).mono'
    (higherKernelResponse_real_continuous J B hB f j).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with e he
  exact (norm_higherKernelResponse_physical_le J B hB f j e he.1.le).trans_eq (by dsimp [C]; ring)

/-- Uniform ordinary mass bound for a response row, with the scalar origin and
all nonzero-spin square-root edges covered by the same energy moment. -/
theorem integral_norm_higherKernelResponse_lowBand_le {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 < B) (f : LowBandHilbert J B) (j : ℤ) :
    (∫ e, ‖higherKernelResponse J B f j e‖
      ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) ≤
        32 * π ^ 2 * B ^ 2 * sqrt (Fintype.card ι) * ‖f‖ := by
  let C : ℝ := 32 * π ^ 2 * B * sqrt (Fintype.card ι) * ‖f‖
  have hC : 0 ≤ C := by dsimp [C]; positivity
  calc
    _ ≤ ∫ e, C * e ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| B) := by
      apply integral_mono_ae (higherKernelResponse_integrable_lowBand J B hB f j).norm
        ((lowBand_energy_integrable j B).const_mul C)
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with e he
      exact (norm_higherKernelResponse_physical_le J B hB f j e he.1.le).trans_eq
        (by dsimp [C]; ring)
    _ = C * ∫ e, e ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| B) := integral_const_mul _ _
    _ ≤ C * B := mul_le_mul_of_nonneg_left (lowBand_integral_energy_le j B hB.le) hC
    _ = _ := by dsimp [C]; ring

/-- Summed ordinary mass on any finite output spin family. The input and output
cardinalities remain explicit, so repeated or empty spin families are allowed. -/
theorem sum_integral_norm_higherKernelResponse_lowBand_le
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (J : ι → ℤ) (j : κ → ℤ) (B : ℝ) (hB : 0 < B) (f : LowBandHilbert J B) :
    (∑ k, ∫ e, ‖higherKernelResponse J B f (j k) e‖
      ∂(referenceMeasure (j k)).restrict (Ioo |(j k : ℝ)| B)) ≤
        (Fintype.card κ : ℝ) *
          (32 * π ^ 2 * B ^ 2 * sqrt (Fintype.card ι)) * ‖f‖ := by
  calc
    _ ≤ ∑ k : κ, 32 * π ^ 2 * B ^ 2 * sqrt (Fintype.card ι) * ‖f‖ :=
      Finset.sum_le_sum fun k _ => integral_norm_higherKernelResponse_lowBand_le J B hB f (j k)
    _ = _ := by simp; ring

/-- The same vanishing response is an actual low-band Hilbert vector. -/
theorem higherKernelResponse_memLp_lowBand {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 < B) (f : LowBandHilbert J B) (j : ℤ) :
    MemLp (fun e : ℝ => higherKernelResponse J B f j e) 2
      ((referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) := by
  let C : ℝ := 32 * π ^ 2 * B * sqrt (Fintype.card ι) * ‖f‖
  apply (lowBand_energy_memLp j B hB.le).of_le_mul
    (c := C) (higherKernelResponse_real_continuous J B hB f j).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with e he
  have he0 : 0 ≤ e := (abs_nonneg _).trans he.1.le
  rw [Real.norm_eq_abs, abs_of_nonneg he0]
  exact (norm_higherKernelResponse_physical_le J B hB f j e he.1.le).trans_eq (by dsimp [C]; ring)

/-- The Hilbert equivalence class of the actual ordinary response. -/
def higherKernelResponseHilbert {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 < B) (f : LowBandHilbert J B) : LowBandHilbert J B :=
  WithLp.toLp 2 (fun i => (higherKernelResponse_memLp_lowBand J B hB f (J i)).toLp
    (fun e : ℝ => higherKernelResponse J B f (J i) e))

theorem higherKernelResponseHilbert_coeFn {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 < B) (f : LowBandHilbert J B) (i : ι) :
    ⇑(higherKernelResponseHilbert J B hB f i) =ᵐ[
      (referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B)]
        (fun e : ℝ => higherKernelResponse J B f (J i) e) :=
  (higherKernelResponse_memLp_lowBand J B hB f (J i)).coeFn_toLp

/-- Ordinary Fubini identifies the previously constructed Riesz operator with
the actual Hilbert response, not merely with an abstract representative. -/
theorem higherKernelLowBandOperator_eq_responseHilbert {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 < B) (f : LowBandHilbert J B) :
    higherKernelLowBandOperator J B f = higherKernelResponseHilbert J B hB f := by
  apply ext_inner_left ℂ
  intro g
  rw [inner_higherKernelLowBandOperator, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [higherKernelResponseHilbert_coeFn J B hB f i] with e he
  simp only [RCLike.inner_apply', he]

/-- The actual bounded higher-kernel operator has the proved ordinary response
as representative in every row. -/
theorem higherKernelLowBandOperator_coeFn {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 < B) (f : LowBandHilbert J B) (i : ι) :
    ⇑(higherKernelLowBandOperator J B f i) =ᵐ[
      (referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B)]
        (fun e : ℝ => higherKernelResponse J B f (J i) e) := by
  rw [higherKernelLowBandOperator_eq_responseHilbert J B hB f]
  exact higherKernelResponseHilbert_coeFn J B hB f i

/-- Genuine ordinary `L¹` smoothing for the actual Hilbert operator itself. -/
theorem higherKernelLowBandOperator_integrable {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 < B) (f : LowBandHilbert J B) (i : ι) :
    Integrable (higherKernelLowBandOperator J B f i)
      ((referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B)) :=
  (higherKernelResponse_integrable_lowBand J B hB f (J i)).congr
    (higherKernelLowBandOperator_coeFn J B hB f i).symm

/-- Zero extension gives an ordinarily integrable numerator on the full
physical row, as required before forming a finite ordinary density measure. -/
theorem higherKernelLowBandOperator_zeroExtension_integrable
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (B : ℝ) (hB : 0 < B)
    (f : LowBandHilbert J B) (i : ι) :
    Integrable ((Ioo |(J i : ℝ)| B).indicator (higherKernelLowBandOperator J B f i))
      (referenceMeasure (J i)) :=
  (integrable_indicator_iff measurableSet_Ioo).mpr
    (higherKernelLowBandOperator_integrable J B hB f i)

/-- Total ordinary mass of the actual higher-kernel compression. -/
theorem sum_integral_norm_higherKernelLowBandOperator_le
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (B : ℝ) (hB : 0 < B) (f : LowBandHilbert J B) :
    (∑ i, ∫ e, ‖higherKernelLowBandOperator J B f i e‖
      ∂(referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B)) ≤
        (Fintype.card ι : ℝ) *
          (32 * π ^ 2 * B ^ 2 * sqrt (Fintype.card ι)) * ‖f‖ := by
  convert sum_integral_norm_higherKernelResponse_lowBand_le J J B hB f using 1
  apply Finset.sum_congr rfl
  intro i hi
  apply integral_congr_ae
  filter_upwards [higherKernelLowBandOperator_coeFn J B hB f i] with e he
  exact congrArg norm he

/-- The source's `B^(7/2)` ordinary-mass scale for every distinct finite
physical spin family. The spin-count estimate is proved internally. -/
theorem sum_integral_norm_higherKernelLowBandOperator_le_physical
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (hJ : Function.Injective J)
    (B : ℝ) (hB : 1 ≤ B) (hband : ∀ i, |(J i : ℝ)| < B) (f : LowBandHilbert J B) :
    (∑ i, ∫ e, ‖higherKernelLowBandOperator J B f i e‖
      ∂(referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B)) ≤
        160 * π ^ 2 * sqrt 5 * B ^ 3 * sqrt B * ‖f‖ := by
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hcard := physicalLowBand_card_le J hJ hB hband
  calc
    _ ≤ (Fintype.card ι : ℝ) *
        (32 * π ^ 2 * B ^ 2 * sqrt (Fintype.card ι)) * ‖f‖ :=
      sum_integral_norm_higherKernelLowBandOperator_le J B hB0 f
    _ ≤ (5 * B) * (32 * π ^ 2 * B ^ 2 * sqrt (5 * B)) * ‖f‖ := by
      gcongr
    _ = _ := by rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 5)]; ring

end GapFamily.Analytic
