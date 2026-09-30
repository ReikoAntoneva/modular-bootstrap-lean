import GapFamily.Analytic.Kernel.FullKernelOperator
import GapFamily.Analytic.Kernel.HigherKernelSmoothingNorm
import GapFamily.Analytic.Kernel.FullKernelSmoothingMoment

/-!
# Ordinary smoothing by the full corrected kernel

The response uses the actual central, higher and scalar rank-one terms.
Energy and square-root energy moments supply ordinary domination at the
scalar origin; finite scalar reference mass is never assumed.
-/

noncomputable section

open MeasureTheory Real Set
open scoped BigOperators ComplexConjugate

namespace GapFamily.Analytic

/-- The ordinary response of the full corrected kernel to one input row. -/
def correctedKernelRowResponse (j J : ℤ) (B : ℝ) (f : LowBandRow J B) (e : ℝ) : ℂ :=
  ∫ E, correctedKernel j J e E * f E
    ∂(referenceMeasure J).restrict (Ioo |(J : ℝ)| B)

/-- The full corrected response of a finite collection of physical input rows. -/
def correctedKernelResponse {ι : Type*} [Fintype ι] (J : ι → ℤ) (B : ℝ)
    (f : LowBandHilbert J B) (j : ℤ) (e : ℝ) : ℂ :=
  ∑ i, correctedKernelRowResponse j (J i) B (f i) e

theorem correctedKernelRowResponse_stronglyMeasurable (j J : ℤ) (B : ℝ)
    (f : LowBandRow J B) : StronglyMeasurable (correctedKernelRowResponse j J B f) := by
  exact ((continuous_correctedKernel j J).stronglyMeasurable.mul
    ((Lp.stronglyMeasurable f).comp_measurable measurable_snd)).integral_prod_right'

theorem correctedKernelResponse_stronglyMeasurable {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (f : LowBandHilbert J B) (j : ℤ) :
    StronglyMeasurable (correctedKernelResponse J B f j) := by
  exact Finset.stronglyMeasurable_fun_sum Finset.univ
    (fun i _ => correctedKernelRowResponse_stronglyMeasurable j (J i) B (f i))

theorem correctedKernelRowResponse_integrable (j J : ℤ) (B : ℝ) (hB : 0 ≤ B)
    (f : LowBandRow J B) (e : ℝ) (he : |(j : ℝ)| ≤ e) :
    Integrable (fun E => correctedKernel j J e E * f E)
      ((referenceMeasure J).restrict (Ioo |(J : ℝ)| B)) := by
  have he0 : 0 ≤ e := (abs_nonneg _).trans he
  have hC := correctedKernelBound_pos
  have hm : AEStronglyMeasurable (fun E => correctedKernel j J e E * f E)
      ((referenceMeasure J).restrict (Ioo |(J : ℝ)| B)) :=
    ((continuous_correctedKernel j J).comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable.mul (Lp.aestronglyMeasurable f)
  apply (((lowBand_energy_norm_integrable J B hB f).const_mul e).add
    ((lowBand_sqrt_energy_norm_integrable J B f).const_mul (sqrt e))).const_mul
      correctedKernelBound |>.mono' hm
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with E hE
  rw [norm_mul]
  calc
    _ ≤ (correctedKernelBound * (|(j : ℝ)| * |(J : ℝ)| + sqrt e * sqrt E)) * ‖f E‖ :=
      mul_le_mul_of_nonneg_right (norm_correctedKernel_le j J e E he hE.1.le) (norm_nonneg _)
    _ ≤ (correctedKernelBound * (e * E + sqrt e * sqrt E)) * ‖f E‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul he hE.1.le (abs_nonneg _) he0) le_rfl) hC.le)
          (norm_nonneg _)
    _ = _ := by dsimp only [Pi.add_apply]; ring

/-- The actual row response has an energy plus square-root energy majorant. -/
theorem norm_correctedKernelRowResponse_le (j J : ℤ) (B : ℝ) (hB : 0 ≤ B)
    (f : LowBandRow J B) (e : ℝ) (he : |(j : ℝ)| ≤ e) :
    ‖correctedKernelRowResponse j J B f e‖ ≤
      correctedKernelBound * (e * B + sqrt e * sqrt B) * ‖f‖ := by
  have he0 : 0 ≤ e := (abs_nonneg _).trans he
  have hC := correctedKernelBound_pos
  have hiE := lowBand_energy_norm_integrable J B hB f
  have hiS := lowBand_sqrt_energy_norm_integrable J B f
  calc
    _ ≤ ∫ E, correctedKernelBound *
        (e * (E * ‖f E‖) + sqrt e * (sqrt E * ‖f E‖))
        ∂(referenceMeasure J).restrict (Ioo |(J : ℝ)| B) := by
      apply norm_integral_le_of_norm_le (((hiE.const_mul e).add
        (hiS.const_mul (sqrt e))).const_mul correctedKernelBound)
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with E hE
      rw [norm_mul]
      calc
        _ ≤ (correctedKernelBound * (|(j : ℝ)| * |(J : ℝ)| + sqrt e * sqrt E)) * ‖f E‖ :=
          mul_le_mul_of_nonneg_right (norm_correctedKernel_le j J e E he hE.1.le) (norm_nonneg _)
        _ ≤ (correctedKernelBound * (e * E + sqrt e * sqrt E)) * ‖f E‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (add_le_add (mul_le_mul he hE.1.le (abs_nonneg _) he0) le_rfl) hC.le)
              (norm_nonneg _)
        _ = _ := by dsimp only [Pi.add_apply]; ring
    _ = correctedKernelBound *
        (e * (∫ E, E * ‖f E‖ ∂(referenceMeasure J).restrict (Ioo |(J : ℝ)| B)) +
          sqrt e * (∫ E, sqrt E * ‖f E‖ ∂(referenceMeasure J).restrict (Ioo |(J : ℝ)| B))) := by
      rw [integral_const_mul, integral_add (hiE.const_mul e) (hiS.const_mul (sqrt e)),
        integral_const_mul, integral_const_mul]
    _ ≤ correctedKernelBound * (e * (B * ‖f‖) + sqrt e * (sqrt B * ‖f‖)) := by
      gcongr
      · exact lowBand_energy_norm_integral_le J B hB f
      · exact lowBand_sqrt_energy_norm_integral_le J B hB f
    _ = _ := by ring

/-- Finite-spin Hilbert Cauchy controls the full physical response. -/
theorem norm_correctedKernelResponse_le {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (f : LowBandHilbert J B)
    (j : ℤ) (e : ℝ) (he : |(j : ℝ)| ≤ e) :
    ‖correctedKernelResponse J B f j e‖ ≤
      correctedKernelBound * (e * B + sqrt e * sqrt B) *
        sqrt (Fintype.card ι : ℝ) * ‖f‖ := by
  have he0 : 0 ≤ e := (abs_nonneg _).trans he
  have hC := correctedKernelBound_pos
  calc
    _ ≤ ∑ i, ‖correctedKernelRowResponse j (J i) B (f i) e‖ := norm_sum_le _ _
    _ ≤ ∑ i, (correctedKernelBound * (e * B + sqrt e * sqrt B)) * ‖f i‖ :=
      Finset.sum_le_sum fun i _ => norm_correctedKernelRowResponse_le j (J i) B hB (f i) e he
    _ = (correctedKernelBound * (e * B + sqrt e * sqrt B)) * ∑ i, ‖f i‖ :=
      (Finset.mul_sum ..).symm
    _ ≤ (correctedKernelBound * (e * B + sqrt e * sqrt B)) *
        (sqrt (Fintype.card ι : ℝ) * ‖f‖) :=
      mul_le_mul_of_nonneg_left (lowBandHilbert_sum_norm_le J B f) (by positivity)
    _ = _ := by ring

/-- Ordinary `L¹` smoothing, including the infinite-mass scalar input and output rows. -/
theorem correctedKernelResponse_integrable_lowBand {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (f : LowBandHilbert J B) (j : ℤ) :
    Integrable (correctedKernelResponse J B f j)
      ((referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) := by
  apply (((((lowBand_energy_integrable j B).mul_const B).add
    ((lowBand_sqrt_energy_integrable j B).mul_const (sqrt B))).const_mul correctedKernelBound).mul_const (sqrt (Fintype.card ι : ℝ))).mul_const ‖f‖ |>.mono'
        (correctedKernelResponse_stronglyMeasurable J B f j).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with e he
  exact norm_correctedKernelResponse_le J B hB f j e he.1.le

/-- A uniform ordinary mass coefficient for one output row. -/
def correctedSmoothingBound (B : ℝ) : ℝ :=
  correctedKernelBound * (B ^ 2 + sqrt B * (B + 2 * sqrt B))

theorem correctedSmoothingBound_nonneg (B : ℝ) (hB : 0 ≤ B) :
    0 ≤ correctedSmoothingBound B := by
  have hC := correctedKernelBound_pos
  unfold correctedSmoothingBound
  positivity

theorem integral_norm_correctedKernelResponse_lowBand_le {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (f : LowBandHilbert J B) (j : ℤ) :
    (∫ e, ‖correctedKernelResponse J B f j e‖
      ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) ≤
        correctedSmoothingBound B * sqrt (Fintype.card ι : ℝ) * ‖f‖ := by
  have hC := correctedKernelBound_pos
  have hiE := (lowBand_energy_integrable j B).mul_const B
  have hiS := (lowBand_sqrt_energy_integrable j B).mul_const (sqrt B)
  calc
    _ ≤ ∫ e, correctedKernelBound * (e * B + sqrt e * sqrt B) *
        sqrt (Fintype.card ι : ℝ) * ‖f‖
        ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| B) := by
      apply integral_mono_ae (correctedKernelResponse_integrable_lowBand J B hB f j).norm
        (((hiE.add hiS).const_mul correctedKernelBound).mul_const _ |>.mul_const _)
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with e he
      exact norm_correctedKernelResponse_le J B hB f j e he.1.le
    _ = correctedKernelBound *
        ((∫ e, e ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) * B +
          (∫ e, sqrt e ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) * sqrt B) *
        sqrt (Fintype.card ι : ℝ) * ‖f‖ := by
      rw [integral_mul_const, integral_mul_const, integral_const_mul,
        integral_add hiE hiS, integral_mul_const, integral_mul_const]
    _ ≤ correctedKernelBound * (B * B + (B + 2 * sqrt B) * sqrt B) *
        sqrt (Fintype.card ι : ℝ) * ‖f‖ := by
      gcongr
      · exact ((by
          by_cases hj : |(j : ℝ)| ≤ B
          · rw [lowBand_integral_energy j hj]
            exact (Real.sqrt_le_left hB).mpr (by nlinarith [sq_nonneg (j : ℝ)])
          · simp [Ioo_eq_empty_of_le (le_of_not_ge hj), hB]) :
            (∫ e, e ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) ≤ B)
      · exact lowBand_integral_sqrt_energy_le j B hB
    _ = _ := by unfold correctedSmoothingBound; ring

/-- The same ordinary response also belongs to the physical Hilbert row. -/
theorem correctedKernelResponse_memLp_lowBand {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (f : LowBandHilbert J B) (j : ℤ) :
    MemLp (correctedKernelResponse J B f j) 2
      ((referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) := by
  have hM := ((((lowBand_energy_memLp j B hB).mul_const B).add
    ((lowBand_sqrt_energy_memLp j B).mul_const (sqrt B))).const_mul correctedKernelBound).mul_const (sqrt (Fintype.card ι : ℝ)) |>.mul_const ‖f‖
  apply hM.of_le (correctedKernelResponse_stronglyMeasurable J B f j).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with e he
  have he0 : 0 ≤ e := (abs_nonneg _).trans he.1.le
  have hC := correctedKernelBound_pos
  dsimp only [Pi.add_apply]
  rw [Real.norm_of_nonneg (by positivity)]
  exact norm_correctedKernelResponse_le J B hB f j e he.1.le

/-- The full response as an actual Hilbert vector. -/
def correctedKernelResponseHilbert {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (f : LowBandHilbert J B) : LowBandHilbert J B :=
  WithLp.toLp 2 (fun i => (correctedKernelResponse_memLp_lowBand J B hB f (J i)).toLp
    (correctedKernelResponse J B f (J i)))

theorem correctedKernelResponseHilbert_coeFn {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (f : LowBandHilbert J B) (i : ι) :
    ⇑(correctedKernelResponseHilbert J B hB f i) =ᵐ[
      (referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B)]
        correctedKernelResponse J B f (J i) :=
  (correctedKernelResponse_memLp_lowBand J B hB f (J i)).coeFn_toLp

/-- Ordinary Fubini identifies the response with the actual compressed pairing. -/
theorem correctedKernelRowResponse_pairing (j J : ℤ) (B : ℝ)
    (g : LowBandRow j B) (f : LowBandRow J B) :
    Integrable (fun e => conj (g e) * correctedKernelRowResponse j J B f e)
      ((referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) ∧
    lowBandKernelPairing j J B (fun p => correctedKernel j J p.1 p.2) g f =
      ∫ e, conj (g e) * correctedKernelRowResponse j J B f e
        ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| B) := by
  have hi := correctedKernel_lowBand_integrable j J B g f
  have heq : (fun e : ℝ => ∫ E,
      weakKernelIntegrand (fun p => correctedKernel j J p.1 p.2) g f (e, E)
        ∂(referenceMeasure J).restrict (Ioo |(J : ℝ)| B)) =
      (fun e : ℝ => conj (g e) * correctedKernelRowResponse j J B f e) := by
    funext e
    rw [correctedKernelRowResponse, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with E
    simp only [weakKernelIntegrand]
    ring
  refine ⟨heq ▸ hi.integral_prod_left, ?_⟩
  rw [lowBandKernelPairing, integral_prod _ hi, heq]

theorem inner_correctedLowBandOperator_response {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (g f : LowBandHilbert J B) :
    inner ℂ g (correctedLowBandOperator J B f) =
      ∑ i, ∫ e, conj (g i e) * correctedKernelResponse J B f (J i) e
        ∂(referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B) := by
  rw [inner_correctedLowBandOperator]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [correctedKernelResponse, Finset.mul_sum]
  rw [integral_finsetSum Finset.univ (fun l _ =>
    (correctedKernelRowResponse_pairing (J i) (J l) B (g i) (f l)).1)]
  exact Finset.sum_congr rfl fun l _ =>
    (correctedKernelRowResponse_pairing (J i) (J l) B (g i) (f l)).2

/-- The bounded full-kernel operator is represented by the proved ordinary response. -/
theorem correctedLowBandOperator_eq_responseHilbert {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (f : LowBandHilbert J B) :
    correctedLowBandOperator J B f = correctedKernelResponseHilbert J B hB f := by
  apply ext_inner_left ℂ
  intro g
  rw [inner_correctedLowBandOperator_response, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [correctedKernelResponseHilbert_coeFn J B hB f i] with e he
  simp only [RCLike.inner_apply', he]

theorem correctedLowBandOperator_coeFn {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (f : LowBandHilbert J B) (i : ι) :
    ⇑(correctedLowBandOperator J B f i) =ᵐ[
      (referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B)]
        correctedKernelResponse J B f (J i) := by
  rw [correctedLowBandOperator_eq_responseHilbert J B hB f]
  exact correctedKernelResponseHilbert_coeFn J B hB f i

/-- Genuine ordinary `L¹` smoothing of the full low-band Hilbert operator. -/
theorem correctedLowBandOperator_integrable {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (f : LowBandHilbert J B) (i : ι) :
    Integrable (correctedLowBandOperator J B f i)
      ((referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B)) :=
  (correctedKernelResponse_integrable_lowBand J B hB f (J i)).congr
    (correctedLowBandOperator_coeFn J B hB f i).symm

/-- Zero extension is integrable against the full physical reference measure. -/
theorem correctedLowBandOperator_zeroExtension_integrable
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B)
    (f : LowBandHilbert J B) (i : ι) :
    Integrable ((Ioo |(J i : ℝ)| B).indicator (correctedLowBandOperator J B f i))
      (referenceMeasure (J i)) :=
  (integrable_indicator_iff measurableSet_Ioo).mpr
    (correctedLowBandOperator_integrable J B hB f i)

/-- Summed ordinary mass of the full corrected compression. -/
theorem sum_integral_norm_correctedLowBandOperator_le
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B)
    (f : LowBandHilbert J B) :
    (∑ i, ∫ e, ‖correctedLowBandOperator J B f i e‖
      ∂(referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B)) ≤
        (Fintype.card ι : ℝ) * correctedSmoothingBound B *
          sqrt (Fintype.card ι : ℝ) * ‖f‖ := by
  calc
    _ = ∑ i, ∫ e, ‖correctedKernelResponse J B f (J i) e‖
        ∂(referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply integral_congr_ae
      filter_upwards [correctedLowBandOperator_coeFn J B hB f i] with e he
      exact congrArg norm he
    _ ≤ ∑ _ : ι, correctedSmoothingBound B * sqrt (Fintype.card ι : ℝ) * ‖f‖ :=
      Finset.sum_le_sum fun i _ => integral_norm_correctedKernelResponse_lowBand_le J B hB f (J i)
    _ = _ := by simp; ring

/-- The full central-plus-higher-plus-rank-one smoothing coefficient is quadratic
on bands of width at least one. -/
theorem correctedSmoothingBound_le (B : ℝ) (hB : 1 ≤ B) :
    correctedSmoothingBound B ≤ 4 * correctedKernelBound * B ^ 2 := by
  have hB0 : 0 ≤ B := le_trans zero_le_one hB
  have hs : sqrt B ≤ B := Real.sqrt_le_self_iff.mpr (Or.inr hB)
  have hC := correctedKernelBound_pos
  have hsq := Real.sq_sqrt hB0
  unfold correctedSmoothingBound
  calc
    _ = correctedKernelBound * (B ^ 2 + B * sqrt B + 2 * B) := by
      congr 1
      nlinarith [hsq]
    _ ≤ correctedKernelBound * (4 * B ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      nlinarith [mul_le_mul_of_nonneg_left hs hB0]
    _ = _ := by ring

/-- The source's `B^(7/2)` ordinary smoothing scale holds for the full corrected
kernel on every finite collection of distinct physical spin rows. -/
theorem sum_integral_norm_correctedLowBandOperator_le_physical
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (hJ : Function.Injective J)
    (B : ℝ) (hB : 1 ≤ B) (hband : ∀ i, |(J i : ℝ)| < B)
    (f : LowBandHilbert J B) :
    (∑ i, ∫ e, ‖correctedLowBandOperator J B f i e‖
      ∂(referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B)) ≤
        20 * correctedKernelBound * sqrt 5 * B ^ 3 * sqrt B * ‖f‖ := by
  have hB0 : 0 ≤ B := le_trans zero_le_one hB
  have hC := correctedKernelBound_pos
  have hcard := physicalLowBand_card_le J hJ hB hband
  calc
    _ ≤ (Fintype.card ι : ℝ) * correctedSmoothingBound B *
        sqrt (Fintype.card ι : ℝ) * ‖f‖ :=
      sum_integral_norm_correctedLowBandOperator_le J B hB0 f
    _ ≤ (5 * B) * (4 * correctedKernelBound * B ^ 2) * sqrt (5 * B) * ‖f‖ := by
      gcongr
      · exact correctedSmoothingBound_nonneg B hB0
      · exact correctedSmoothingBound_le B hB
    _ = _ := by rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 5)]; ring

end GapFamily.Analytic
