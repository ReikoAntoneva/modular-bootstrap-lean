import GapFamily.Analytic.Kernel.FullKernelSmoothing
import GapFamily.Analytic.Foundation.SignedMomentIntegral

/-!
# Ordinary smoothing of a compact signed seed

The seed is integrated against its actual signed measure. All input bounds
use its variation, while the output lies in the physical ordinary `L¹` and
`L²` spaces, including the scalar row with reference measure `dE/E`.
-/

noncomputable section

open MeasureTheory Real Set
open scoped BigOperators

namespace GapFamily.Analytic

/-- The full corrected response of one genuine signed input measure. -/
def correctedSignedRowResponse (ν : SignedMeasure ℝ) (J j : ℤ) (e : ℝ) : ℂ :=
  ∫ᵛ E, correctedKernel j J e E ∂<•ν

/-- Compact physical support makes every kernel slice ordinarily integrable,
even for observation energies outside the physical half-line. -/
theorem correctedSignedRowResponse_integrable (ν : SignedMeasure ℝ) (J j : ℤ)
    (M : ℝ) (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ M) (e : ℝ) :
    ν.Integrable (fun E => correctedKernel j J e E) := by
  let := signedMeasure_isFiniteMeasure_variation ν
  have hpair : Continuous (fun E : ℝ => (e, E)) := continuous_const.prodMk continuous_id
  have hc := (continuous_correctedKernel j J).comp hpair
  have hi := hc.integrableOn_Icc (μ := ν.variation) (a := |(J : ℝ)|) (b := M)
  have hr : ν.variation.restrict (Icc |(J : ℝ)| M) = ν.variation :=
    Measure.restrict_eq_self_of_ae_mem hs
  rw [IntegrableOn, hr] at hi
  exact hi

/-- Jordan decomposition realizes the signed response as the difference of
two measurable ordinary parameter integrals. -/
theorem correctedSignedRowResponse_stronglyMeasurable (ν : SignedMeasure ℝ)
    (J j : ℤ) (M : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ M) :
    StronglyMeasurable (correctedSignedRowResponse ν J j) := by
  have heq : correctedSignedRowResponse ν J j = fun e =>
      (∫ E, correctedKernel j J e E ∂ν.toJordanDecomposition.posPart) -
        ∫ E, correctedKernel j J e E ∂ν.toJordanDecomposition.negPart := by
    funext e
    exact signedIntegral_eq_jordan (correctedSignedRowResponse_integrable ν J j M hs e)
  rw [heq]
  exact (continuous_correctedKernel j J).stronglyMeasurable.integral_prod_right'.sub
    (continuous_correctedKernel j J).stronglyMeasurable.integral_prod_right'

private theorem correctedKernel_seed_bound (J j : ℤ) (M e E : ℝ)
    (he : |(j : ℝ)| ≤ e) (hE : |(J : ℝ)| ≤ E ∧ E ≤ M) :
    ‖correctedKernel j J e E‖ ≤ correctedKernelBound * (e * M + sqrt e * sqrt M) := by
  have he0 := (abs_nonneg (j : ℝ)).trans he
  have hE0 := (abs_nonneg (J : ℝ)).trans hE.1
  have hC := correctedKernelBound_pos
  calc
    _ ≤ correctedKernelBound * (|(j : ℝ)| * |(J : ℝ)| + sqrt e * sqrt E) :=
      norm_correctedKernel_le j J e E he hE.1
    _ ≤ correctedKernelBound * (e * M + sqrt e * sqrt M) := by
      gcongr
      · exact hE.1.trans hE.2
      · exact hE.2

/-- The actual total variation mass controls the signed physical response. -/
theorem norm_correctedSignedRowResponse_le (ν : SignedMeasure ℝ) (J j : ℤ)
    (M : ℝ) (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ M)
    (e : ℝ) (he : |(j : ℝ)| ≤ e) :
    ‖correctedSignedRowResponse ν J j e‖ ≤
      ν.variation.real univ * correctedKernelBound * (e * M + sqrt e * sqrt M) := by
  let := signedMeasure_isFiniteMeasure_variation ν
  have hb : ∀ᵐ E ∂ν.variation,
      ‖correctedKernel j J e E‖ ≤ correctedKernelBound * (e * M + sqrt e * sqrt M) :=
    hs.mono fun E hE => correctedKernel_seed_bound J j M e E he hE
  have h := VectorMeasure.norm_integral_le_of_norm_le_const
    (B := (ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ)).flip) hb
  simpa only [correctedSignedRowResponse, ContinuousLinearMap.opNorm_flip,
    ContinuousLinearMap.opNorm_lsmul, mul_one, one_mul, mul_comm, mul_left_comm,
    mul_assoc] using h

/-- Signed seeds have ordinary integrable output numerators on every low band. -/
theorem correctedSignedRowResponse_integrable_lowBand (ν : SignedMeasure ℝ)
    (J j : ℤ) (M B : ℝ) (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ M) :
    Integrable (correctedSignedRowResponse ν J j)
      ((referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) := by
  apply (((lowBand_energy_integrable j B).mul_const M).add
    ((lowBand_sqrt_energy_integrable j B).mul_const (sqrt M))).const_mul
      (ν.variation.real univ * correctedKernelBound) |>.mono'
        (correctedSignedRowResponse_stronglyMeasurable ν J j M hs).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with e he
  exact norm_correctedSignedRowResponse_le ν J j M hs e he.1.le

/-- The ordinary output mass keeps the input and output cutoffs separate. -/
theorem integral_norm_correctedSignedRowResponse_lowBand_le (ν : SignedMeasure ℝ)
    (J j : ℤ) (M B : ℝ) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ M) :
    (∫ e, ‖correctedSignedRowResponse ν J j e‖
      ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) ≤
      ν.variation.real univ * correctedKernelBound *
        (M * B + sqrt M * (B + 2 * sqrt B)) := by
  have hC := correctedKernelBound_pos
  have hiE := (lowBand_energy_integrable j B).mul_const M
  have hiS := (lowBand_sqrt_energy_integrable j B).mul_const (sqrt M)
  calc
    _ ≤ ∫ e, ν.variation.real univ * correctedKernelBound * (e * M + sqrt e * sqrt M)
        ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| B) := by
      apply integral_mono_ae (correctedSignedRowResponse_integrable_lowBand ν J j M B hs).norm
        ((hiE.add hiS).const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with e he
      exact norm_correctedSignedRowResponse_le ν J j M hs e he.1.le
    _ = ν.variation.real univ * correctedKernelBound *
        ((∫ e, e ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) * M +
          (∫ e, sqrt e ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) * sqrt M) := by
      rw [integral_const_mul, integral_add hiE hiS, integral_mul_const, integral_mul_const]
    _ ≤ ν.variation.real univ * correctedKernelBound *
        (B * M + (B + 2 * sqrt B) * sqrt M) := by
      gcongr
      · by_cases hj : |(j : ℝ)| ≤ B
        · rw [lowBand_integral_energy j hj]
          exact (Real.sqrt_le_left hB).mpr (by nlinarith [sq_nonneg (j : ℝ)])
        · simp [Ioo_eq_empty_of_le (le_of_not_ge hj), hB]
      · exact lowBand_integral_sqrt_energy_le j B hB
    _ = _ := by ring

/-- The same signed output is a genuine Hilbert row. -/
theorem correctedSignedRowResponse_memLp_lowBand (ν : SignedMeasure ℝ)
    (J j : ℤ) (M B : ℝ) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ M) :
    MemLp (correctedSignedRowResponse ν J j) 2
      ((referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) := by
  have hm := (((lowBand_energy_memLp j B hB).mul_const M).add
    ((lowBand_sqrt_energy_memLp j B).mul_const (sqrt M))).const_mul
      (ν.variation.real univ * correctedKernelBound)
  apply hm.of_le
    (correctedSignedRowResponse_stronglyMeasurable ν J j M hs).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with e he
  have he0 := (abs_nonneg (j : ℝ)).trans he.1.le
  have hC := correctedKernelBound_pos
  have hTV : 0 ≤ ν.variation.real univ := measureReal_nonneg
  change ‖correctedSignedRowResponse ν J j e‖ ≤
    ‖ν.variation.real univ * correctedKernelBound * (e * M + sqrt e * sqrt M)‖
  rw [Real.norm_of_nonneg (by positivity)]
  exact norm_correctedSignedRowResponse_le ν J j M hs e he.1.le

/-- The actual signed response as an equivalence class of physical `L²` functions. -/
def correctedSignedRowResponseLp (ν : SignedMeasure ℝ) (J j : ℤ)
    (M B : ℝ) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ M) : LowBandRow j B :=
  (correctedSignedRowResponse_memLp_lowBand ν J j M B hM hB hs).toLp
    (correctedSignedRowResponse ν J j)

theorem correctedSignedRowResponseLp_coeFn (ν : SignedMeasure ℝ) (J j : ℤ)
    (M B : ℝ) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ M) :
    ⇑(correctedSignedRowResponseLp ν J j M B hM hB hs) =ᵐ[
      (referenceMeasure j).restrict (Ioo |(j : ℝ)| B)] correctedSignedRowResponse ν J j :=
  (correctedSignedRowResponse_memLp_lowBand ν J j M B hM hB hs).coeFn_toLp

private theorem real_L2_norm_sq_eq_integral {μ : Measure ℝ} (f : Lp ℝ 2 μ) :
    ‖f‖ ^ 2 = ∫ e, (f e) ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

private theorem norm_energy_toLp_le (j : ℤ) (B : ℝ) (hB : 0 ≤ B) :
    ‖(lowBand_energy_memLp j B hB).toLp (fun E : ℝ => E)‖ ≤ B := by
  apply (sq_le_sq₀ (norm_nonneg _) hB).mp
  rw [real_L2_norm_sq_eq_integral]
  calc
    _ = ∫ E, E ^ 2 ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| B) := by
      apply integral_congr_ae
      filter_upwards [(lowBand_energy_memLp j B hB).coeFn_toLp] with E hE
      rw [hE]
    _ ≤ B ^ 2 := (lowBand_energy_sq_integrable_le j hB).2

private theorem norm_sqrt_energy_toLp_le (j : ℤ) (B : ℝ) (hB : 0 ≤ B) :
    ‖(lowBand_sqrt_energy_memLp j B).toLp (fun E : ℝ => sqrt E)‖ ≤ sqrt B := by
  apply (sq_le_sq₀ (norm_nonneg _) (sqrt_nonneg B)).mp
  rw [real_L2_norm_sq_eq_integral, Real.sq_sqrt hB]
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

/-- The exact Hilbert estimate uses the first and second energy moments. -/
theorem norm_correctedSignedRowResponseLp_le (ν : SignedMeasure ℝ) (J j : ℤ)
    (M B : ℝ) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ M) :
    ‖correctedSignedRowResponseLp ν J j M B hM hB hs‖ ≤
      ν.variation.real univ * correctedKernelBound * (M * B + sqrt M * sqrt B) := by
  let u := (lowBand_energy_memLp j B hB).toLp (fun E : ℝ => E)
  let v := (lowBand_sqrt_energy_memLp j B).toLp (fun E : ℝ => sqrt E)
  let A := ν.variation.real univ * correctedKernelBound
  have hA : 0 ≤ A := mul_nonneg (measureReal_nonneg) correctedKernelBound_pos.le
  have hu : ‖u‖ ≤ B := norm_energy_toLp_le j B hB
  have hv : ‖v‖ ≤ sqrt B := norm_sqrt_energy_toLp_le j B hB
  calc
    _ ≤ A * ‖M • u + sqrt M • v‖ := by
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [correctedSignedRowResponseLp_coeFn ν J j M B hM hB hs,
        Lp.coeFn_add (M • u) (sqrt M • v), Lp.coeFn_smul M u,
        Lp.coeFn_smul (sqrt M) v, (lowBand_energy_memLp j B hB).coeFn_toLp,
        (lowBand_sqrt_energy_memLp j B).coeFn_toLp,
        ae_restrict_mem measurableSet_Ioo] with e hf hadd hmu hmv hu hv he
      have he0 := (abs_nonneg (j : ℝ)).trans he.1.le
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hadd hmu hmv
      rw [hf, hadd, hmu, hmv, hu, hv, Real.norm_of_nonneg (by positivity)]
      exact (norm_correctedSignedRowResponse_le ν J j M hs e he.1.le).trans_eq (by dsimp [A]; ring)
    _ ≤ A * (‖M • u‖ + ‖sqrt M • v‖) := mul_le_mul_of_nonneg_left (norm_add_le _ _) hA
    _ = A * (M * ‖u‖ + sqrt M * ‖v‖) := by
      rw [norm_smul, norm_smul, Real.norm_of_nonneg hM, Real.norm_of_nonneg (sqrt_nonneg M)]
    _ ≤ A * (M * B + sqrt M * sqrt B) := by gcongr

/-- Finite signed input rows are superposed by their actual signed integrals. -/
def correctedSignedResponse {ι : Type*} [Fintype ι]
    (ν : ι → SignedMeasure ℝ) (J : ι → ℤ) (j : ℤ) (e : ℝ) : ℂ :=
  ∑ i, correctedSignedRowResponse (ν i) (J i) j e

/-- The total variation budget of a finite signed spin family. -/
def signedSeedMass {ι : Type*} [Fintype ι] (ν : ι → SignedMeasure ℝ) : ℝ :=
  ∑ i, (ν i).variation.real univ

theorem signedSeedMass_nonneg {ι : Type*} [Fintype ι] (ν : ι → SignedMeasure ℝ) :
    0 ≤ signedSeedMass ν := Finset.sum_nonneg fun _ _ => measureReal_nonneg

theorem correctedSignedResponse_integrable_lowBand {ι : Type*} [Fintype ι]
    (ν : ι → SignedMeasure ℝ) (J : ι → ℤ) (j : ℤ) (M B : ℝ)
    (hs : ∀ i, ∀ᵐ E ∂(ν i).variation, |(J i : ℝ)| ≤ E ∧ E ≤ M) :
    Integrable (correctedSignedResponse ν J j)
      ((referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) :=
  integrable_finsetSum Finset.univ fun i _ =>
    correctedSignedRowResponse_integrable_lowBand (ν i) (J i) j M B (hs i)

theorem integral_norm_correctedSignedResponse_lowBand_le {ι : Type*} [Fintype ι]
    (ν : ι → SignedMeasure ℝ) (J : ι → ℤ) (j : ℤ) (M B : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hs : ∀ i, ∀ᵐ E ∂(ν i).variation, |(J i : ℝ)| ≤ E ∧ E ≤ M) :
    (∫ e, ‖correctedSignedResponse ν J j e‖
      ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) ≤
      signedSeedMass ν * correctedKernelBound *
        (M * B + sqrt M * (B + 2 * sqrt B)) := by
  calc
    _ ≤ ∫ e, ∑ i, ‖correctedSignedRowResponse (ν i) (J i) j e‖
        ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| B) := by
      apply integral_mono_ae (correctedSignedResponse_integrable_lowBand ν J j M B hs).norm
        (integrable_finsetSum Finset.univ fun i _ =>
          (correctedSignedRowResponse_integrable_lowBand (ν i) (J i) j M B (hs i)).norm)
      exact Filter.Eventually.of_forall fun e => norm_sum_le _ _
    _ = ∑ i, ∫ e, ‖correctedSignedRowResponse (ν i) (J i) j e‖
        ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| B) :=
      integral_finsetSum Finset.univ fun i _ =>
        (correctedSignedRowResponse_integrable_lowBand (ν i) (J i) j M B (hs i)).norm
    _ ≤ ∑ i, (ν i).variation.real univ * correctedKernelBound *
        (M * B + sqrt M * (B + 2 * sqrt B)) := Finset.sum_le_sum fun i _ =>
      integral_norm_correctedSignedRowResponse_lowBand_le (ν i) (J i) j M B hM hB (hs i)
    _ = _ := by simp only [signedSeedMass, Finset.sum_mul]

/-- The actual finite signed seed output as a physical Hilbert row. -/
def correctedSignedResponseLp {ι : Type*} [Fintype ι]
    (ν : ι → SignedMeasure ℝ) (J : ι → ℤ) (j : ℤ) (M B : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hs : ∀ i, ∀ᵐ E ∂(ν i).variation, |(J i : ℝ)| ≤ E ∧ E ≤ M) : LowBandRow j B :=
  ∑ i, correctedSignedRowResponseLp (ν i) (J i) j M B hM hB (hs i)

theorem correctedSignedResponseLp_coeFn {ι : Type*} [Fintype ι]
    (ν : ι → SignedMeasure ℝ) (J : ι → ℤ) (j : ℤ) (M B : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hs : ∀ i, ∀ᵐ E ∂(ν i).variation, |(J i : ℝ)| ≤ E ∧ E ≤ M) :
    ⇑(correctedSignedResponseLp ν J j M B hM hB hs) =ᵐ[
      (referenceMeasure j).restrict (Ioo |(j : ℝ)| B)] correctedSignedResponse ν J j := by
  apply (Lp.coeFn_finsetSum Finset.univ _).trans
  apply (eventuallyEq_sum (s := Finset.univ) fun i _ =>
    correctedSignedRowResponseLp_coeFn (ν i) (J i) j M B hM hB (hs i)).trans
  exact Filter.Eventually.of_forall fun e => by simp [correctedSignedResponse]

theorem norm_correctedSignedResponseLp_le {ι : Type*} [Fintype ι]
    (ν : ι → SignedMeasure ℝ) (J : ι → ℤ) (j : ℤ) (M B : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hs : ∀ i, ∀ᵐ E ∂(ν i).variation, |(J i : ℝ)| ≤ E ∧ E ≤ M) :
    ‖correctedSignedResponseLp ν J j M B hM hB hs‖ ≤
      signedSeedMass ν * correctedKernelBound * (M * B + sqrt M * sqrt B) := by
  calc
    _ ≤ ∑ i, ‖correctedSignedRowResponseLp (ν i) (J i) j M B hM hB (hs i)‖ := norm_sum_le _ _
    _ ≤ ∑ i, (ν i).variation.real univ * correctedKernelBound *
        (M * B + sqrt M * sqrt B) := Finset.sum_le_sum fun i _ =>
      norm_correctedSignedRowResponseLp_le (ν i) (J i) j M B hM hB (hs i)
    _ = _ := by simp only [signedSeedMass, Finset.sum_mul]

/-- Simultaneous Hilbert output on an arbitrary finite family of physical spins. -/
def correctedSignedResponseHilbert {ι κ : Type*} [Fintype ι] [Fintype κ]
    (ν : ι → SignedMeasure ℝ) (J : ι → ℤ) (j : κ → ℤ) (M B : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hs : ∀ i, ∀ᵐ E ∂(ν i).variation, |(J i : ℝ)| ≤ E ∧ E ≤ M) : LowBandHilbert j B :=
  WithLp.toLp 2 fun k => correctedSignedResponseLp ν J (j k) M B hM hB hs

theorem norm_correctedSignedResponseHilbert_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (ν : ι → SignedMeasure ℝ) (J : ι → ℤ) (j : κ → ℤ) (M B : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hs : ∀ i, ∀ᵐ E ∂(ν i).variation, |(J i : ℝ)| ≤ E ∧ E ≤ M) :
    ‖correctedSignedResponseHilbert ν J j M B hM hB hs‖ ≤
      sqrt (Fintype.card κ : ℝ) *
        (signedSeedMass ν * correctedKernelBound * (M * B + sqrt M * sqrt B)) := by
  have hC := correctedKernelBound_pos
  have hTV := signedSeedMass_nonneg ν
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [PiLp.norm_sq_eq_of_L2, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  calc
    _ ≤ ∑ _ : κ, (signedSeedMass ν * correctedKernelBound * (M * B + sqrt M * sqrt B)) ^ 2 :=
      Finset.sum_le_sum fun k _ => sq_le_sq₀ (norm_nonneg _) (by positivity) |>.mpr
        (norm_correctedSignedResponseLp_le ν J (j k) M B hM hB hs)
    _ = _ := by simp

theorem sum_integral_norm_correctedSignedResponse_lowBand_le
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (ν : ι → SignedMeasure ℝ) (J : ι → ℤ) (j : κ → ℤ) (M B : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hs : ∀ i, ∀ᵐ E ∂(ν i).variation, |(J i : ℝ)| ≤ E ∧ E ≤ M) :
    (∑ k, ∫ e, ‖correctedSignedResponse ν J (j k) e‖
      ∂(referenceMeasure (j k)).restrict (Ioo |(j k : ℝ)| B)) ≤
      (Fintype.card κ : ℝ) * signedSeedMass ν * correctedKernelBound *
        (M * B + sqrt M * (B + 2 * sqrt B)) := by
  calc
    _ ≤ ∑ _ : κ, signedSeedMass ν * correctedKernelBound *
        (M * B + sqrt M * (B + 2 * sqrt B)) := Finset.sum_le_sum fun k _ =>
      integral_norm_correctedSignedResponse_lowBand_le ν J (j k) M B hM hB hs
    _ = _ := by simp; ring

private theorem sqrt_triple_le_twice {B : ℝ} (hB : 1 ≤ B) : sqrt (3 * B) ≤ 2 * B := by
  apply (Real.sqrt_le_left (by linarith : 0 ≤ 2 * B)).mpr
  nlinarith

private theorem signedSeed_hilbert_coefficient_le {B : ℝ} (hB : 1 ≤ B) :
    (3 * B) * B + sqrt (3 * B) * sqrt B ≤ 5 * B ^ 2 := by
  have hs : sqrt B ≤ B := Real.sqrt_le_self_iff.mpr (Or.inr hB)
  calc
    _ ≤ (3 * B) * B + (2 * B) * B := by
      gcongr
      exact sqrt_triple_le_twice hB
    _ = _ := by ring

private theorem signedSeed_mass_coefficient_le {B : ℝ} (hB : 1 ≤ B) :
    (3 * B) * B + sqrt (3 * B) * (B + 2 * sqrt B) ≤ 9 * B ^ 2 := by
  have hs : sqrt B ≤ B := Real.sqrt_le_self_iff.mpr (Or.inr hB)
  calc
    _ ≤ (3 * B) * B + (2 * B) * (B + 2 * B) := by
      gcongr
      exact sqrt_triple_le_twice hB
    _ = _ := by ring

/-- Hilbert smoothing at the physical input cutoff `3 B`; the number of
distinct physical output spins is estimated internally. -/
theorem norm_correctedSignedResponseHilbert_le_physical
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (ν : ι → SignedMeasure ℝ) (J : ι → ℤ) (j : κ → ℤ)
    (hj : Function.Injective j) (B : ℝ) (hB : 1 ≤ B)
    (hband : ∀ k, |(j k : ℝ)| < B)
    (hs : ∀ i, ∀ᵐ E ∂(ν i).variation, |(J i : ℝ)| ≤ E ∧ E ≤ 3 * B) :
    ‖correctedSignedResponseHilbert ν J j (3 * B) B (by linarith) (by linarith) hs‖ ≤
      5 * sqrt 5 * correctedKernelBound * signedSeedMass ν * B ^ 2 * sqrt B := by
  have hC := correctedKernelBound_pos
  have hTV := signedSeedMass_nonneg ν
  have hB0 : 0 ≤ B := by linarith
  calc
    _ ≤ sqrt (Fintype.card κ : ℝ) *
        (signedSeedMass ν * correctedKernelBound *
          ((3 * B) * B + sqrt (3 * B) * sqrt B)) :=
      norm_correctedSignedResponseHilbert_le ν J j (3 * B) B (by linarith) hB0 hs
    _ ≤ sqrt (5 * B) * (signedSeedMass ν * correctedKernelBound * (5 * B ^ 2)) := by
      gcongr
      · exact physicalLowBand_card_le j hj hB hband
      · exact signedSeed_hilbert_coefficient_le hB
    _ = _ := by rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 5)]; ring

/-- Ordinary mass smoothing for the same genuine compact signed seed. -/
theorem sum_integral_norm_correctedSignedResponse_lowBand_le_physical
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (ν : ι → SignedMeasure ℝ) (J : ι → ℤ) (j : κ → ℤ)
    (hj : Function.Injective j) (B : ℝ) (hB : 1 ≤ B)
    (hband : ∀ k, |(j k : ℝ)| < B)
    (hs : ∀ i, ∀ᵐ E ∂(ν i).variation, |(J i : ℝ)| ≤ E ∧ E ≤ 3 * B) :
    (∑ k, ∫ e, ‖correctedSignedResponse ν J (j k) e‖
      ∂(referenceMeasure (j k)).restrict (Ioo |(j k : ℝ)| B)) ≤
      45 * correctedKernelBound * signedSeedMass ν * B ^ 3 := by
  have hC := correctedKernelBound_pos
  have hTV := signedSeedMass_nonneg ν
  have hB0 : 0 ≤ B := by linarith
  calc
    _ ≤ (Fintype.card κ : ℝ) * signedSeedMass ν * correctedKernelBound *
        ((3 * B) * B + sqrt (3 * B) * (B + 2 * sqrt B)) :=
      sum_integral_norm_correctedSignedResponse_lowBand_le ν J j (3 * B) B
        (by linarith) hB0 hs
    _ ≤ (5 * B) * signedSeedMass ν * correctedKernelBound * (9 * B ^ 2) := by
      gcongr
      · exact physicalLowBand_card_le j hj hB hband
      · exact signedSeed_mass_coefficient_le hB
    _ = _ := by ring

end GapFamily.Analytic
