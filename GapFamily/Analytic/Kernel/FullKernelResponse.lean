import GapFamily.Analytic.Kernel.FullKernelExtension
import GapFamily.Analytic.Kernel.FullKernelSmoothing
import GapFamily.Analytic.Kernel.HigherKernelResponse

/-! Entire responses of the actual full canonical kernel. The central term is
controlled by the input energy before integration; scalar Hilbert vectors are
never assumed to have finite ordinary mass. -/
noncomputable section
open MeasureTheory Real Set Metric
open scoped Topology BigOperators ComplexConjugate
namespace GapFamily.Analytic

/-- The actual uniform central arithmetic constant. -/
def centralKernelBound : ℝ := exists_centralKernel_bound.choose

theorem centralKernelBound_pos : 0 < centralKernelBound :=
  exists_centralKernel_bound.choose_spec.1

theorem norm_centralKernel_le (j J : ℤ) :
    ‖centralKernel j J‖ ≤ centralKernelBound * (|(j : ℝ)| * |(J : ℝ)|) :=
  exists_centralKernel_bound.choose_spec.2 j J

/-- The input-energy factor is retained even on the scalar row. -/
def fullKernelCompactBound (j : ℤ) (B R : ℝ) : ℝ :=
  centralKernelBound * |(j : ℝ)| + higherKernelCompactBound j B R

theorem fullKernelCompactBound_nonneg (j : ℤ) (B R : ℝ) (hR : 0 ≤ R) :
    0 ≤ fullKernelCompactBound j B R :=
  add_nonneg (mul_nonneg centralKernelBound_pos.le (abs_nonneg _))
    (higherKernelCompactBound_nonneg j B R hR)

theorem norm_fullKernel_complex_output_on_band_le (j J : ℤ) (e : ℂ)
    (E B R : ℝ) (hE : |(J : ℝ)| ≤ E) (hEB : E ≤ B) (he : ‖e‖ ≤ R) :
    ‖fullKernelHol j J e E‖ ≤ fullKernelCompactBound j B R * E := by
  have hc : ‖centralKernel j J‖ ≤ centralKernelBound * |(j : ℝ)| * E :=
    (norm_centralKernel_le j J).trans (by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_left hE
        (mul_nonneg centralKernelBound_pos.le (abs_nonneg _)))
  calc
    _ ≤ ‖centralKernel j J‖ + ‖higherKernel j J e E‖ := norm_add_le _ _
    _ ≤ centralKernelBound * |(j : ℝ)| * E + higherKernelCompactBound j B R * E :=
      add_le_add hc (norm_higherKernel_complex_output_on_band_le j J e E B R hE hEB he)
    _ = _ := by unfold fullKernelCompactBound; ring

/-- The ordinary full-kernel response of one physical low-band input row. -/
def fullKernelRowResponse (j J : ℤ) (B : ℝ) (f : LowBandRow J B) (e : ℂ) : ℂ :=
  ∫ E, fullKernelHol j J e E * f E
    ∂(referenceMeasure J).restrict (Ioo |(J : ℝ)| B)

theorem fullKernelRowResponse_aestronglyMeasurable (j J : ℤ) (B : ℝ)
    (f : LowBandRow J B) (e : ℂ) :
    AEStronglyMeasurable (fun E : ℝ => fullKernelHol j J e E * f E)
      ((referenceMeasure J).restrict (Ioo |(J : ℝ)| B)) := by
  have hp : Continuous (fun E : ℝ => (e, (E : ℂ))) :=
    continuous_const.prodMk Complex.continuous_ofReal
  have hc : Continuous (fun E : ℝ => fullKernelHol j J e (E : ℂ)) := by
    simpa only [Function.comp_def] using (continuous_fullKernelHol j J).comp hp
  exact hc.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f)

/-- Local domination keeps the actual input-energy factor, uniformly in complex output. -/
theorem fullKernelRowResponse_disk_domination (j J : ℤ) (B : ℝ)
    (hB : 0 < B) (f : LowBandRow J B) (e₀ : ℂ) :
    ∃ b : ℝ → ℝ,
      Integrable b ((referenceMeasure J).restrict (Ioo |(J : ℝ)| B)) ∧
      ∀ᵐ (E : ℝ) ∂(referenceMeasure J).restrict (Ioo |(J : ℝ)| B),
        ∀ e ∈ closedBall e₀ 2, ‖fullKernelHol j J e E * f E‖ ≤ b E := by
  refine ⟨fun E => fullKernelCompactBound j B (‖e₀‖ + 2) * (E * ‖f E‖),
    (lowBand_energy_norm_integrable J B hB.le f).const_mul _, ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with E hE
  intro e he
  have her : ‖e‖ ≤ ‖e₀‖ + 2 := by
    exact norm_le_norm_add_const_of_dist_le (mem_closedBall.mp he)
  rw [norm_mul]
  calc
    _ ≤ (fullKernelCompactBound j B (‖e₀‖ + 2) * E) * ‖f E‖ :=
      mul_le_mul_of_nonneg_right
        (norm_fullKernel_complex_output_on_band_le j J e E B (‖e₀‖ + 2)
          hE.1.le hE.2.le her) (norm_nonneg _)
    _ = _ := by ring

/-- The defining row integral is genuinely integrable at every complex output energy. -/
theorem fullKernelRowResponse_integrable (j J : ℤ) (B : ℝ)
    (hB : 0 < B) (f : LowBandRow J B) (e : ℂ) :
    Integrable (fun E : ℝ => fullKernelHol j J e E * f E)
      ((referenceMeasure J).restrict (Ioo |(J : ℝ)| B)) :=
  integrable_of_entire_disk_bound
    (fullKernelRowResponse_aestronglyMeasurable j J B f)
    (fullKernelRowResponse_disk_domination j J B hB f) e

/-- The ordinary row response is entire in output energy. -/
theorem differentiable_fullKernelRowResponse (j J : ℤ) (B : ℝ)
    (hB : 0 < B) (f : LowBandRow J B) :
    Differentiable ℂ (fullKernelRowResponse j J B f) := by
  apply differentiable_integral_of_entire_disk_bound
    (fullKernelRowResponse_aestronglyMeasurable j J B f) _
    (fullKernelRowResponse_disk_domination j J B hB f)
  exact Filter.Eventually.of_forall fun E =>
    (differentiable_fullKernelHol_comp j J id (fun _ => (E : ℂ))
      differentiable_id (differentiable_const _)).mul_const (f E)

/-- A uniform output-disk bound in the actual input Hilbert norm. -/
theorem norm_fullKernelRowResponse_le (j J : ℤ) (B : ℝ)
    (hB : 0 < B) (f : LowBandRow J B) (e : ℂ) (R : ℝ) (he : ‖e‖ ≤ R) :
    ‖fullKernelRowResponse j J B f e‖ ≤ fullKernelCompactBound j B R * B * ‖f‖ := by
  have hR : 0 ≤ R := (norm_nonneg e).trans he
  have hC := fullKernelCompactBound_nonneg j B R hR
  calc
    _ ≤ ∫ E, fullKernelCompactBound j B R * (E * ‖f E‖)
        ∂(referenceMeasure J).restrict (Ioo |(J : ℝ)| B) := by
      apply norm_integral_le_of_norm_le ((lowBand_energy_norm_integrable J B hB.le f).const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with E hE
      rw [norm_mul]
      calc
        _ ≤ (fullKernelCompactBound j B R * E) * ‖f E‖ :=
          mul_le_mul_of_nonneg_right
            (norm_fullKernel_complex_output_on_band_le j J e E B R hE.1.le hE.2.le he)
            (norm_nonneg _)
        _ = _ := by ring
    _ = fullKernelCompactBound j B R *
        ∫ E, E * ‖f E‖ ∂(referenceMeasure J).restrict (Ioo |(J : ℝ)| B) := integral_const_mul _ _
    _ ≤ fullKernelCompactBound j B R * (B * ‖f‖) :=
      mul_le_mul_of_nonneg_left (lowBand_energy_norm_integral_le J B hB.le f) hC
    _ = _ := by ring

/-- A finite spin family gives the actual finite sum of ordinary row responses. -/
def fullKernelResponse {ι : Type*} [Fintype ι] (J : ι → ℤ) (B : ℝ)
    (f : LowBandHilbert J B) (j : ℤ) (e : ℂ) : ℂ :=
  ∑ i, fullKernelRowResponse j (J i) B (f i) e

theorem differentiable_fullKernelResponse {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 < B) (f : LowBandHilbert J B) (j : ℤ) :
    Differentiable ℂ (fullKernelResponse J B f j) :=
  Differentiable.fun_sum fun i _ => differentiable_fullKernelRowResponse j (J i) B hB (f i)

/-- Finite-spin norm control; no input row is required to have finite reference mass. -/
theorem norm_fullKernelResponse_le {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 < B) (f : LowBandHilbert J B) (j : ℤ)
    (e : ℂ) (R : ℝ) (he : ‖e‖ ≤ R) :
    ‖fullKernelResponse J B f j e‖ ≤
      (Fintype.card ι : ℝ) * (fullKernelCompactBound j B R * B) * ‖f‖ := by
  have hC := fullKernelCompactBound_nonneg j B R ((norm_nonneg e).trans he)
  calc
    _ ≤ ∑ i, ‖fullKernelRowResponse j (J i) B (f i) e‖ := norm_sum_le _ _
    _ ≤ ∑ i : ι, fullKernelCompactBound j B R * B * ‖f‖ := by
      apply Finset.sum_le_sum
      intro i hi
      exact (norm_fullKernelRowResponse_le j (J i) B hB (f i) e R he).trans
        (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le f i) (mul_nonneg hC hB.le))
    _ = _ := by simp; ring


/-- The ordinary half-energy moment of one Hilbert row. -/
def lowBandHalfMoment (J : ℤ) (B : ℝ) (f : LowBandRow J B) : ℂ :=
  ∫ E, (sqrt E : ℂ) * f E ∂(referenceMeasure J).restrict (Ioo |(J : ℝ)| B)

theorem lowBandHalfMoment_integrable (J : ℤ) (B : ℝ) (f : LowBandRow J B) :
    Integrable (fun E => (sqrt E : ℂ) * f E)
      ((referenceMeasure J).restrict (Ioo |(J : ℝ)| B)) := by
  apply (lowBand_sqrt_energy_norm_integrable J B f).mono'
    ((Complex.continuous_ofReal.comp Real.continuous_sqrt).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable f))
  exact Filter.Eventually.of_forall fun E => by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sqrt_nonneg E)]

theorem norm_lowBandHalfMoment_le (J : ℤ) (B : ℝ) (hB : 0 ≤ B)
    (f : LowBandRow J B) : ‖lowBandHalfMoment J B f‖ ≤ sqrt B * ‖f‖ := by
  apply (norm_integral_le_of_norm_le (lowBand_sqrt_energy_norm_integrable J B f)
    (Filter.Eventually.of_forall fun E => ?_)).trans
      (lowBand_sqrt_energy_norm_integral_le J B hB f)
  simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sqrt_nonneg E)]

/-- The rank-one term uses only the scalar input channel. -/
def lowBandScalarMoment {ι : Type*} [Fintype ι] (J : ι → ℤ) (B : ℝ)
    (f : LowBandHilbert J B) : ℂ :=
  ∑ i, if J i = 0 then lowBandHalfMoment (J i) B (f i) else 0

/-- The actual row response separates into its entire-energy and ordinary
rank-one parts. Both defining integrals are proved integrable. -/
theorem correctedKernelRowResponse_eq_full_add_rank (j J : ℤ) (B : ℝ)
    (hB : 0 < B) (f : LowBandRow J B) (e : ℝ) :
    correctedKernelRowResponse j J B f e = fullKernelRowResponse j J B f e +
      if j = 0 ∧ J = 0 then 12 * (sqrt e : ℂ) * lowBandHalfMoment J B f else 0 := by
  have hr : Integrable (fun E : ℝ => (scalarRankKernel j J e E : ℂ) * f E)
      ((referenceMeasure J).restrict (Ioo |(J : ℝ)| B)) := by
    by_cases h : j = 0 ∧ J = 0
    · simpa only [scalarRankKernel, if_pos h, Complex.ofReal_mul, Complex.ofReal_ofNat,
        mul_assoc] using (lowBandHalfMoment_integrable J B f).const_mul (12 * (sqrt e : ℂ))
    · simp only [scalarRankKernel, if_neg h, Complex.ofReal_zero, zero_mul]
      exact integrable_zero _ _ _
  unfold correctedKernelRowResponse correctedKernel
  simp_rw [add_mul]
  rw [integral_add (fullKernelRowResponse_integrable j J B hB f e) hr]
  congr 1
  by_cases h : j = 0 ∧ J = 0
  · simp only [scalarRankKernel, if_pos h, Complex.ofReal_mul, Complex.ofReal_ofNat,
      mul_assoc, integral_const_mul, lowBandHalfMoment]
  · simp [scalarRankKernel, h]

/-- The full holomorphic response, including the prescribed scalar rank term. -/
def correctedKernelScaledResponse {ι : Type*} [Fintype ι] (J : ι → ℤ) (B : ℝ)
    (f : LowBandHilbert J B) (j : ℤ) (z : ℂ) : ℂ :=
  fullKernelResponse J B f j (|(j : ℝ)| + (B : ℂ) * z ^ 2) +
    if j = 0 then 12 * (sqrt B : ℂ) * z * lowBandScalarMoment J B f else 0

theorem differentiable_correctedKernelScaledResponse {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 < B) (f : LowBandHilbert J B) (j : ℤ) :
    Differentiable ℂ (correctedKernelScaledResponse J B f j) := by
  unfold correctedKernelScaledResponse
  apply Differentiable.add
  · exact (differentiable_fullKernelResponse J B hB f j).comp (by fun_prop)
  · split_ifs <;> fun_prop

/-- Physical agreement uses only nonnegative real square-root coordinates. -/
theorem correctedKernelScaledResponse_ofReal {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 < B) (f : LowBandHilbert J B) (j : ℤ)
    (t : ℝ) (ht : 0 ≤ t) :
    correctedKernelScaledResponse J B f j t =
      correctedKernelResponse J B f j (|(j : ℝ)| + B * t ^ 2) := by
  unfold correctedKernelScaledResponse correctedKernelResponse
  simp_rw [correctedKernelRowResponse_eq_full_add_rank _ _ B hB]
  rw [Finset.sum_add_distrib]
  unfold fullKernelResponse
  push_cast
  congr 1
  by_cases hj : j = 0
  · subst j
    simp only [if_true, Int.cast_zero, abs_zero, zero_add, true_and]
    rw [sqrt_mul hB.le, sqrt_sq ht]
    simp only [Complex.ofReal_mul, lowBandScalarMoment, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> ring
  · simp [hj]

@[simp] theorem fullKernelRowResponse_scalar_zero (J : ℤ) (B : ℝ)
    (f : LowBandRow J B) : fullKernelRowResponse 0 J B f 0 = 0 := by
  simp [fullKernelRowResponse]

@[simp] theorem correctedKernelScaledResponse_scalar_zero {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (f : LowBandHilbert J B) :
    correctedKernelScaledResponse J B f 0 0 = 0 := by
  simp [correctedKernelScaledResponse, fullKernelResponse]

/-- The scalar quotient has its removable value at the origin. -/
def correctedKernelScalarNormalizedResponse {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (f : LowBandHilbert J B) : ℂ → ℂ :=
  dslope (correctedKernelScaledResponse J B f 0) 0

theorem correctedKernelScalarNormalizedResponse_eq_div {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (f : LowBandHilbert J B) (z : ℂ) (hz : z ≠ 0) :
    correctedKernelScalarNormalizedResponse J B f z =
      correctedKernelScaledResponse J B f 0 z / z := by
  simp [correctedKernelScalarNormalizedResponse, dslope_of_ne _ hz, slope_def_module,
    div_eq_mul_inv, mul_comm]

theorem differentiable_correctedKernelScalarNormalizedResponse {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 < B) (f : LowBandHilbert J B) :
    Differentiable ℂ (correctedKernelScalarNormalizedResponse J B f) := by
  apply differentiableOn_univ.mp
  exact (Complex.differentiableOn_dslope (s := univ) (c := 0) Filter.univ_mem).mpr
    (differentiable_correctedKernelScaledResponse J B hB f 0).differentiableOn

/-- At zero the removable scalar quotient is exactly the rank-one moment. -/
@[simp] theorem correctedKernelScalarNormalizedResponse_zero {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 < B) (f : LowBandHilbert J B) :
    correctedKernelScalarNormalizedResponse J B f 0 =
      12 * (sqrt B : ℂ) * lowBandScalarMoment J B f := by
  have hc : HasDerivAt (fun z : ℂ => (B : ℂ) * z ^ 2) 0 0 := by
    convert (((hasDerivAt_id (0 : ℂ)).pow 2).const_mul (B : ℂ)) using 1 <;> norm_num
  have hd : HasDerivAt (fun z : ℂ => fullKernelResponse J B f 0 ((B : ℂ) * z ^ 2)) 0 0 := by
    simpa only [Function.comp_def, mul_zero] using
      ((differentiable_fullKernelResponse J B hB f 0)
        ((B : ℂ) * (0 : ℂ) ^ 2)).hasDerivAt.comp 0 hc
  have hr : HasDerivAt (fun z : ℂ => 12 * (sqrt B : ℂ) * z * lowBandScalarMoment J B f)
      (12 * (sqrt B : ℂ) * lowBandScalarMoment J B f) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).const_mul (12 * (sqrt B : ℂ))).mul_const
      (lowBandScalarMoment J B f)
  rw [correctedKernelScalarNormalizedResponse, dslope_same]
  have hfun : correctedKernelScaledResponse J B f 0 =
      (fun z : ℂ => fullKernelResponse J B f 0 ((B : ℂ) * z ^ 2)) +
        (fun z : ℂ => 12 * (sqrt B : ℂ) * z * lowBandScalarMoment J B f) := by
    funext z
    simp [correctedKernelScaledResponse]
  rw [hfun]
  simpa using (hd.add hr).deriv

theorem norm_lowBandScalarMoment_le {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (f : LowBandHilbert J B) :
    ‖lowBandScalarMoment J B f‖ ≤ (Fintype.card ι : ℝ) * sqrt B * ‖f‖ := by
  calc
    _ ≤ ∑ i, ‖if J i = 0 then lowBandHalfMoment (J i) B (f i) else 0‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, sqrt B * ‖f‖ := by
      apply Finset.sum_le_sum
      intro i hi
      split_ifs
      · exact (norm_lowBandHalfMoment_le (J i) B hB (f i)).trans
          (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le f i) (sqrt_nonneg B))
      · simp only [norm_zero]
        positivity
    _ = _ := by simp; ring

/-- Uniform disk control of the full response, retaining explicit polynomial
losses and the existing higher-kernel exponential bound. -/
theorem norm_correctedKernelScaledResponse_le {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 < B) (f : LowBandHilbert J B) (j : ℤ)
    (R : ℝ) (hR : 0 ≤ R) (z : ℂ) (hz : ‖z‖ ≤ R) :
    ‖correctedKernelScaledResponse J B f j z‖ ≤
      (Fintype.card ι : ℝ) *
        (fullKernelCompactBound j B (|(j : ℝ)| + B * R ^ 2) * B + 12 * B * R) * ‖f‖ := by
  have he : ‖((|(j : ℝ)| : ℝ) : ℂ) + (B : ℂ) * z ^ 2‖ ≤ |(j : ℝ)| + B * R ^ 2 := by
    calc
      _ ≤ ‖((|(j : ℝ)| : ℝ) : ℂ)‖ + ‖(B : ℂ) * z ^ 2‖ := norm_add_le _ _
      _ = |(j : ℝ)| + B * ‖z‖ ^ 2 := by
        rw [norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_abs, abs_of_pos hB]
      _ ≤ _ := by gcongr
  have hr : ‖if j = 0 then 12 * (sqrt B : ℂ) * z * lowBandScalarMoment J B f else 0‖ ≤
      (Fintype.card ι : ℝ) * (12 * B * R) * ‖f‖ := by
    split_ifs
    · simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sqrt_nonneg B)]
      calc
        _ ≤ 12 * sqrt B * R * ((Fintype.card ι : ℝ) * sqrt B * ‖f‖) := by
          gcongr
          exact norm_lowBandScalarMoment_le J B hB.le f
        _ = (Fintype.card ι : ℝ) * (12 * (sqrt B) ^ 2 * R) * ‖f‖ := by ring
        _ = _ := by rw [sq_sqrt hB.le]
    · simp only [norm_zero]
      positivity
  exact (norm_add_le _ _).trans ((add_le_add
    (norm_fullKernelResponse_le J B hB f j _ _ he) hr).trans_eq (by ring))

/-- The scalar removable quotient has controlled size on every propagation disk. -/
theorem norm_correctedKernelScalarNormalizedResponse_le {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 < B) (f : LowBandHilbert J B)
    (R : ℝ) (hR : 0 ≤ R) (z : ℂ) (hz : ‖z‖ ≤ R) :
    ‖correctedKernelScalarNormalizedResponse J B f z‖ ≤
      ((Fintype.card ι : ℝ) *
        (fullKernelCompactBound 0 B (B * (R + 1) ^ 2) * B + 12 * B * (R + 1)) * ‖f‖) /
          (R + 1) := by
  apply Complex.norm_dslope_le_div_of_mapsTo_ball
    (differentiable_correctedKernelScaledResponse J B hB f 0).differentiableOn
  · intro w hw
    rw [correctedKernelScaledResponse_scalar_zero, mem_closedBall, dist_zero_right]
    simpa only [Int.cast_zero, abs_zero, zero_add] using
      norm_correctedKernelScaledResponse_le J B hB f 0 (R + 1) (by linarith) w
        ((show ‖w‖ < R + 1 by simpa only [mem_ball, dist_zero_right] using hw).le)
  · change dist z 0 < R + 1
    rw [dist_zero_right]
    linarith

end GapFamily.Analytic
