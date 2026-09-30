import GapFamily.Analytic.Kernel.HigherKernelResponseBound
import GapFamily.Analytic.Kernel.HigherKernelResponseIntegral
import GapFamily.Analytic.Kernel.HigherKernelResponseMoment
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Entire response of the actual higher kernel

The response integrates the genuine higher-kernel series against the actual
low-band Hilbert rows. Its linear input-energy zero supplies ordinary
integrability even in the scalar row. The separately continued central
arithmetic term and the rank-one correction are not included.
-/

noncomputable section

open MeasureTheory Real Set Metric
open scoped Topology BigOperators ComplexConjugate

namespace GapFamily.Analytic

/-- The ordinary higher-kernel response of one physical low-band input row. -/
def higherKernelRowResponse (j J : ℤ) (B : ℝ) (f : LowBandRow J B) (e : ℂ) : ℂ :=
  ∫ E, higherKernel j J e E * f E
    ∂(referenceMeasure J).restrict (Ioo |(J : ℝ)| B)

theorem higherKernelRowResponse_aestronglyMeasurable (j J : ℤ) (B : ℝ)
    (f : LowBandRow J B) (e : ℂ) :
    AEStronglyMeasurable (fun E : ℝ => higherKernel j J e E * f E)
      ((referenceMeasure J).restrict (Ioo |(J : ℝ)| B)) := by
  have hp : Continuous (fun E : ℝ => (e, (E : ℂ))) :=
    continuous_const.prodMk Complex.continuous_ofReal
  have hc : Continuous (fun E : ℝ => higherKernel j J e (E : ℂ)) := by
    simpa only [Function.comp_def] using (continuous_higherKernel j J).comp hp
  exact hc.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f)

/-- Local domination keeps the actual input-energy factor, uniformly in complex output. -/
theorem higherKernelRowResponse_disk_domination (j J : ℤ) (B : ℝ)
    (hB : 0 < B) (f : LowBandRow J B) (e₀ : ℂ) :
    ∃ b : ℝ → ℝ,
      Integrable b ((referenceMeasure J).restrict (Ioo |(J : ℝ)| B)) ∧
      ∀ᵐ (E : ℝ) ∂(referenceMeasure J).restrict (Ioo |(J : ℝ)| B),
        ∀ e ∈ closedBall e₀ 2, ‖higherKernel j J e E * f E‖ ≤ b E := by
  refine ⟨fun E => higherKernelCompactBound j B (‖e₀‖ + 2) * (E * ‖f E‖),
    (lowBand_energy_norm_integrable J B hB.le f).const_mul _, ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with E hE
  intro e he
  have her : ‖e‖ ≤ ‖e₀‖ + 2 := by
    exact norm_le_norm_add_const_of_dist_le (mem_closedBall.mp he)
  rw [norm_mul]
  calc
    _ ≤ (higherKernelCompactBound j B (‖e₀‖ + 2) * E) * ‖f E‖ :=
      mul_le_mul_of_nonneg_right
        (norm_higherKernel_complex_output_on_band_le j J e E B (‖e₀‖ + 2)
          hE.1.le hE.2.le her) (norm_nonneg _)
    _ = _ := by ring

/-- The defining row integral is genuinely integrable at every complex output energy. -/
theorem higherKernelRowResponse_integrable (j J : ℤ) (B : ℝ)
    (hB : 0 < B) (f : LowBandRow J B) (e : ℂ) :
    Integrable (fun E : ℝ => higherKernel j J e E * f E)
      ((referenceMeasure J).restrict (Ioo |(J : ℝ)| B)) :=
  integrable_of_entire_disk_bound
    (higherKernelRowResponse_aestronglyMeasurable j J B f)
    (higherKernelRowResponse_disk_domination j J B hB f) e

/-- The ordinary row response is entire in output energy. -/
theorem differentiable_higherKernelRowResponse (j J : ℤ) (B : ℝ)
    (hB : 0 < B) (f : LowBandRow J B) :
    Differentiable ℂ (higherKernelRowResponse j J B f) := by
  apply differentiable_integral_of_entire_disk_bound
    (higherKernelRowResponse_aestronglyMeasurable j J B f) _
    (higherKernelRowResponse_disk_domination j J B hB f)
  exact Filter.Eventually.of_forall fun E =>
    (differentiable_higherKernel_comp j J id (fun _ => (E : ℂ))
      differentiable_id (differentiable_const _)).mul_const (f E)

/-- A uniform output-disk bound in the actual input Hilbert norm. -/
theorem norm_higherKernelRowResponse_le (j J : ℤ) (B : ℝ)
    (hB : 0 < B) (f : LowBandRow J B) (e : ℂ) (R : ℝ) (he : ‖e‖ ≤ R) :
    ‖higherKernelRowResponse j J B f e‖ ≤ higherKernelCompactBound j B R * B * ‖f‖ := by
  have hR : 0 ≤ R := (norm_nonneg e).trans he
  have hC := higherKernelCompactBound_nonneg j B R hR
  calc
    _ ≤ ∫ E, higherKernelCompactBound j B R * (E * ‖f E‖)
        ∂(referenceMeasure J).restrict (Ioo |(J : ℝ)| B) := by
      apply norm_integral_le_of_norm_le ((lowBand_energy_norm_integrable J B hB.le f).const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with E hE
      rw [norm_mul]
      calc
        _ ≤ (higherKernelCompactBound j B R * E) * ‖f E‖ :=
          mul_le_mul_of_nonneg_right
            (norm_higherKernel_complex_output_on_band_le j J e E B R hE.1.le hE.2.le he)
            (norm_nonneg _)
        _ = _ := by ring
    _ = higherKernelCompactBound j B R *
        ∫ E, E * ‖f E‖ ∂(referenceMeasure J).restrict (Ioo |(J : ℝ)| B) := integral_const_mul _ _
    _ ≤ higherKernelCompactBound j B R * (B * ‖f‖) :=
      mul_le_mul_of_nonneg_left (lowBand_energy_norm_integral_le J B hB.le f) hC
    _ = _ := by ring

/-- A finite spin family gives the actual finite sum of ordinary row responses. -/
def higherKernelResponse {ι : Type*} [Fintype ι] (J : ι → ℤ) (B : ℝ)
    (f : LowBandHilbert J B) (j : ℤ) (e : ℂ) : ℂ :=
  ∑ i, higherKernelRowResponse j (J i) B (f i) e

theorem differentiable_higherKernelResponse {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 < B) (f : LowBandHilbert J B) (j : ℤ) :
    Differentiable ℂ (higherKernelResponse J B f j) :=
  Differentiable.fun_sum fun i _ => differentiable_higherKernelRowResponse j (J i) B hB (f i)

/-- Finite-spin norm control; no input row is required to have finite reference mass. -/
theorem norm_higherKernelResponse_le {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 < B) (f : LowBandHilbert J B) (j : ℤ)
    (e : ℂ) (R : ℝ) (he : ‖e‖ ≤ R) :
    ‖higherKernelResponse J B f j e‖ ≤
      (Fintype.card ι : ℝ) * (higherKernelCompactBound j B R * B) * ‖f‖ := by
  have hC := higherKernelCompactBound_nonneg j B R ((norm_nonneg e).trans he)
  calc
    _ ≤ ∑ i, ‖higherKernelRowResponse j (J i) B (f i) e‖ := norm_sum_le _ _
    _ ≤ ∑ i : ι, higherKernelCompactBound j B R * B * ‖f‖ := by
      apply Finset.sum_le_sum
      intro i hi
      exact (norm_higherKernelRowResponse_le j (J i) B hB (f i) e R he).trans
        (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le f i) (mul_nonneg hC hB.le))
    _ = _ := by simp; ring

/-- The quadratic output-energy curve gives the holomorphic response parametrization. -/
def higherKernelScaledResponse {ι : Type*} [Fintype ι] (J : ι → ℤ) (B : ℝ)
    (f : LowBandHilbert J B) (j : ℤ) (z : ℂ) : ℂ :=
  higherKernelResponse J B f j (((|(j : ℝ)| : ℝ) : ℂ) + (B : ℂ) * z ^ 2)

theorem differentiable_higherKernelScaledResponse {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 < B) (f : LowBandHilbert J B) (j : ℤ) :
    Differentiable ℂ (higherKernelScaledResponse J B f j) :=
  (differentiable_higherKernelResponse J B hB f j).comp (by fun_prop)

/-- Explicit bound on every closed propagation disk for the quadratic parametrization. -/
theorem norm_higherKernelScaledResponse_le {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 < B) (f : LowBandHilbert J B) (j : ℤ)
    (R : ℝ) (_hR : 0 ≤ R) (z : ℂ) (hz : ‖z‖ ≤ R) :
    ‖higherKernelScaledResponse J B f j z‖ ≤
      (Fintype.card ι : ℝ) *
        (higherKernelCompactBound j B (|(j : ℝ)| + B * R ^ 2) * B) * ‖f‖ := by
  apply norm_higherKernelResponse_le J B hB f j _ _
  calc
    _ ≤ ‖((|(j : ℝ)| : ℝ) : ℂ)‖ + ‖(B : ℂ) * z ^ 2‖ := norm_add_le _ _
    _ = |(j : ℝ)| + B * ‖z‖ ^ 2 := by
      rw [norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_abs, abs_of_pos hB]
    _ ≤ _ := by gcongr

/-- The scalar output has its exact energy zero before any normalization. -/
@[simp]
theorem higherKernelRowResponse_scalar_zero (J : ℤ) (B : ℝ) (f : LowBandRow J B) :
    higherKernelRowResponse 0 J B f 0 = 0 := by
  simp [higherKernelRowResponse]

@[simp]
theorem higherKernelResponse_scalar_zero {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (f : LowBandHilbert J B) :
    higherKernelResponse J B f 0 0 = 0 := by
  simp [higherKernelResponse]

@[simp]
theorem higherKernelScaledResponse_scalar_zero {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (f : LowBandHilbert J B) :
    higherKernelScaledResponse J B f 0 0 = 0 := by
  simp [higherKernelScaledResponse]

/-- The scalar quotient with its removable value, defined by the derivative slope. -/
def higherKernelScalarNormalizedResponse {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (f : LowBandHilbert J B) : ℂ → ℂ :=
  dslope (higherKernelScaledResponse J B f 0) 0

/-- Away from zero the normalized scalar response is the actual quotient by z. -/
theorem higherKernelScalarNormalizedResponse_eq_div {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (f : LowBandHilbert J B) {z : ℂ} (hz : z ≠ 0) :
    higherKernelScalarNormalizedResponse J B f z = higherKernelScaledResponse J B f 0 z / z := by
  simp [higherKernelScalarNormalizedResponse, dslope_of_ne _ hz, slope_def_module,
    div_eq_mul_inv, mul_comm]

/-- The removable scalar quotient is entire, including the value at zero. -/
theorem differentiable_higherKernelScalarNormalizedResponse {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 < B) (f : LowBandHilbert J B) :
    Differentiable ℂ (higherKernelScalarNormalizedResponse J B f) := by
  apply differentiableOn_univ.mp
  exact (Complex.differentiableOn_dslope (s := univ) (c := 0) Filter.univ_mem).mpr
    (differentiable_higherKernelScaledResponse J B hB f 0).differentiableOn

/-- The higher part has removable scalar value zero; no square root is continued globally. -/
@[simp]
theorem higherKernelScalarNormalizedResponse_zero {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 < B) (f : LowBandHilbert J B) :
    higherKernelScalarNormalizedResponse J B f 0 = 0 := by
  have hc : HasDerivAt (fun z : ℂ => (B : ℂ) * z ^ 2) 0 0 := by
    convert (((hasDerivAt_id (0 : ℂ)).pow 2).const_mul (B : ℂ)) using 1 <;> norm_num
  have hd := ((differentiable_higherKernelResponse J B hB f 0)
    ((B : ℂ) * (0 : ℂ) ^ 2)).hasDerivAt.comp
      (h := fun z : ℂ => (B : ℂ) * z ^ 2) 0 hc
  have hfun : higherKernelScaledResponse J B f 0 =
      fun z : ℂ => higherKernelResponse J B f 0 ((B : ℂ) * z ^ 2) := by
    funext z
    simp [higherKernelScaledResponse]
  rw [higherKernelScalarNormalizedResponse, dslope_same, hfun]
  simpa only [Function.comp_def, mul_zero] using hd.deriv

/-- A closed-disk bound for the normalized scalar response, with all constants explicit. -/
theorem norm_higherKernelScalarNormalizedResponse_le {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 < B) (f : LowBandHilbert J B)
    (R : ℝ) (hR : 0 ≤ R) (z : ℂ) (hz : ‖z‖ ≤ R) :
    ‖higherKernelScalarNormalizedResponse J B f z‖ ≤
      ((Fintype.card ι : ℝ) *
        (higherKernelCompactBound 0 B (B * (R + 1) ^ 2) * B) * ‖f‖) / (R + 1) := by
  apply Complex.norm_dslope_le_div_of_mapsTo_ball
    (differentiable_higherKernelScaledResponse J B hB f 0).differentiableOn
  · intro w hw
    rw [higherKernelScaledResponse_scalar_zero, mem_closedBall, dist_zero_right]
    simpa only [Int.cast_zero, abs_zero, zero_add] using
      norm_higherKernelScaledResponse_le J B hB f 0 (R + 1) (by linarith) w
        ((show ‖w‖ < R + 1 by simpa only [mem_ball, dist_zero_right] using hw).le)
  · change dist z 0 < R + 1
    rw [dist_zero_right]
    linarith

/-- The holomorphic energy curve agrees with its real-energy formula on the real axis. -/
theorem higherKernelScaledResponse_ofReal {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (f : LowBandHilbert J B) (j : ℤ) (t : ℝ) :
    higherKernelScaledResponse J B f j t =
      higherKernelResponse J B f j ((|(j : ℝ)| + B * t ^ 2 : ℝ) : ℂ) := by
  simp [higherKernelScaledResponse]

/-- The disk estimate has exponential growth linear in the band width. -/
theorem norm_higherKernelScaledResponse_le_exp {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 < B) (f : LowBandHilbert J B) (j : ℤ)
    (hj : |(j : ℝ)| ≤ B) (R : ℝ) (hR : 0 ≤ R) (z : ℂ) (hz : ‖z‖ ≤ R) :
    ‖higherKernelScaledResponse J B f j z‖ ≤
      (Fintype.card ι : ℝ) *
        (16 * π ^ 2 * (R ^ 2 + 2) * B ^ 2 *
          Real.exp (8 * π * Real.sqrt (R ^ 2 + 2) * B)) * ‖f‖ := by
  have hc := higherKernelCompactBound_scaled_le j B (|(j : ℝ)| + B * R ^ 2)
    (R ^ 2 + 1) hB.le (by positivity) hj (by nlinarith)
  calc
    _ ≤ (Fintype.card ι : ℝ) *
        (higherKernelCompactBound j B (|(j : ℝ)| + B * R ^ 2) * B) * ‖f‖ :=
      norm_higherKernelScaledResponse_le J B hB f j R hR z hz
    _ ≤ (Fintype.card ι : ℝ) *
        ((16 * π ^ 2 * ((R ^ 2 + 1) + 1) * B *
          Real.exp (8 * π * Real.sqrt ((R ^ 2 + 1) + 1) * B)) * B) * ‖f‖ := by
      gcongr
    _ = _ := by congr 2; ring_nf

/-- Fubini identifies each low-band response with the actual compressed kernel pairing. -/
theorem higherKernelRowResponse_pairing (j J : ℤ) (B : ℝ)
    (g : LowBandRow j B) (f : LowBandRow J B) :
    Integrable (fun e : ℝ => conj (g e) * higherKernelRowResponse j J B f e)
      ((referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) ∧
    lowBandKernelPairing j J B (fun p => higherKernel j J p.1 p.2) g f =
      ∫ e, conj (g e) * higherKernelRowResponse j J B f e
        ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| B) := by
  have hi := lowBandKernel_integrable (C := 64 * π ^ 2) (by positivity)
    (higherKernel_real_aestronglyMeasurable j J) (higherKernel_ae_weak_bound j J)
    (Lp.memLp g) (Lp.memLp f)
  have heq : (fun e : ℝ => ∫ E,
      weakKernelIntegrand (fun p => higherKernel j J p.1 p.2) g f (e, E)
        ∂(referenceMeasure J).restrict (Ioo |(J : ℝ)| B)) =
      (fun e : ℝ => conj (g e) * higherKernelRowResponse j J B f e) := by
    funext e
    rw [higherKernelRowResponse, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with E
    simp only [weakKernelIntegrand]
    ring
  refine ⟨heq ▸ hi.integral_prod_left, ?_⟩
  rw [lowBandKernelPairing, integral_prod _ hi, heq]

/-- The actual higher kernel instantiates the previously constructed low-band operator. -/
def higherKernelLowBandOperator {ι : Type*} [Fintype ι] (J : ι → ℤ) (B : ℝ) :
    LowBandHilbert J B →L[ℂ] LowBandHilbert J B :=
  lowBandKernelOperator J B (fun i l p => higherKernel (J i) (J l) p.1 p.2)
    (C := 64 * π ^ 2) (by positivity)
    (fun i l => higherKernel_real_aestronglyMeasurable (J i) (J l))
    (fun i l => higherKernel_ae_weak_bound (J i) (J l))

/-- The entire response is the ordinary weak representative of the actual higher operator. -/
theorem inner_higherKernelLowBandOperator {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (g f : LowBandHilbert J B) :
    inner ℂ g (higherKernelLowBandOperator J B f) =
      ∑ i, ∫ e, conj (g i e) * higherKernelResponse J B f (J i) e
        ∂(referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B) := by
  rw [higherKernelLowBandOperator, inner_lowBandKernelOperator]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [higherKernelResponse, Finset.mul_sum]
  rw [integral_finsetSum Finset.univ (fun l _ =>
    (higherKernelRowResponse_pairing (J i) (J l) B (g i) (f l)).1)]
  exact Finset.sum_congr rfl fun l _ =>
    (higherKernelRowResponse_pairing (J i) (J l) B (g i) (f l)).2

end GapFamily.Analytic
