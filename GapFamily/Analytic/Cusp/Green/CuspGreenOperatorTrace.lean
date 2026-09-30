import GapFamily.Analytic.Cusp.Green.CuspGreenOperatorBasic
import GapFamily.Analytic.Cusp.Green.CuspGreenTraceAnalytic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! The actual boundary derivative trace on finite-collar `L²` sources. -/

noncomputable section
namespace GapFamily.Analytic
open MeasureTheory Set Filter
open scoped ComplexConjugate Topology

/-- The boundary derivative kernel on the source collar. -/
def cuspGreenCollarTraceKernel (t₀ T : ℝ) (κ : ℂ) : C(CuspGreenCollar t₀ T, ℂ) :=
  ⟨fun u => Complex.exp (-κ * (((u : ℝ) - t₀ : ℝ) : ℂ)), by fun_prop⟩

/-- The genuine boundary trace as a bounded linear functional on the source space. -/
def cuspGreenCollarTraceOperator (t₀ T : ℝ) (κ : ℂ) :
    Lp ℂ 2 (cuspGreenCollarMeasure t₀ T) →L[ℂ] ℂ :=
  innerSL ℂ (ContinuousMap.toLp 2 (cuspGreenCollarMeasure t₀ T) ℂ
    (star (cuspGreenCollarTraceKernel t₀ T κ)))

theorem cuspGreenCollarTrace_integrable (t₀ T : ℝ) (κ : ℂ)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure t₀ T)) :
    Integrable (fun u : CuspGreenCollar t₀ T =>
      Complex.exp (-κ * (((u : ℝ) - t₀ : ℝ) : ℂ)) * f u) (cuspGreenCollarMeasure t₀ T) := by
  apply (L2.integrable_inner (ContinuousMap.toLp 2 (cuspGreenCollarMeasure t₀ T) ℂ
    (star (cuspGreenCollarTraceKernel t₀ T κ))) f).congr
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (μ := cuspGreenCollarMeasure t₀ T)
    (𝕜 := ℂ) (star (cuspGreenCollarTraceKernel t₀ T κ))] with u hu
  rw [RCLike.inner_apply', hu]
  simp [cuspGreenCollarTraceKernel]

/-- The functional is its ordinary convergent source integral. -/
theorem cuspGreenCollarTraceOperator_apply (t₀ T : ℝ) (κ : ℂ)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure t₀ T)) :
    cuspGreenCollarTraceOperator t₀ T κ f = ∫ u : CuspGreenCollar t₀ T,
      Complex.exp (-κ * (((u : ℝ) - t₀ : ℝ) : ℂ)) * f u ∂cuspGreenCollarMeasure t₀ T := by
  change inner ℂ _ f = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (μ := cuspGreenCollarMeasure t₀ T)
    (𝕜 := ℂ) (star (cuspGreenCollarTraceKernel t₀ T κ))] with u hu
  rw [RCLike.inner_apply', hu]
  simp [cuspGreenCollarTraceKernel]

theorem norm_cuspGreenCollarTraceKernel_le (t₀ T R : ℝ) (κ : ℂ) (hκ : ‖κ‖ ≤ R) :
    ‖cuspGreenCollarTraceKernel t₀ T κ‖ ≤ Real.exp (R * (T - t₀)) := by
  apply (ContinuousMap.norm_le _ (Real.exp_pos _).le).mpr
  intro u
  exact norm_cuspGreenBoundaryTraceKernel_le t₀ T R u κ u.property.1 u.property.2 hκ

/-- A finite source mass controls the functional by the uniform kernel norm. -/
theorem norm_cuspGreenCollarTraceOperator_le_kernel (t₀ T : ℝ) (hT : t₀ ≤ T) (κ : ℂ) :
    ‖cuspGreenCollarTraceOperator t₀ T κ‖ ≤
      Real.sqrt (T - t₀) * ‖cuspGreenCollarTraceKernel t₀ T κ‖ := by
  rw [cuspGreenCollarTraceOperator, innerSL_apply_norm]
  calc
    _ ≤ ‖(ContinuousMap.toLp 2 (cuspGreenCollarMeasure t₀ T) ℂ :
        C(CuspGreenCollar t₀ T, ℂ) →L[ℂ] Lp ℂ 2 (cuspGreenCollarMeasure t₀ T))‖ *
        ‖star (cuspGreenCollarTraceKernel t₀ T κ)‖ :=
      (ContinuousMap.toLp (E := ℂ) 2 (cuspGreenCollarMeasure t₀ T) ℂ).le_opNorm _
    _ ≤ _ := by
      rw [norm_star (cuspGreenCollarTraceKernel t₀ T κ)]
      exact mul_le_mul_of_nonneg_right (norm_cuspGreenCollar_toL2_le t₀ T hT) (norm_nonneg _)

/-- The trace has the expected square-root collar-mass operator bound. -/
theorem norm_cuspGreenCollarTraceOperator_le (t₀ T R : ℝ) (hT : t₀ ≤ T)
    (κ : ℂ) (hκ : ‖κ‖ ≤ R) :
    ‖cuspGreenCollarTraceOperator t₀ T κ‖ ≤
      Real.sqrt (T - t₀) * Real.exp (R * (T - t₀)) := by
  exact (norm_cuspGreenCollarTraceOperator_le_kernel t₀ T hT κ).trans
    (mul_le_mul_of_nonneg_left (norm_cuspGreenCollarTraceKernel_le t₀ T R κ hκ)
      (Real.sqrt_nonneg _))

/-- Throughout the closed physical half-plane the trace norm is bounded just by collar mass. -/
theorem norm_cuspGreenCollarTraceOperator_halfplane_le (t₀ T : ℝ) (hT : t₀ ≤ T)
    {κ : ℂ} (hκ : 0 ≤ κ.re) :
    ‖cuspGreenCollarTraceOperator t₀ T κ‖ ≤ Real.sqrt (T - t₀) := by
  have hk : ‖cuspGreenCollarTraceKernel t₀ T κ‖ ≤ 1 := by
    apply (ContinuousMap.norm_le _ zero_le_one).mpr
    intro u
    change ‖Complex.exp (-κ * (((u : ℝ) - t₀ : ℝ) : ℂ))‖ ≤ 1
    rw [Complex.norm_exp, Real.exp_le_one_iff]
    simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
      Complex.neg_im, Complex.ofReal_im, mul_zero, sub_zero]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hκ) (sub_nonneg.mpr u.property.1)
  simpa only [mul_one] using (norm_cuspGreenCollarTraceOperator_le_kernel t₀ T hT κ).trans
    (mul_le_mul_of_nonneg_left hk (Real.sqrt_nonneg _))

/-- Every source class is also ordinarily integrable on the finite collar. -/
theorem cuspGreenCollarSource_integrable (t₀ T : ℝ)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure t₀ T)) :
    Integrable f (cuspGreenCollarMeasure t₀ T) := by
  simpa using cuspGreenCollarTrace_integrable t₀ T 0 f

@[simp] theorem cuspGreenCollarTraceOperator_zero (t₀ T : ℝ)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure t₀ T)) :
    cuspGreenCollarTraceOperator t₀ T 0 f =
      ∫ u : CuspGreenCollar t₀ T, f u ∂cuspGreenCollarMeasure t₀ T := by
  simp [cuspGreenCollarTraceOperator_apply]

/-- The ordinary-source trace is recovered exactly. -/
theorem cuspGreenCollarTraceOperator_eq_trace (t₀ T : ℝ) (hT : t₀ ≤ T) (κ : ℂ)
    (f : ℝ → ℂ) (hf : Continuous f) (hfT : ∀ u : ℝ, T < u → f u = 0) :
    cuspGreenCollarTraceOperator t₀ T κ (cuspGreenCollarSource t₀ T f hf) =
      cuspGreenBoundaryTrace t₀ κ f := by
  rw [cuspGreenCollarTraceOperator_apply]
  calc
    _ = ∫ u : CuspGreenCollar t₀ T,
        Complex.exp (-κ * (((u : ℝ) - t₀ : ℝ) : ℂ)) * f u ∂cuspGreenCollarMeasure t₀ T := by
      apply integral_congr_ae
      filter_upwards [cuspGreenCollarSource_coeFn t₀ T f hf] with u hu
      rw [hu]
    _ = ∫ u : ℝ in Icc t₀ T, Complex.exp (-κ * ((u - t₀ : ℝ) : ℂ)) * f u :=
      integral_subtype_comap measurableSet_Icc
        (fun u : ℝ => Complex.exp (-κ * ((u - t₀ : ℝ) : ℂ)) * f u)
    _ = _ := by
      rw [cuspGreenBoundaryTrace_eq_interval t₀ T hT κ hfT,
        intervalIntegral.integral_of_le hT, integral_Icc_eq_integral_Ioc]

/-- The same source response evaluated at an arbitrary real observation position. -/
def cuspGreenCollarResponse (t₀ T : ℝ) (κ : ℂ)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure t₀ T)) (t : ℝ) : ℂ :=
  ∫ u : CuspGreenCollar t₀ T, cuspGreen t₀ t u κ * f u ∂cuspGreenCollarMeasure t₀ T

theorem cuspGreenCollarResponse_integrable (t₀ T t : ℝ) (κ : ℂ)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure t₀ T)) :
    Integrable (fun u : CuspGreenCollar t₀ T => cuspGreen t₀ t u κ * f u)
      (cuspGreenCollarMeasure t₀ T) := by
  let k : C(Unit × CuspGreenCollar t₀ T, ℂ) :=
    ⟨fun p => cuspGreen t₀ t p.2 κ,
      (cuspGreen_continuous_source t₀ t κ).comp (continuous_subtype_val.comp continuous_snd)⟩
  exact compactKernelIntegral_integrable (cuspGreenCollarMeasure t₀ T) k f ()

@[simp] theorem cuspGreenCollarResponse_boundary (t₀ T : ℝ) (κ : ℂ)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure t₀ T)) :
    cuspGreenCollarResponse t₀ T κ f t₀ = 0 := by
  unfold cuspGreenCollarResponse
  apply integral_eq_zero_of_ae
  filter_upwards [] with u
  simp only [cuspGreen_boundary_left t₀ u u.property.1 κ, zero_mul, Pi.zero_apply]

theorem cuspGreenCollarResponse_eq_operator (t₀ T : ℝ) (κ : ℂ)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure t₀ T)) (t : CuspGreenCollar t₀ T) :
    cuspGreenCollarResponse t₀ T κ f t = cuspGreenCollarOperator t₀ T κ f t :=
  (cuspGreenCollarOperator_apply t₀ T κ f t).symm

private theorem cuspGreenCollarMeasure_nullSingleton (t₀ T : ℝ) : NullSingletonClass (cuspGreenCollarMeasure t₀ T) where
  measure_singleton u := by
    rw [cuspGreenCollarMeasure, (MeasurableEmbedding.subtype_coe measurableSet_Icc).comap_apply]
    simp

/-- The real response of any collar L² source has the actual bounded trace functional
as its derivative from increasing cusp height, including at κ = 0. -/
theorem hasDerivWithinAt_cuspGreenCollarResponse_boundary (t₀ T : ℝ) (hT : t₀ ≤ T) (κ : ℂ)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure t₀ T)) :
    HasDerivWithinAt (cuspGreenCollarResponse t₀ T κ f)
      (cuspGreenCollarTraceOperator t₀ T κ f) (Ici t₀) t₀ := by
  unfold cuspGreenCollarResponse
  rw [cuspGreenCollarTraceOperator_apply]
  let μ := cuspGreenCollarMeasure t₀ T
  let : NullSingletonClass μ := cuspGreenCollarMeasure_nullSingleton t₀ T
  have hzero (u : CuspGreenCollar t₀ T) : cuspGreen t₀ t₀ u κ = 0 :=
    cuspGreen_boundary_left t₀ u u.property.1 κ
  have hf : Integrable f μ := cuspGreenCollarSource_integrable t₀ T f
  let b : ℝ := Real.exp (‖κ‖ * (1 + T - t₀))
  let F : ℝ → CuspGreenCollar t₀ T → ℂ :=
    fun t u => slope (fun t => cuspGreen t₀ t u κ * f u) t₀ t
  have hmeas : ∀ t, AEStronglyMeasurable (F t) μ := by
    intro t
    have hc : Continuous (fun u : CuspGreenCollar t₀ T => cuspGreen t₀ t u κ) :=
      (cuspGreen_continuous_source t₀ t κ).comp continuous_subtype_val
    apply ((hc.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f)).const_smul ((t - t₀ : ℝ)⁻¹)).congr
    filter_upwards [] with u
    simp only [F, slope_def_module, hzero, zero_mul, sub_zero, Pi.smul_apply, Pi.mul_apply]
  have hbound : ∀ᶠ t in 𝓝[>] t₀, ∀ᵐ u ∂μ, ‖F t u‖ ≤ b * ‖f u‖ := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show t₀ < t₀ + 1 by linarith))] with t ht ht1
    filter_upwards [] with u
    have hd : 0 < t - t₀ := sub_pos.mpr ht
    have hb : ‖cuspGreen t₀ t u κ‖ ≤ (t - t₀) * b := by
      calc
        _ ≤ (min t u - t₀) * Real.exp (‖κ‖ * (t + u - 2 * t₀)) :=
          norm_cuspGreen_le t₀ t u ht.le u.property.1 κ
        _ ≤ (t - t₀) * b := by
          apply mul_le_mul
          · exact sub_le_sub_right (min_le_left _ _) _
          · apply Real.exp_le_exp.mpr
            exact mul_le_mul_of_nonneg_left (by linarith [u.property.2, (show t < t₀ + 1 from ht1)]) (norm_nonneg _)
          · positivity
          · exact hd.le
    simp only [F, slope_def_module,
      cuspGreen_boundary_left t₀ _ u.property.1 κ, zero_mul, sub_zero,
      norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hd, norm_mul]
    calc
      (t - t₀)⁻¹ * (‖cuspGreen t₀ t u κ‖ * ‖f u‖) ≤
          (t - t₀)⁻¹ * (((t - t₀) * b) * ‖f u‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hb (norm_nonneg _)) (inv_nonneg.mpr hd.le)
      _ = b * ‖f u‖ := by field_simp
  have hlim : ∀ᵐ u ∂μ, Tendsto (fun t => F t u) (𝓝[>] t₀)
      (𝓝 (Complex.exp (-κ * ((u - t₀ : ℝ) : ℂ)) * f u)) := by
    filter_upwards [μ.ae_ne (⟨t₀, le_rfl, hT⟩ : CuspGreenCollar t₀ T)] with u hu
    have hu' : t₀ < (u : ℝ) := lt_of_le_of_ne u.property.1 (by
      intro he
      exact hu (Subtype.ext he.symm))
    have hd := (cuspGreen_hasDerivAt_left t₀ t₀ u hu' κ).mul_const (f u)
    have he : cuspGreenLeftSlope t₀ t₀ u κ = Complex.exp (-κ * ((u - t₀ : ℝ) : ℂ)) := by
      unfold cuspGreenLeftSlope
      rw [show t₀ + (u : ℝ) - 2 * t₀ = u - t₀ by ring]
      ring
    rw [he] at hd
    simpa only [Ici_sdiff_left] using
      (hasDerivWithinAt_iff_tendsto_slope.mp (hd.hasDerivWithinAt (s := Ici t₀)))
  have hconv := tendsto_integral_filter_of_dominated_convergence
    (fun u => b * ‖f u‖) (Eventually.of_forall hmeas) hbound (hf.norm.const_mul b) hlim
  rw [hasDerivWithinAt_iff_tendsto_slope, Ici_sdiff_left]
  convert hconv using 1
  ext t
  simp only [F, slope_def_module,
    hzero, zero_mul, integral_zero, sub_zero,
    integral_smul]
  rfl

theorem derivWithin_cuspGreenCollarResponse_boundary (t₀ T : ℝ) (hT : t₀ ≤ T) (κ : ℂ)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure t₀ T)) :
    derivWithin (cuspGreenCollarResponse t₀ T κ f) (Ici t₀) t₀ =
      cuspGreenCollarTraceOperator t₀ T κ f :=
  (hasDerivWithinAt_cuspGreenCollarResponse_boundary t₀ T hT κ f).derivWithin
    (uniqueDiffWithinAt_Ici t₀)

end GapFamily.Analytic
