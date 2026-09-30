import GapFamily.Analytic.Foundation.CompactKernelIntegral
import GapFamily.Analytic.Cusp.Green.CuspGreenSolutionAnalyticBound

/-!
# The actual Green operator on a finite logarithmic collar

The source and observation measure is literal, unnormalized Lebesgue measure.
The scalar Green integral supplies compact operators into both continuous
functions and `L²`, including at parameter zero.
-/

noncomputable section

namespace GapFamily.Analytic

open MeasureTheory Set

/-- The closed finite interval in the logarithmic cusp coordinate. -/
abbrev CuspGreenCollar (t₀ T : ℝ) := ↥(Icc t₀ T)

/-- Literal Lebesgue measure on the collar, with no normalization. -/
def cuspGreenCollarMeasure (t₀ T : ℝ) : Measure (CuspGreenCollar t₀ T) :=
  volume.comap (Subtype.val : CuspGreenCollar t₀ T → ℝ)

instance cuspGreenCollarMeasure_finite (t₀ T : ℝ) :
    IsFiniteMeasure (cuspGreenCollarMeasure t₀ T) where
  measure_univ_lt_top := by
    rw [cuspGreenCollarMeasure,
      (MeasurableEmbedding.subtype_coe measurableSet_Icc).comap_apply]
    simpa only [image_univ, Subtype.range_coe] using
      ((isCompact_Icc : IsCompact (Icc t₀ T)).measure_lt_top (μ := (volume : Measure ℝ)))

theorem cuspGreenCollarMeasure_univ (t₀ T : ℝ) :
    cuspGreenCollarMeasure t₀ T univ = ENNReal.ofReal (T - t₀) := by
  rw [cuspGreenCollarMeasure,
    (MeasurableEmbedding.subtype_coe measurableSet_Icc).comap_apply]
  simpa only [image_univ, Subtype.range_coe] using (Real.volume_Icc (a := t₀) (b := T))

theorem cuspGreenCollarMeasure_real_univ (t₀ T : ℝ) (hT : t₀ ≤ T) :
    (cuspGreenCollarMeasure t₀ T).real univ = T - t₀ := by
  rw [Measure.real, cuspGreenCollarMeasure_univ, ENNReal.toReal_ofReal (sub_nonneg.mpr hT)]

/-- Spatial joint continuity is proved for the actual scalar integral. -/
theorem continuous_cuspGreen_position (t₀ : ℝ) (κ : ℂ) :
    Continuous (fun p : ℝ × ℝ => cuspGreen t₀ p.1 p.2 κ) := by
  by_cases hκ : κ = 0
  · subst κ
    simp only [cuspGreen_zero]
    fun_prop
  · simp_rw [cuspGreen_eq_quotient _ _ _ hκ]
    fun_prop

/-- The actual Green kernel as a continuous function on the product collar. -/
def cuspGreenCollarKernel (t₀ T : ℝ) (κ : ℂ) :
    C(CuspGreenCollar t₀ T × CuspGreenCollar t₀ T, ℂ) :=
  ⟨fun p => cuspGreen t₀ p.1 p.2 κ,
    (continuous_cuspGreen_position t₀ κ).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))⟩

@[simp] theorem cuspGreenCollarKernel_apply (t₀ T : ℝ) (κ : ℂ)
    (t u : CuspGreenCollar t₀ T) :
    cuspGreenCollarKernel t₀ T κ (t, u) = cuspGreen t₀ t u κ := rfl

/-- Explicit uniform kernel bound on each parameter disk, also at zero. -/
theorem norm_cuspGreenCollarKernel_le (t₀ T R : ℝ) (hT : t₀ ≤ T)
    (κ : ℂ) (hκ : ‖κ‖ ≤ R) :
    ‖cuspGreenCollarKernel t₀ T κ‖ ≤
      (T - t₀) * Real.exp (R * (T + T - 2 * t₀)) := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (sub_nonneg.mpr hT) (Real.exp_pos _).le)).mpr
  intro p
  exact norm_cuspGreen_on_collar_le t₀ T T R p.1 p.2 κ
    p.1.property.1 p.1.property.2 p.2.property.1 p.2.property.2 hκ

/-- The Green response is a genuine bounded operator into continuous functions. -/
def cuspGreenCollarOperator (t₀ T : ℝ) (κ : ℂ) :
    Lp ℂ 2 (cuspGreenCollarMeasure t₀ T) →L[ℂ] C(CuspGreenCollar t₀ T, ℂ) :=
  compactKernelIntegralOperator (cuspGreenCollarMeasure t₀ T) (cuspGreenCollarKernel t₀ T κ)

theorem cuspGreenCollar_integrable (t₀ T : ℝ) (κ : ℂ)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure t₀ T)) (t : CuspGreenCollar t₀ T) :
    Integrable (fun u : CuspGreenCollar t₀ T => cuspGreen t₀ t u κ * f u)
      (cuspGreenCollarMeasure t₀ T) :=
  compactKernelIntegral_integrable _ (cuspGreenCollarKernel t₀ T κ) f t

/-- The continuous response is precisely the ordinary Green integral. -/
theorem cuspGreenCollarOperator_apply (t₀ T : ℝ) (κ : ℂ)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure t₀ T)) (t : CuspGreenCollar t₀ T) :
    cuspGreenCollarOperator t₀ T κ f t =
      ∫ u : CuspGreenCollar t₀ T, cuspGreen t₀ t u κ * f u ∂cuspGreenCollarMeasure t₀ T :=
  compactKernelIntegralOperator_apply _ (cuspGreenCollarKernel t₀ T κ) f t

theorem isCompactOperator_cuspGreenCollarOperator (t₀ T : ℝ) (κ : ℂ) :
    IsCompactOperator (cuspGreenCollarOperator t₀ T κ) :=
  isCompactOperator_compactKernelIntegralOperator _ _

/-- Explicit operator bound into the uniform norm. -/
theorem norm_cuspGreenCollarOperator_le (t₀ T R : ℝ) (hT : t₀ ≤ T)
    (κ : ℂ) (hκ : ‖κ‖ ≤ R) :
    ‖cuspGreenCollarOperator t₀ T κ‖ ≤
      Real.sqrt (T - t₀) * ((T - t₀) * Real.exp (R * (T + T - 2 * t₀))) := by
  apply (norm_compactKernelIntegralOperator_le (cuspGreenCollarMeasure t₀ T)
    (cuspGreenCollarKernel t₀ T κ)).trans
  rw [cuspGreenCollarMeasure_real_univ t₀ T hT]
  exact mul_le_mul_of_nonneg_left (norm_cuspGreenCollarKernel_le t₀ T R hT κ hκ)
    (Real.sqrt_nonneg _)

/-- The same ordinary Green response as an actual `L²` class. -/
def cuspGreenCollarL2Operator (t₀ T : ℝ) (κ : ℂ) :
    Lp ℂ 2 (cuspGreenCollarMeasure t₀ T) →L[ℂ] Lp ℂ 2 (cuspGreenCollarMeasure t₀ T) :=
  (ContinuousMap.toLp 2 (cuspGreenCollarMeasure t₀ T) ℂ).comp
    (cuspGreenCollarOperator t₀ T κ)

theorem isCompactOperator_cuspGreenCollarL2Operator (t₀ T : ℝ) (κ : ℂ) :
    IsCompactOperator (cuspGreenCollarL2Operator t₀ T κ) :=
  (isCompactOperator_cuspGreenCollarOperator t₀ T κ).clm_comp
    (ContinuousMap.toLp 2 (cuspGreenCollarMeasure t₀ T) ℂ)

theorem cuspGreenCollarL2Operator_coeFn (t₀ T : ℝ) (κ : ℂ)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure t₀ T)) :
    ⇑(cuspGreenCollarL2Operator t₀ T κ f) =ᵐ[cuspGreenCollarMeasure t₀ T]
      (fun t => ∫ u : CuspGreenCollar t₀ T,
        cuspGreen t₀ t u κ * f u ∂cuspGreenCollarMeasure t₀ T) := by
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (μ := cuspGreenCollarMeasure t₀ T)
    (𝕜 := ℂ) (cuspGreenCollarOperator t₀ T κ f)] with t ht
  exact ht.trans (cuspGreenCollarOperator_apply t₀ T κ f t)

theorem norm_cuspGreenCollar_toL2_le (t₀ T : ℝ) (hT : t₀ ≤ T) :
    ‖(ContinuousMap.toLp 2 (cuspGreenCollarMeasure t₀ T) ℂ :
      C(CuspGreenCollar t₀ T, ℂ) →L[ℂ] Lp ℂ 2 (cuspGreenCollarMeasure t₀ T))‖ ≤
      Real.sqrt (T - t₀) := by
  have h := ContinuousMap.toLp_norm_le (p := 2) (E := ℂ) (𝕜 := ℂ)
    (cuspGreenCollarMeasure t₀ T)
  simp only [ENNReal.toReal_ofNat] at h
  change ‖(ContinuousMap.toLp 2 (cuspGreenCollarMeasure t₀ T) ℂ :
    C(CuspGreenCollar t₀ T, ℂ) →L[ℂ] Lp ℂ 2 (cuspGreenCollarMeasure t₀ T))‖ ≤
    ((cuspGreenCollarMeasure t₀ T).real univ) ^ (2 : ℝ)⁻¹ at h
  simpa only [cuspGreenCollarMeasure_real_univ t₀ T hT, Real.sqrt_eq_rpow, one_div] using h

/-- The `L²` operator bound uses the actual collar mass twice. -/
theorem norm_cuspGreenCollarL2Operator_le (t₀ T R : ℝ) (hT : t₀ ≤ T)
    (κ : ℂ) (hκ : ‖κ‖ ≤ R) :
    ‖cuspGreenCollarL2Operator t₀ T κ‖ ≤
      (T - t₀) ^ 2 * Real.exp (R * (T + T - 2 * t₀)) := by
  calc
    _ ≤ ‖(ContinuousMap.toLp 2 (cuspGreenCollarMeasure t₀ T) ℂ :
        C(CuspGreenCollar t₀ T, ℂ) →L[ℂ] Lp ℂ 2 (cuspGreenCollarMeasure t₀ T))‖ *
        ‖cuspGreenCollarOperator t₀ T κ‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ Real.sqrt (T - t₀) *
        (Real.sqrt (T - t₀) * ((T - t₀) * Real.exp (R * (T + T - 2 * t₀)))) :=
      mul_le_mul (norm_cuspGreenCollar_toL2_le t₀ T hT)
        (norm_cuspGreenCollarOperator_le t₀ T R hT κ hκ)
        (norm_nonneg (cuspGreenCollarOperator t₀ T κ)) (Real.sqrt_nonneg _)
    _ = _ := by rw [← mul_assoc, Real.mul_self_sqrt (sub_nonneg.mpr hT)]; ring

/-- Restriction of an actual continuous source to the measured collar. -/
def cuspGreenCollarSource (t₀ T : ℝ) (f : ℝ → ℂ) (hf : Continuous f) :
    Lp ℂ 2 (cuspGreenCollarMeasure t₀ T) :=
  ContinuousMap.toLp 2 (cuspGreenCollarMeasure t₀ T) ℂ
    ⟨fun u : CuspGreenCollar t₀ T => f u, hf.comp continuous_subtype_val⟩

theorem cuspGreenCollarSource_coeFn (t₀ T : ℝ) (f : ℝ → ℂ) (hf : Continuous f) :
    ⇑(cuspGreenCollarSource t₀ T f hf) =ᵐ[cuspGreenCollarMeasure t₀ T]
      (fun u : CuspGreenCollar t₀ T => f u) :=
  ContinuousMap.coeFn_toLp _ _

/-- On ordinary sources the operator is the literal real-coordinate integral. -/
theorem cuspGreenCollarOperator_apply_source (t₀ T : ℝ) (κ : ℂ)
    (f : ℝ → ℂ) (hf : Continuous f) (t : CuspGreenCollar t₀ T) :
    cuspGreenCollarOperator t₀ T κ (cuspGreenCollarSource t₀ T f hf) t =
      ∫ u : ℝ in Icc t₀ T, cuspGreen t₀ t u κ * f u := by
  rw [cuspGreenCollarOperator_apply]
  calc
    _ = ∫ u : CuspGreenCollar t₀ T,
        cuspGreen t₀ t u κ * f u ∂cuspGreenCollarMeasure t₀ T := by
      apply integral_congr_ae
      filter_upwards [cuspGreenCollarSource_coeFn t₀ T f hf] with u hu
      rw [hu]
    _ = _ := integral_subtype_comap measurableSet_Icc (fun u => cuspGreen t₀ t u κ * f u)

/-- The finite operator agrees with the actual half-line Green solution for
every continuous source vanishing above the collar. -/
theorem cuspGreenCollarOperator_eq_solution (t₀ T : ℝ) (hT : t₀ ≤ T) (κ : ℂ)
    (f : ℝ → ℂ) (hf : Continuous f) (hfT : ∀ u : ℝ, T < u → f u = 0)
    (t : CuspGreenCollar t₀ T) :
    cuspGreenCollarOperator t₀ T κ (cuspGreenCollarSource t₀ T f hf) t =
      cuspGreenSolution t₀ κ f t := by
  rw [cuspGreenCollarOperator_apply_source,
    cuspGreenSolution_eq_interval t₀ T t hT κ hfT,
    intervalIntegral.integral_of_le hT, integral_Icc_eq_integral_Ioc]

/-- Every collar response has literal zero Dirichlet boundary value. -/
theorem cuspGreenCollarOperator_boundary (t₀ T : ℝ) (hT : t₀ ≤ T) (κ : ℂ)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure t₀ T)) :
    cuspGreenCollarOperator t₀ T κ f ⟨t₀, le_rfl, hT⟩ = 0 := by
  rw [cuspGreenCollarOperator_apply]
  apply integral_eq_zero_of_ae
  filter_upwards [] with u
  simp only [cuspGreen_boundary_left t₀ u u.property.1 κ, zero_mul, Pi.zero_apply]

end GapFamily.Analytic
