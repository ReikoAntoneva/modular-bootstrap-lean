import GapFamily.Analytic.Cusp.Fourier.CuspHorizontalTail

/-!
# The literal cusp average is an L² contraction

The ordinary horizontal integral satisfies Jensen's inequality on the
width-one cusp. All convergence statements use the actual restricted modular
measure, and are proved before passing to Hilbert equivalence classes.
-/

noncomputable section
namespace GapFamily.Analytic

open Set MeasureTheory UpperHalfPlane
open scoped ENNReal ContDiff

theorem cuspHorizontalAverage_row_jensen (F : ModularGradient.smoothCore)
    {y : ℝ} (hy : 0 < y) :
    ‖cuspHorizontalAverage F.val y‖ ^ 2 ≤
      ∫ x in (-1/2 : ℝ)..(1/2), ‖cuspHorizontalSlice F.val y x‖ ^ 2 := by
  have hc := (contDiff_cuspHorizontalSlice F.property.1 hy).continuous
  have hn : ‖cuspHorizontalAverage F.val y‖ ≤
      ∫ x in (-1/2 : ℝ)..(1/2), ‖cuspHorizontalSlice F.val y x‖ := by
    simpa only [cuspHorizontalAverage,
      intervalIntegral.integral_of_le (by norm_num : (-1/2 : ℝ) ≤ 1/2)] using
      norm_integral_le_integral_norm (μ := volume.restrict (Ioc (-1/2 : ℝ) (1/2)))
        (cuspHorizontalSlice F.val y)
  have hpos : 0 ≤ ∫ x in (-1/2 : ℝ)..(1/2), ‖cuspHorizontalSlice F.val y x‖ :=
    intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => norm_nonneg _)
  have hC := integral_sq_le_length_mul_integral_sq hc.norm
    (by norm_num : (-1/2 : ℝ) < 1/2)
  exact ((sq_le_sq₀ (norm_nonneg _) hpos).mpr hn).trans (by
    simpa only [show (1/2 : ℝ) - (-1/2) = 1 by norm_num, one_mul] using hC)

theorem continuous_cuspHorizontalAverage_core (F : ModularGradient.smoothCore) :
    Continuous (fun τ : UpperHalfPlane => cuspHorizontalAverage F.val τ.im) :=
  (continuousOn_cuspHorizontalAverage F.property.1.continuousOn).comp_continuous
    UpperHalfPlane.continuous_im (fun τ => τ.im_pos)

/-- Jensen's inequality in the actual high-cusp hyperbolic measure. -/
theorem cuspHorizontalAverage_lintegral_le (F : ModularGradient.smoothCore)
    {H : ℝ} (hH : 1 ≤ H) :
    (∫⁻ τ : UpperHalfPlane in {τ | H < τ.im},
      ENNReal.ofReal (‖cuspHorizontalAverage F.val τ.im‖ ^ 2) ∂modularMeasure) ≤
      ∫⁻ τ : UpperHalfPlane in {τ | H < τ.im},
        ENNReal.ofReal (‖F.val τ‖ ^ 2) ∂modularMeasure := by
  have havg : ContinuousOn (fun z : ℂ => cuspHorizontalAverage F.val z.im)
      upperHalfPlaneSet :=
    (continuousOn_cuspHorizontalAverage F.property.1.continuousOn).comp
      Complex.continuous_im.continuousOn (fun _ hz => hz)
  have hA := lintegral_modular_highCusp (fun z => ‖cuspHorizontalAverage F.val z.im‖^2)
    (havg.norm.pow 2) hH
  change (∫⁻ τ : UpperHalfPlane in {τ | H < τ.im},
    ENNReal.ofReal (‖cuspHorizontalAverage F.val τ.im‖ ^ 2) ∂modularMeasure) = _ at hA
  rw [hA, lintegral_modular_highCusp (fun z => ‖F.val z‖^2)
    (F.property.1.continuousOn.norm.pow 2) hH]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hyH
  have hy : 0 < y := zero_lt_one.trans (hH.trans_lt hyH)
  change (∫⁻ x : ℝ in Ioo (-1/2) (1/2),
      ENNReal.ofReal ((1/y^2) * ‖cuspHorizontalAverage F.val y‖^2)) ≤ _
  rw [lintegral_const, Measure.restrict_apply_univ]
  have hvol : (volume : Measure ℝ) (Ioo (-1/2 : ℝ) (1/2)) = 1 := by
    norm_num [Real.volume_Ioo]
  rw [hvol, mul_one, restrict_Ioo_eq_restrict_Ioc]
  have hc : Continuous (fun x => (1/y^2) * ‖F.val (Complex.mk x y)‖^2) :=
    continuous_const.mul ((contDiff_cuspHorizontalSlice F.property.1 hy).continuous.norm.pow 2)
  have hi : IntegrableOn (fun x => (1/y^2) * ‖F.val (Complex.mk x y)‖^2)
      (Ioc (-1/2 : ℝ) (1/2)) := hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall (fun _ => mul_nonneg (by positivity) (sq_nonneg _))),
    ← intervalIntegral.integral_of_le (by norm_num : (-1/2 : ℝ) ≤ 1/2),
    intervalIntegral.integral_const_mul]
  exact ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left (cuspHorizontalAverage_row_jensen F hy) (by positivity))

/-- The ordinary mean has genuine finite squared norm, bounded by the input norm. -/
theorem cuspHorizontalAverage_integrable_and_le (F : ModularGradient.smoothCore)
    {H : ℝ} (hH : 1 ≤ H) :
    IntegrableOn (fun τ : UpperHalfPlane => ‖cuspHorizontalAverage F.val τ.im‖^2)
        {τ | H < τ.im} modularMeasure ∧
      (∫ τ : UpperHalfPlane in {τ | H < τ.im},
        ‖cuspHorizontalAverage F.val τ.im‖^2 ∂modularMeasure) ≤
      ∫ τ : UpperHalfPlane in {τ | H < τ.im}, ‖F.val τ‖^2 ∂modularMeasure := by
  have hinput : IntegrableOn (fun τ : UpperHalfPlane => ‖F.val τ‖^2)
      {τ | H < τ.im} modularMeasure :=
    ((memLp_two_iff_integrable_sq_norm F.property.2.2.1.aestronglyMeasurable).mp
      F.property.2.2.1).integrableOn
  have h := cuspHorizontalAverage_lintegral_le F hH
  rw [← ofReal_integral_eq_lintegral_ofReal hinput
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))] at h
  have hi : IntegrableOn (fun τ : UpperHalfPlane => ‖cuspHorizontalAverage F.val τ.im‖^2)
      {τ | H < τ.im} modularMeasure := by
    refine ⟨((continuous_cuspHorizontalAverage_core F).norm.pow 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have hfinite := h.trans_lt ENNReal.ofReal_lt_top
    simpa only [Real.enorm_eq_ofReal_abs, abs_pow, abs_norm] using hfinite
  refine ⟨hi, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))] at h
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg (fun _ => sq_nonneg _))).mp h

theorem cuspHorizontalAverage_memLp (F : ModularGradient.smoothCore)
    {H : ℝ} (hH : 1 ≤ H) :
    MemLp (fun τ : UpperHalfPlane => cuspHorizontalAverage F.val τ.im) 2
      (modularMeasure.restrict {τ | H < τ.im}) :=
  (memLp_two_iff_integrable_sq_norm
    (continuous_cuspHorizontalAverage_core F).aestronglyMeasurable).mpr
      (cuspHorizontalAverage_integrable_and_le F hH).1

theorem cuspMean_l2_norm_sq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : Lp ℂ 2 μ) : ‖f‖^2 = ∫ x, ‖f x‖^2 ∂μ := by
  calc
    ‖f‖^2 = (inner ℂ f f).re := norm_sq_eq_re_inner (𝕜 := ℂ) f
    _ = (∫ x, inner ℂ (f x) (f x) ∂μ).re := by rw [L2.inner_def]
    _ = ∫ x, (inner ℂ (f x) (f x)).re ∂μ :=
      (Complex.reCLM.integral_comp_comm (L2.integrable_inner (𝕜 := ℂ) f f)).symm
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall
      (fun x => (norm_sq_eq_re_inner (𝕜 := ℂ) (f x)).symm))

theorem cuspMean_toLp_norm_sq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : α → ℂ) (hf : MemLp f 2 μ) : ‖hf.toLp f‖^2 = ∫ x, ‖f x‖^2 ∂μ := by
  rw [cuspMean_l2_norm_sq]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx]

end GapFamily.Analytic
