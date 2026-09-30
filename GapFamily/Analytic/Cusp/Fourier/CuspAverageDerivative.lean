import GapFamily.Analytic.Cusp.Fourier.CuspAverageTraceSlice
import GapFamily.Analytic.Cusp.Fourier.CuspAverageTraceIntegral
import GapFamily.Analytic.Cusp.Fourier.CuspHorizontalMeasure
import GapFamily.Analytic.Modular.Elliptic.ModularInteriorCompactWeight
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Smoothness and energy of the actual horizontal average

The ordinary horizontal average of a genuine smooth automorphic core function
is smooth on positive heights. Its vertical derivative is the averaged actual
vertical derivative, with a convergent half-line energy integral bounded by
the modular gradient energy.
-/

noncomputable section

namespace GapFamily.Analytic

open Set Filter MeasureTheory UpperHalfPlane ModularGradient
open scoped Topology ENNReal Convolution ContDiff

private theorem continuous_cuspAverageDerivative_row (F : smoothCore) {y : ℝ}
    (hy : 0 < y) :
    Continuous (fun x : ℝ => fderiv ℝ F.val (Complex.mk x y) Complex.I) := by
  have hD : ContinuousOn (fun z : ℂ => fderiv ℝ F.val z Complex.I)
      upperHalfPlaneSet :=
    (F.property.1.continuousOn_fderiv_of_isOpen
      isOpen_upperHalfPlaneSet (by simp)).clm_apply continuousOn_const
  apply hD.comp_continuous
  · simp only [cuspPoint_eq]
    fun_prop
  · intro x
    exact hy

/-- Actual differentiation under the ordinary horizontal integral for a genuine
smooth automorphic core function, at every positive height. -/
theorem hasDerivAt_cuspHorizontalAverage (F : smoothCore) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (cuspHorizontalAverage F.val)
      (∫ x in (-1/2 : ℝ)..(1/2),
        fderiv ℝ F.val (Complex.mk x y) Complex.I) y := by
  let J : Set ℝ := Icc (-1/2 : ℝ) (1/2)
  let μ : Measure ℝ := volume.restrict J
  have hs : Ioo (y/2) (y+1) ∈ 𝓝 y := Ioo_mem_nhds (by linarith) (by linarith)
  have hD : ContinuousOn (fun z : ℂ => fderiv ℝ F.val z Complex.I)
      upperHalfPlaneSet :=
    (F.property.1.continuousOn_fderiv_of_isOpen
      isOpen_upperHalfPlaneSet (by simp)).clm_apply continuousOn_const
  have hprod : ContinuousOn
      (fun p : ℝ × ℝ => fderiv ℝ F.val (Complex.mk p.1 p.2) Complex.I)
      (J ×ˢ Icc (y/2) (y+1)) := by
    apply hD.comp (by
      simp only [cuspPoint_eq]
      fun_prop)
    intro p hp
    change 0 < p.2
    linarith [hp.2.1]
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hprod
  have hm : ∀ᶠ t in 𝓝 y, AEStronglyMeasurable
      (fun x : ℝ => F.val (Complex.mk x t)) μ := by
    filter_upwards [Ioi_mem_nhds hy] with t ht
    exact (contDiff_cuspHorizontalSlice F.property.1 ht).continuous.aestronglyMeasurable
  have hi : Integrable (fun x : ℝ => F.val (Complex.mk x y)) μ :=
    (contDiff_cuspHorizontalSlice F.property.1 hy).continuous.integrableOn_Icc
  have hDm : AEStronglyMeasurable
      (fun x : ℝ => fderiv ℝ F.val (Complex.mk x y) Complex.I) μ :=
    (continuous_cuspAverageDerivative_row F hy).aestronglyMeasurable
  have hb : ∀ᵐ x ∂μ, ∀ t ∈ Ioo (y/2) (y+1),
      ‖fderiv ℝ F.val (Complex.mk x t) Complex.I‖ ≤ B := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with x hx
    intro t ht
    exact hB (x, t) ⟨hx, ⟨ht.1.le, ht.2.le⟩⟩
  have hdiff : ∀ᵐ x ∂μ, ∀ t ∈ Ioo (y/2) (y+1),
      HasDerivAt (fun r : ℝ => F.val (Complex.mk x r))
        (fderiv ℝ F.val (Complex.mk x t) Complex.I) t := by
    exact Eventually.of_forall (fun x t ht =>
      hasDerivAt_cuspVerticalSlice F.property.1 x (by linarith [ht.1]))
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (bound := fun _ => B) hs hm hi hDm hb (integrable_const B) hdiff).2
  change HasDerivAt (fun t : ℝ => ∫ x in (-1/2 : ℝ)..(1/2), F.val (Complex.mk x t))
    (∫ x in (-1/2 : ℝ)..(1/2), fderiv ℝ F.val (Complex.mk x y) Complex.I) y
  simpa only [μ, J, cuspHorizontalAverage, cuspHorizontalSlice,
    integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (by norm_num : (-1/2 : ℝ) ≤ 1/2)] using h

theorem deriv_cuspHorizontalAverage (F : smoothCore) {y : ℝ} (hy : 0 < y) :
    deriv (cuspHorizontalAverage F.val) y =
      ∫ x in (-1/2 : ℝ)..(1/2), fderiv ℝ F.val (Complex.mk x y) Complex.I :=
  (hasDerivAt_cuspHorizontalAverage F hy).deriv

/-- The literal averaged vertical derivative varies continuously on positive heights. -/
theorem continuousOn_cuspHorizontalAverage_verticalDerivative (F : smoothCore) :
    ContinuousOn (fun y : ℝ => ∫ x in (-1/2 : ℝ)..(1/2),
      fderiv ℝ F.val (Complex.mk x y) Complex.I) (Ioi 0) := by
  change ContinuousOn (cuspHorizontalAverage (fun z => fderiv ℝ F.val z Complex.I)) (Ioi 0)
  exact continuousOn_cuspHorizontalAverage
    ((F.property.1.continuousOn_fderiv_of_isOpen
      isOpen_upperHalfPlaneSet (by simp)).clm_apply continuousOn_const)

theorem continuousOn_deriv_cuspHorizontalAverage (F : smoothCore) :
    ContinuousOn (deriv (cuspHorizontalAverage F.val)) (Ioi 0) := by
  apply (continuousOn_cuspHorizontalAverage_verticalDerivative F).congr
  intro y hy
  exact deriv_cuspHorizontalAverage F hy

/-- The nonnegative extended derivative energy is bounded before assuming any
ordinary integrability in the vertical variable. -/
theorem cuspHorizontalAverage_deriv_lintegral_le (F : smoothCore) :
    (∫⁻ y : ℝ in Ioi 1, ENNReal.ofReal (‖deriv (cuspHorizontalAverage F.val) y‖ ^ 2)) ≤
      ∫⁻ τ : UpperHalfPlane,
        ENNReal.ofReal (‖directional F.val Complex.I τ‖ ^ 2) ∂modularMeasure := by
  let E : ℂ → ℝ := fun z => ‖(z.im : ℂ) * fderiv ℝ F.val z Complex.I‖ ^ 2
  have hD : ContinuousOn (fun z : ℂ => fderiv ℝ F.val z Complex.I)
      upperHalfPlaneSet :=
    (F.property.1.continuousOn_fderiv_of_isOpen
      isOpen_upperHalfPlaneSet (by simp)).clm_apply continuousOn_const
  have hE : ContinuousOn E upperHalfPlaneSet :=
    (((Complex.continuous_ofReal.comp Complex.continuous_im).continuousOn).mul hD).norm.pow 2
  have hcancel {y : ℝ} (hy : y ≠ 0) (x : ℝ) :
      (1 / y ^ 2) * E (Complex.mk x y) =
        ‖fderiv ℝ F.val (Complex.mk x y) Complex.I‖ ^ 2 := by
    simp only [E, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    field_simp
  change (∫⁻ y : ℝ in Ioi 1, ENNReal.ofReal (‖deriv (cuspHorizontalAverage F.val) y‖ ^ 2)) ≤
    ∫⁻ τ : UpperHalfPlane, ENNReal.ofReal (E τ) ∂modularMeasure
  calc
    _ ≤ ∫⁻ τ : UpperHalfPlane in {τ | 1 < τ.im}, ENNReal.ofReal (E τ)
        ∂modularMeasure := by
      rw [lintegral_modular_highCusp E hE le_rfl]
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      have hy0 : 0 < y := zero_lt_one.trans hy
      simp_rw [hcancel hy0.ne']
      rw [restrict_Ioo_eq_restrict_Ioc]
      have hc := continuous_cuspAverageDerivative_row F hy0
      have hi : IntegrableOn
          (fun x : ℝ => ‖fderiv ℝ F.val (Complex.mk x y) Complex.I‖ ^ 2)
          (Ioc (-1/2 : ℝ) (1/2)) :=
        (hc.norm.pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self
      rw [← ofReal_integral_eq_lintegral_ofReal hi
        (Eventually.of_forall (fun _ => sq_nonneg _)),
        ← intervalIntegral.integral_of_le (by norm_num : (-1/2 : ℝ) ≤ 1/2),
        deriv_cuspHorizontalAverage F hy0]
      exact ENNReal.ofReal_le_ofReal (cusp_horizontal_integral_sq_le hc)
    _ ≤ _ := lintegral_mono' Measure.restrict_le_self (fun _ => le_rfl)

/-- The actual averaged vertical derivative has a genuinely convergent ordinary
energy integral on the half-line, controlled by the true modular core gradient. -/
theorem cuspHorizontalAverage_deriv_integrable_and_le (F : smoothCore) :
    IntegrableOn (fun y : ℝ => ‖deriv (cuspHorizontalAverage F.val) y‖ ^ 2) (Ioi 1) ∧
      (∫ y : ℝ in Ioi 1, ‖deriv (cuspHorizontalAverage F.val) y‖ ^ 2) ≤
        ‖coreGradient F‖ ^ 2 := by
  have henergy : Integrable (fun τ : UpperHalfPlane =>
      ‖directional F.val Complex.I τ‖ ^ 2) modularMeasure :=
    (memLp_two_iff_integrable_sq_norm F.property.2.2.2.2.aestronglyMeasurable).mp
      F.property.2.2.2.2
  have h := cuspHorizontalAverage_deriv_lintegral_le F
  rw [← ofReal_integral_eq_lintegral_ofReal henergy
    (Eventually.of_forall (fun _ => sq_nonneg _))] at h
  have hc : ContinuousOn (fun y : ℝ => ‖deriv (cuspHorizontalAverage F.val) y‖ ^ 2)
      (Ioi 1) :=
    ((continuousOn_deriv_cuspHorizontalAverage F).norm.pow 2).mono
      (by
        intro y hy
        change 0 < y
        exact lt_trans (by norm_num : (0 : ℝ) < 1) hy)
  have hi : IntegrableOn (fun y : ℝ => ‖deriv (cuspHorizontalAverage F.val) y‖ ^ 2)
      (Ioi 1) := by
    refine ⟨hc.aestronglyMeasurable measurableSet_Ioi, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have hfinite := h.trans_lt ENNReal.ofReal_lt_top
    simpa only [Real.enorm_eq_ofReal_abs, abs_pow, abs_norm] using hfinite
  refine ⟨hi, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall (fun _ => sq_nonneg _))] at h
  have hb := (ENNReal.ofReal_le_ofReal_iff
    (integral_nonneg (fun τ : UpperHalfPlane => sq_nonneg ‖directional F.val Complex.I τ‖))).mp h
  have he : (∫ τ : UpperHalfPlane, ‖directional F.val Complex.I τ‖ ^ 2 ∂modularMeasure) =
      ‖yComponent F‖ ^ 2 :=
    core_component_integral_norm_sq Complex.I (fun G => G.property.2.2.2.2) F
  rw [he] at hb
  exact hb.trans (by rw [coreGradient_norm_sq]; nlinarith [sq_nonneg ‖xComponent F‖])

/-- Ordinary horizontal averaging preserves full smoothness at positive height.
The compact horizontal cutoff lets the actual average be realized by the pinned
smooth parameter-dependent convolution theorem. -/
theorem contDiffOn_cuspHorizontalAverage (F : smoothCore) :
    ContDiffOn ℝ ∞ (cuspHorizontalAverage F.val) (Ioi 0) := by
  let φ : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
  let J : Set ℝ := Icc (-1/2 : ℝ) (1/2)
  let q : ℝ → ℝ := J.indicator (fun _ => 1)
  let g : ℝ → ℝ → ℂ := fun y x => φ x • F.val (Complex.mk (-x) y)
  let L : ℝ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.lsmul ℝ ℝ
  have hq : Integrable q volume := by
    apply (integrable_indicator_iff measurableSet_Icc).mpr
    exact integrableOn_const (C := (1 : ℝ)) (by simp)
  have hgs : ∀ y x, y ∈ Ioi (0 : ℝ) → x ∉ Metric.closedBall (0 : ℝ) 2 → g y x = 0 := by
    intro y x hy hx
    have hx' : 2 < dist x (0 : ℝ) := by simpa only [Metric.mem_closedBall, not_le] using hx
    have hφ : φ x = 0 := φ.zero_of_le_dist hx'.le
    simp only [g, hφ, zero_smul]
  have hmk : ContDiff ℝ ∞ (fun p : ℝ × ℝ => Complex.mk (-p.2) p.1) := by
    have hx := Complex.ofRealCLM.contDiff.comp (contDiff_snd.neg :
      ContDiff ℝ ∞ (fun p : ℝ × ℝ => -p.2))
    have hy := Complex.ofRealCLM.contDiff.comp (contDiff_fst :
      ContDiff ℝ ∞ (fun p : ℝ × ℝ => p.1))
    simpa only [cuspPoint_eq, Function.comp_apply, Complex.ofRealCLM_apply] using
      hx.add (hy.mul contDiff_const)
  have hg : ContDiffOn ℝ ∞ (Function.uncurry g) (Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ)) := by
    exact (φ.contDiff.comp contDiff_snd).contDiffOn.smul
      (F.property.1.comp hmk.contDiffOn (fun p hp => hp.1))
  have hconv := contDiffOn_convolution_right_with_param_comp (μ := volume)
    (g := g) (f := q) (v := fun _ : ℝ => (0 : ℝ)) (k := Metric.closedBall (0 : ℝ) 2)
    L contDiffOn_const isOpen_Ioi (isCompact_closedBall (0 : ℝ) 2) hgs hq.locallyIntegrable hg
  apply hconv.congr
  intro y hy
  symm
  change (∫ x : ℝ, q x • g y (0 - x)) = cuspHorizontalAverage F.val y
  calc
    _ = ∫ x in J, φ (-x) • F.val (Complex.mk x y) := by
      rw [← integral_indicator measurableSet_Icc]
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => by
        by_cases hx : x ∈ J
        · change x ∈ Icc (-1/2 : ℝ) (1/2) at hx
          simp only [q, g, J, Set.indicator_of_mem hx, zero_sub, neg_neg, one_smul]
        · change x ∉ Icc (-1/2 : ℝ) (1/2) at hx
          simp only [q, J, Set.indicator_of_notMem hx, zero_smul])
    _ = ∫ x in J, F.val (Complex.mk x y) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro x hx
      have hφ : φ (-x) = 1 := by
        apply φ.one_of_mem_closedBall
        change dist (-x) (0 : ℝ) ≤ 1
        simp only [dist_zero_right, norm_neg, Real.norm_eq_abs, abs_le]
        constructor <;> linarith [hx.1, hx.2]
      dsimp only
      rw [hφ, one_smul]
    _ = _ := by
      simp only [J, cuspHorizontalAverage, cuspHorizontalSlice,
        intervalIntegral.integral_of_le (by norm_num : (-1/2 : ℝ) ≤ 1/2),
        integral_Icc_eq_integral_Ioc]

end GapFamily.Analytic
