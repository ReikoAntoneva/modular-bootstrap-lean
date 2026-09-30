import GapFamily.Analytic.Cusp.Fourier.CuspHorizontalSlice
import GapFamily.Analytic.Cusp.Fourier.CuspHorizontalMeasure

/-!
# Nonzero horizontal mode in the actual modular cusp
The ordinary horizontal average is subtracted before estimating the high-cusp tail. The actual inverse-square measure and a unit-interval Poincare estimate give the explicit factor H⁻² against the genuine horizontal gradient energy.
-/
noncomputable section
namespace GapFamily.Analytic
open Set MeasureTheory UpperHalfPlane
open scoped ENNReal ContDiff

private theorem cusp_row_lintegral (f : ℝ → ℝ) (hf : Continuous f)
    (hpos : ∀ x, 0 ≤ f x) :
    (∫⁻ x : ℝ in Ioo (-1/2) (1/2), ENNReal.ofReal (f x)) =
      ENNReal.ofReal (∫ x in (-1/2 : ℝ)..(1/2), f x) := by
  rw [restrict_Ioo_eq_restrict_Ioc]
  have hi : IntegrableOn f (Ioc (-1/2 : ℝ) (1/2)) :=
    hf.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hpos),
    ← intervalIntegral.integral_of_le (by norm_num : (-1/2 : ℝ) ≤ 1/2)]

def cuspHorizontalEnergy (F : ℂ → ℂ) (z : ℂ) : ℝ :=
  ‖(z.im : ℂ) * fderiv ℝ F z 1‖ ^ 2

theorem continuousOn_cuspHorizontalEnergy {F : ℂ → ℂ}
    (hF : ContDiffOn ℝ ∞ F upperHalfPlaneSet) :
    ContinuousOn (cuspHorizontalEnergy F) upperHalfPlaneSet := by
  have hd : ContinuousOn (fun z => fderiv ℝ F z 1) upperHalfPlaneSet :=
    (hF.continuousOn_fderiv_of_isOpen isOpen_upperHalfPlaneSet (by simp)).clm_apply
      continuousOn_const
  exact (((Complex.continuous_ofReal.comp Complex.continuous_im).continuousOn).mul hd).norm.pow 2

theorem cuspHorizontalEnergy_cancel (F : ℂ → ℂ) {y : ℝ} (hy : y ≠ 0) (x : ℝ) :
    (1 / y ^ 2) * cuspHorizontalEnergy F (Complex.mk x y) =
      ‖fderiv ℝ F (Complex.mk x y) 1‖ ^ 2 := by
  simp only [cuspHorizontalEnergy, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    mul_pow, sq_abs]
  field_simp

theorem cuspHorizontal_row_bound (F : ModularGradient.smoothCore)
    {H y : ℝ} (hH : 1 ≤ H) (hyH : H < y) :
    (∫⁻ x : ℝ in Ioo (-1/2) (1/2),
      ENNReal.ofReal ((1 / y ^ 2) * ‖cuspHorizontalResidual F.val (Complex.mk x y)‖ ^ 2)) ≤
      ENNReal.ofReal (1 / H ^ 2) *
        ∫⁻ x : ℝ in Ioo (-1/2) (1/2),
          ENNReal.ofReal ((1 / y ^ 2) * cuspHorizontalEnergy F.val (Complex.mk x y)) := by
  have hHpos : 0 < H := zero_lt_one.trans_le hH
  have hy : 0 < y := hHpos.trans hyH
  have hS := contDiff_cuspHorizontalSlice F.property.1 hy
  have hRc : Continuous (fun x => ‖cuspHorizontalResidual F.val (Complex.mk x y)‖ ^ 2) := by
    change Continuous (fun x => ‖cuspHorizontalSlice F.val y x - cuspHorizontalAverage F.val y‖ ^ 2)
    exact (hS.continuous.sub continuous_const).norm.pow 2
  have hDc : Continuous (fun x => ‖fderiv ℝ F.val (Complex.mk x y) 1‖ ^ 2) := by
    have hd := hS.continuous_deriv (by simp)
    convert hd.norm.pow 2 using 1
    funext x
    change ‖fderiv ℝ F.val (Complex.mk x y) 1‖ ^ 2 =
      ‖deriv (cuspHorizontalSlice F.val y) x‖ ^ 2
    rw [deriv_cuspHorizontalSlice F.property.1 hy]
  simp_rw [cuspHorizontalEnergy_cancel F.val hy.ne']
  rw [cusp_row_lintegral
      (fun x => (1 / y ^ 2) * ‖cuspHorizontalResidual F.val (Complex.mk x y)‖ ^ 2)
      (continuous_const.mul hRc)
      (fun x => mul_nonneg (by positivity) (sq_nonneg _)),
    cusp_row_lintegral _ hDc (fun x => sq_nonneg _), intervalIntegral.integral_const_mul]
  have hp := modular_horizontal_poincare F.property.1 hy
  have hw : 1 / y ^ 2 ≤ 1 / H ^ 2 := by
    apply one_div_le_one_div_of_le (sq_pos_of_pos hHpos)
    nlinarith [mul_nonneg (sub_nonneg.mpr hyH.le) (add_nonneg hy.le hHpos.le)]
  have hRn : 0 ≤ ∫ x in (-1/2 : ℝ)..(1/2),
      ‖cuspHorizontalResidual F.val (Complex.mk x y)‖ ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => sq_nonneg _)
  calc
    ENNReal.ofReal ((1 / y ^ 2) * ∫ x in (-1/2 : ℝ)..(1/2),
      ‖cuspHorizontalResidual F.val (Complex.mk x y)‖ ^ 2)
      ≤ ENNReal.ofReal ((1 / H ^ 2) * ∫ x in (-1/2 : ℝ)..(1/2),
        ‖fderiv ℝ F.val (Complex.mk x y) 1‖ ^ 2) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul hw hp hRn (by positivity))
    _ = _ := ENNReal.ofReal_mul (by positivity)

/-- The actual extended squared-norm tail is bounded by actual modular gradient energy. -/
theorem cuspHorizontal_tail_lintegral_le (F : ModularGradient.smoothCore)
    {H : ℝ} (hH : 1 ≤ H) :
    (∫⁻ τ : UpperHalfPlane in {τ | H < τ.im},
      ENNReal.ofReal (‖cuspHorizontalResidual F.val τ‖ ^ 2) ∂modularMeasure) ≤
      ENNReal.ofReal (1 / H ^ 2) *
        ∫⁻ τ : UpperHalfPlane, ENNReal.ofReal (cuspHorizontalEnergy F.val τ) ∂modularMeasure := by
  have hR := lintegral_modular_highCusp
    (fun z => ‖cuspHorizontalResidual F.val z‖ ^ 2)
    ((continuousOn_cuspHorizontalResidual F.property.1.continuousOn).norm.pow 2) hH
  have hE := lintegral_modular_highCusp (cuspHorizontalEnergy F.val)
    (continuousOn_cuspHorizontalEnergy F.property.1) hH
  rw [hR]
  calc
    _ ≤ ∫⁻ y : ℝ in Ioi H, ENNReal.ofReal (1 / H ^ 2) *
        ∫⁻ x : ℝ in Ioo (-1/2) (1/2),
          ENNReal.ofReal ((1 / y ^ 2) * cuspHorizontalEnergy F.val (Complex.mk x y)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      exact cuspHorizontal_row_bound F hH hy
    _ = ENNReal.ofReal (1 / H ^ 2) *
        ∫⁻ τ : UpperHalfPlane in {τ | H < τ.im},
          ENNReal.ofReal (cuspHorizontalEnergy F.val τ) ∂modularMeasure := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← hE]
    _ ≤ _ := mul_le_mul' le_rfl
      (lintegral_mono' Measure.restrict_le_self (fun _ => le_rfl))

/-- The ordinary squared-norm tail genuinely converges and obeys the explicit cusp estimate. -/
theorem cuspHorizontal_tail_estimate (F : ModularGradient.smoothCore)
    {H : ℝ} (hH : 1 ≤ H) :
    IntegrableOn (fun τ : UpperHalfPlane => ‖cuspHorizontalResidual F.val τ‖ ^ 2)
        {τ | H < τ.im} modularMeasure ∧
      (∫ τ : UpperHalfPlane in {τ | H < τ.im},
        ‖cuspHorizontalResidual F.val τ‖ ^ 2 ∂modularMeasure) ≤
        (1 / H ^ 2) * ∫ τ : UpperHalfPlane,
          ‖ModularGradient.directional F.val 1 τ‖ ^ 2 ∂modularMeasure := by
  have henergy : Integrable (fun τ : UpperHalfPlane => cuspHorizontalEnergy F.val τ)
      modularMeasure := by
    exact (memLp_two_iff_integrable_sq_norm F.property.2.2.2.1.aestronglyMeasurable).mp
      F.property.2.2.2.1
  have hen := cuspHorizontal_tail_lintegral_le F hH
  rw [← ofReal_integral_eq_lintegral_ofReal henergy
    (Filter.Eventually.of_forall (fun τ => sq_nonneg _)),
    ← ENNReal.ofReal_mul (by positivity)] at hen
  have hcont : Continuous (fun τ : UpperHalfPlane => ‖cuspHorizontalResidual F.val τ‖ ^ 2) :=
    ((continuousOn_cuspHorizontalResidual F.property.1.continuousOn).comp_continuous
      UpperHalfPlane.continuous_coe (fun τ => τ.im_pos)).norm.pow 2
  have hint : IntegrableOn (fun τ : UpperHalfPlane => ‖cuspHorizontalResidual F.val τ‖ ^ 2)
      {τ | H < τ.im} modularMeasure := by
    refine ⟨hcont.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have hfinite := hen.trans_lt ENNReal.ofReal_lt_top
    simpa only [Real.enorm_eq_ofReal_abs, abs_pow, abs_norm] using hfinite
  refine ⟨hint, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall (fun τ => sq_nonneg _))] at hen
  have hb : 0 ≤ (1 / H ^ 2) * ∫ τ : UpperHalfPlane,
      cuspHorizontalEnergy F.val τ ∂modularMeasure :=
    mul_nonneg (by positivity) (integral_nonneg (fun τ => sq_nonneg _))
  exact (ENNReal.ofReal_le_ofReal_iff hb).mp hen

theorem cuspHorizontalResidual_memLp_tail (F : ModularGradient.smoothCore)
    {H : ℝ} (hH : 1 ≤ H) :
    MemLp (fun τ : UpperHalfPlane => cuspHorizontalResidual F.val τ) 2
      (modularMeasure.restrict {τ | H < τ.im}) := by
  have hc : Continuous (fun τ : UpperHalfPlane => cuspHorizontalResidual F.val τ) :=
    (continuousOn_cuspHorizontalResidual F.property.1.continuousOn).comp_continuous
      UpperHalfPlane.continuous_coe (fun τ => τ.im_pos)
  exact (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
    (cuspHorizontal_tail_estimate F hH).1

/-- The ordinary horizontal energy is exactly the actual component's squared Hilbert norm. -/
theorem integral_horizontalEnergy_eq_norm_sq (F : ModularGradient.smoothCore) :
    (∫ τ : UpperHalfPlane, ‖ModularGradient.directional F.val 1 τ‖ ^ 2 ∂modularMeasure) =
      ‖ModularGradient.xComponent F‖ ^ 2 := by
  have hrep : ModularGradient.xComponent F =ᵐ[modularMeasure]
      ModularGradient.directional F.val 1 :=
    ModularGradient.component_ae 1 (fun G => G.property.2.2.2.1) F
  calc
    _ = ∫ τ : UpperHalfPlane,
        (inner ℂ (ModularGradient.xComponent F τ) (ModularGradient.xComponent F τ)).re
        ∂modularMeasure := by
      apply integral_congr_ae
      filter_upwards [hrep] with τ hτ
      rw [hτ]
      exact norm_sq_eq_re_inner (𝕜 := ℂ) _
    _ = (∫ τ : UpperHalfPlane,
        inner ℂ (ModularGradient.xComponent F τ) (ModularGradient.xComponent F τ)
        ∂modularMeasure).re :=
      Complex.reCLM.integral_comp_comm (L2.integrable_inner (𝕜 := ℂ)
        (ModularGradient.xComponent F) (ModularGradient.xComponent F))
    _ = _ := by
      rw [← L2.inner_def]
      exact (norm_sq_eq_re_inner (𝕜 := ℂ) (ModularGradient.xComponent F)).symm

/-- Squared high-cusp nonzero-mode norm is at most H⁻² times the actual full gradient energy. -/
theorem cuspHorizontal_tail_norm_bound (F : ModularGradient.smoothCore)
    {H : ℝ} (hH : 1 ≤ H) :
    (∫ τ : UpperHalfPlane in {τ | H < τ.im},
      ‖cuspHorizontalResidual F.val τ‖ ^ 2 ∂modularMeasure) ≤
      (1 / H ^ 2) * ‖ModularGradient.coreGradient F‖ ^ 2 := by
  have h := (cuspHorizontal_tail_estimate F hH).2
  rw [integral_horizontalEnergy_eq_norm_sq] at h
  have hn : ‖ModularGradient.coreGradient F‖ ^ 2 =
      ‖ModularGradient.xComponent F‖ ^ 2 + ‖ModularGradient.yComponent F‖ ^ 2 := by
    have he := WithLp.prod_norm_sq_eq_of_L2 (ModularGradient.coreGradient F)
    change ‖ModularGradient.coreGradient F‖ ^ 2 =
      ‖(WithLp.ofLp (ModularGradient.coreGradient F)).1‖ ^ 2 +
        ‖(WithLp.ofLp (ModularGradient.coreGradient F)).2‖ ^ 2 at he
    simpa only [ModularGradient.coreGradient_fst, ModularGradient.coreGradient_snd] using he
  apply h.trans
  exact mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg ‖ModularGradient.yComponent F‖])
    (by positivity)

end GapFamily.Analytic
