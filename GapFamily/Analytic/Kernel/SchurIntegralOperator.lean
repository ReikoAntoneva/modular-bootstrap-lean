import GapFamily.Analytic.Kernel.SchurWeightedCauchy
import GapFamily.Analytic.Kernel.SchurKernelMass
import Mathlib.MeasureTheory.Function.L2Space

noncomputable section
namespace GapFamily.Analytic.SchurIntegralOperator
open MeasureTheory Filter
open SchurWeightedCauchy SchurKernelMass

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Explicit ordinary row and column hypotheses of the Schur estimate. -/
structure KernelData (μ : Measure X) (K : X × X → ℂ) (C : ℝ) : Prop where
  nonneg : 0 ≤ C
  measurable : AEStronglyMeasurable K (μ.prod μ)
  row_integrable : ∀ᵐ x ∂μ, Integrable (fun y => ‖K (x, y)‖) μ
  row_bound : ∀ᵐ x ∂μ, (∫ y, ‖K (x, y)‖ ∂μ) ≤ C
  column_integrable : ∀ᵐ y ∂μ, Integrable (fun x => ‖K (x, y)‖) μ
  column_bound : ∀ᵐ y ∂μ, (∫ x, ‖K (x, y)‖ ∂μ) ≤ C

/-- Literal ordinary integral against the actual chosen L² representative. -/
def kernelIntegral (K : X × X → ℂ) (f : Lp ℂ 2 μ) (x : X) : ℂ :=
  ∫ y, K (x, y) * f y ∂μ

theorem l2_norm_sq (f : Lp ℂ 2 μ) : ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards with x
  exact real_inner_self_eq_norm_sq (f x)

variable [SFinite μ] {K : X × X → ℂ} {C : ℝ}

/-- The integral exists ordinarily for almost every row, for every actual L² input. -/
theorem kernelIntegral_integrable_ae (h : KernelData μ K C) (f : Lp ℂ 2 μ) :
    ∀ᵐ x ∂μ, Integrable (fun y => K (x, y) * f y) μ := by
  have hm := weighted_row_integrable_and_mass_le h.measurable h.nonneg
    h.column_integrable h.column_bound (Lp.memLp f).norm.integrable_sq
    (Eventually.of_forall fun _ => sq_nonneg _)
  filter_upwards [h.measurable.prodMk_left, h.row_integrable, hm.1] with x hx hr hs
  exact integrable_kernel_mul hx (Lp.memLp f).aestronglyMeasurable hr hs

/-- The ordinary output has genuine finite squared mass with the sharp Schur coefficient. -/
theorem kernelIntegral_sq_integrable_and_bound (h : KernelData μ K C) (f : Lp ℂ 2 μ) :
    Integrable (fun x => ‖kernelIntegral K f x‖ ^ 2) μ ∧
      (∫ x, ‖kernelIntegral K f x‖ ^ 2 ∂μ) ≤ C ^ 2 * ‖f‖ ^ 2 := by
  have hm := weighted_row_integrable_and_mass_le h.measurable h.nonneg
    h.column_integrable h.column_bound (Lp.memLp f).norm.integrable_sq
    (Eventually.of_forall fun _ => sq_nonneg _)
  have hmeas : AEStronglyMeasurable (kernelIntegral K f) μ :=
    (h.measurable.mul (Lp.memLp f).aestronglyMeasurable.comp_snd).integral_prod_right'
  have hb : ∀ᵐ x ∂μ, ‖kernelIntegral K f x‖ ^ 2 ≤
      C * ∫ y, ‖K (x, y)‖ * ‖f y‖ ^ 2 ∂μ := by
    filter_upwards [h.measurable.prodMk_left, h.row_integrable, h.row_bound, hm.1]
      with x hx hr hC hs
    exact (norm_integral_kernel_mul_sq_le hx (Lp.memLp f).aestronglyMeasurable hr hs).trans
      (mul_le_mul_of_nonneg_right hC (integral_nonneg fun y => mul_nonneg (norm_nonneg _) (sq_nonneg _)))
  have hi : Integrable (fun x => ‖kernelIntegral K f x‖ ^ 2) μ := by
    apply (hm.2.1.const_mul C).mono' (hmeas.norm.pow 2)
    filter_upwards [hb] with x hx
    simpa only [Pi.pow_apply, Real.norm_of_nonneg (sq_nonneg _)] using hx
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ x, C * ∫ y, ‖K (x, y)‖ * ‖f y‖ ^ 2 ∂μ ∂μ :=
      integral_mono_ae hi (hm.2.1.const_mul C) hb
    _ = C * ∫ x, ∫ y, ‖K (x, y)‖ * ‖f y‖ ^ 2 ∂μ ∂μ := integral_const_mul _ _
    _ ≤ C * (C * ∫ y, ‖f y‖ ^ 2 ∂μ) := mul_le_mul_of_nonneg_left hm.2.2 h.nonneg
    _ = C ^ 2 * ‖f‖ ^ 2 := by rw [← l2_norm_sq]; ring

/-- Membership is proved for the ordinary integral itself, before selecting its L² class. -/
theorem kernelIntegral_memLp (h : KernelData μ K C) (f : Lp ℂ 2 μ) :
    MemLp (kernelIntegral K f) 2 μ := by
  have hmeas : AEStronglyMeasurable (kernelIntegral K f) μ :=
    (h.measurable.mul (Lp.memLp f).aestronglyMeasurable.comp_snd).integral_prod_right'
  exact (memLp_two_iff_integrable_sq_norm hmeas).mpr (kernelIntegral_sq_integrable_and_bound h f).1

/-- The actual L² class of the proved ordinarily integrable row integral. -/
def integralValue (h : KernelData μ K C) (f : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  (kernelIntegral_memLp h f).toLp (kernelIntegral K f)

theorem integralValue_ae (h : KernelData μ K C) (f : Lp ℂ 2 μ) :
    integralValue h f =ᵐ[μ] kernelIntegral K f :=
  MemLp.coeFn_toLp _

theorem integralValue_norm_le (h : KernelData μ K C) (f : Lp ℂ 2 μ) :
    ‖integralValue h f‖ ≤ C * ‖f‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg h.nonneg (norm_nonneg _))).mp
  rw [l2_norm_sq]
  have he : (∫ x, ‖integralValue h f x‖ ^ 2 ∂μ) = ∫ x, ‖kernelIntegral K f x‖ ^ 2 ∂μ :=
    integral_congr_ae ((integralValue_ae h f).mono fun x hx => congrArg (fun z : ℂ => ‖z‖ ^ 2) hx)
  rw [he, mul_pow]
  exact (kernelIntegral_sq_integrable_and_bound h f).2

/-- Linearity is obtained from actual ordinary row integrals and L² AE equalities. -/
theorem integralValue_add (h : KernelData μ K C) (f g : Lp ℂ 2 μ) :
    integralValue h (f + g) = integralValue h f + integralValue h g := by
  apply Lp.ext
  filter_upwards [integralValue_ae h (f + g), integralValue_ae h f, integralValue_ae h g,
    Lp.coeFn_add (integralValue h f) (integralValue h g),
    kernelIntegral_integrable_ae h f, kernelIntegral_integrable_ae h g] with x hs hf hg hadd hif hig
  rw [hs, hadd, Pi.add_apply, hf, hg]
  change (∫ y, K (x, y) * (f + g) y ∂μ) = _
  calc
    _ = ∫ y, K (x, y) * f y + K (x, y) * g y ∂μ := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_add f g] with y hy
      simp only [hy, Pi.add_apply, mul_add]
    _ = _ := integral_add hif hig

theorem integralValue_smul (h : KernelData μ K C) (c : ℂ) (f : Lp ℂ 2 μ) :
    integralValue h (c • f) = c • integralValue h f := by
  apply Lp.ext
  filter_upwards [integralValue_ae h (c • f), integralValue_ae h f,
    Lp.coeFn_smul c (integralValue h f)] with x hs hf hsmul
  rw [hs, hsmul, Pi.smul_apply, hf]
  change (∫ y, K (x, y) * (c • f) y ∂μ) = c * ∫ y, K (x, y) * f y ∂μ
  calc
    _ = ∫ y, c * (K (x, y) * f y) ∂μ := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_smul c f] with y hy
      simp only [hy, Pi.smul_apply, smul_eq_mul]
      ring
    _ = _ := integral_const_mul _ _

def integralLinearMap (h : KernelData μ K C) : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ where
  toFun := integralValue h
  map_add' := integralValue_add h
  map_smul' c f := by simpa only [RingHom.id_apply] using integralValue_smul h c f

/-- The bounded operator is constructed from the literal ordinary integral itself. -/
def integralOperator (h : KernelData μ K C) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (integralLinearMap h).mkContinuous C (integralValue_norm_le h)

theorem integralOperator_ae (h : KernelData μ K C) (f : Lp ℂ 2 μ) :
    integralOperator h f =ᵐ[μ] fun x => ∫ y, K (x, y) * f y ∂μ :=
  integralValue_ae h f

/-- The operator norm has the original common row/column coefficient. -/
theorem norm_integralOperator_le (h : KernelData μ K C) : ‖integralOperator h‖ ≤ C :=
  LinearMap.mkContinuous_norm_le (integralLinearMap h) h.nonneg (integralValue_norm_le h)

end GapFamily.Analytic.SchurIntegralOperator
