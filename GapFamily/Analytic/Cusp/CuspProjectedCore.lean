import GapFamily.Analytic.Cusp.CuspFormDecomposition

/-!
# Actual representatives of projected constrained core vectors

The bounded constrained form projection sends genuine smooth core vectors to
actual form-domain vectors. Their modular L² value and gradient representatives
are explicit on both sides of height one. Every constrained form vector is a
form-norm limit of these projected core vectors; the projections themselves are
not assumed to be smooth across height one.
-/

noncomputable section

namespace GapFamily.Analytic

open Set Filter MeasureTheory UpperHalfPlane ModularGradient
open scoped Topology

theorem cuspHorizontalAverage_traceFreeCore (F : smoothCore) {y : ℝ} (hy : 0 < y) :
    cuspHorizontalAverage (cuspTraceFreeCore F).val y =
      cuspHorizontalAverage F.val y - cuspHorizontalAverage F.val 1 := by
  rw [cuspTraceFreeCore_apply]
  change (∫ x in (-1/2 : ℝ)..(1/2),
    F.val (Complex.mk x y) - cuspHorizontalAverage F.val 1 • (1 : ℂ)) = _
  simp only [smul_eq_mul, mul_one]
  have hi : IntervalIntegrable (fun x : ℝ => F.val (Complex.mk x y))
      volume (-1/2) (1/2) :=
    (contDiff_cuspHorizontalSlice F.property.1 hy).continuous.intervalIntegrable _ _
  rw [intervalIntegral.integral_sub hi intervalIntegrable_const]
  norm_num [intervalIntegral.integral_const, cuspHorizontalAverage, cuspHorizontalSlice]

theorem deriv_cuspHorizontalAverage_traceFreeCore (F : smoothCore) {y : ℝ} (hy : 0 < y) :
    deriv (cuspHorizontalAverage (cuspTraceFreeCore F).val) y =
      deriv (cuspHorizontalAverage F.val) y := by
  have heq : cuspHorizontalAverage (cuspTraceFreeCore F).val =ᶠ[𝓝 y]
      (fun t => cuspHorizontalAverage F.val t - cuspHorizontalAverage F.val 1) := by
    filter_upwards [Ioi_mem_nhds hy] with t ht
    exact cuspHorizontalAverage_traceFreeCore F ht
  rw [heq.deriv_eq, deriv_sub_const]

end GapFamily.Analytic


namespace GapFamily.Analytic
open Set Filter MeasureTheory UpperHalfPlane ModularGradient
open scoped Topology ContDiff

/-- The completed scalar core lift has no horizontal gradient component. -/
theorem cuspScalarFormLiftCore_gradient_fst_zero (F : smoothCore) :
    (formGradient (cuspScalarFormLiftCore F)).ofLp.1 = 0 :=
  cuspProfileForm_gradient_fst_eq_zero (cuspHorizontalAverage (cuspTraceFreeCore F).val)
    (contDiffOn_cuspHorizontalAverage (cuspTraceFreeCore F))
    (cuspTraceFreeCore_trace F)
    (cuspHorizontalAverage_scalar_mass_le (cuspTraceFreeCore F)).1
    (cuspHorizontalAverage_deriv_integrable_and_le (cuspTraceFreeCore F)).1

/-- The vertical component of the completed scalar core lift is the literal
height derivative of the ordinary trace-free average. -/
theorem cuspScalarFormLiftCore_gradient_snd_ae (F : smoothCore) :
    (formGradient (cuspScalarFormLiftCore F)).ofLp.2 =ᵐ[modularMeasure]
      (fun τ : UpperHalfPlane => if 1 < τ.im then
        (τ.im : ℂ) * deriv (cuspHorizontalAverage (cuspTraceFreeCore F).val) τ.im else 0) :=
  cuspProfileForm_gradient_snd_ae (cuspHorizontalAverage (cuspTraceFreeCore F).val)
    (contDiffOn_cuspHorizontalAverage (cuspTraceFreeCore F))
    (cuspTraceFreeCore_trace F)
    (cuspHorizontalAverage_scalar_mass_le (cuspTraceFreeCore F)).1
    (cuspHorizontalAverage_deriv_integrable_and_le (cuspTraceFreeCore F)).1

/-- The actual projected core has the literal residual value above one and
subtracts the height-one average below one. -/
theorem cuspMeanZeroFormPart_core_value_ae (F : smoothCore) :
    meanZeroCuspEmbedding (cuspMeanZeroFormPart (coreForm F)) =ᵐ[modularMeasure]
      (fun τ : UpperHalfPlane => if 1 < τ.im then
        F.val τ - cuspHorizontalAverage F.val τ.im else
        F.val τ - cuspHorizontalAverage F.val 1) := by
  rw [meanZeroCuspEmbedding_apply, cuspMeanZeroFormPart_coe, map_sub,
    cuspTraceFree_coreForm, formEmbedding_coreForm, cuspScalarFormLift_coreForm]
  have hscalar : formEmbedding (cuspScalarFormLiftCore F) =ᵐ[modularMeasure]
      (fun τ : UpperHalfPlane => if 1 < τ.im then
        cuspHorizontalAverage (cuspTraceFreeCore F).val τ.im else 0) :=
    cuspProfileForm_embedding_ae (cuspHorizontalAverage (cuspTraceFreeCore F).val)
    (contDiffOn_cuspHorizontalAverage (cuspTraceFreeCore F))
    (cuspTraceFreeCore_trace F)
    (cuspHorizontalAverage_scalar_mass_le (cuspTraceFreeCore F)).1
    (cuspHorizontalAverage_deriv_integrable_and_le (cuspTraceFreeCore F)).1
  filter_upwards [Lp.coeFn_sub (value (cuspTraceFreeCore F))
    (formEmbedding (cuspScalarFormLiftCore F)), value_ae (cuspTraceFreeCore F), hscalar]
    with τ hsub hval hscalar
  rw [hsub]
  simp only [Pi.sub_apply, hval, hscalar]
  have hpoint : (cuspTraceFreeCore F).val τ = F.val τ - cuspHorizontalAverage F.val 1 := by
    simp [cuspTraceFreeCore_apply, constantCore]
  rw [hpoint, cuspHorizontalAverage_traceFreeCore F τ.im_pos]
  by_cases hy : 1 < τ.im <;> simp only [hy, ite_true, ite_false] <;> ring

/-- The actual horizontal L² component is unchanged by either subtraction. -/
theorem cuspMeanZeroFormPart_core_gradient_fst (F : smoothCore) :
    (formGradient (cuspMeanZeroFormPart (coreForm F) : FormDomain)).ofLp.1 = xComponent F := by
  rw [cuspMeanZeroFormPart_coe, map_sub, formGradient_cuspTraceFree,
    formGradient_coreForm, cuspScalarFormLift_coreForm]
  change xComponent F - (formGradient (cuspScalarFormLiftCore F)).ofLp.1 = xComponent F
  rw [cuspScalarFormLiftCore_gradient_fst_zero, sub_zero]

theorem cuspMeanZeroFormPart_core_gradient_fst_ae (F : smoothCore) :
    (formGradient (cuspMeanZeroFormPart (coreForm F) : FormDomain)).ofLp.1 =ᵐ[modularMeasure]
      (fun τ : UpperHalfPlane => (τ.im : ℂ) * fderiv ℝ F.val τ 1) := by
  rw [cuspMeanZeroFormPart_core_gradient_fst]
  exact component_ae 1 _ F

/-- The actual vertical component equals the smooth upper residual derivative
above one and the original derivative below one, including the height-one
representative convention. -/
theorem cuspMeanZeroFormPart_core_gradient_snd_ae (F : smoothCore) :
    (formGradient (cuspMeanZeroFormPart (coreForm F) : FormDomain)).ofLp.2 =ᵐ[modularMeasure]
      (fun τ : UpperHalfPlane => (τ.im : ℂ) *
        (fderiv ℝ F.val τ Complex.I -
          if 1 < τ.im then deriv (cuspHorizontalAverage F.val) τ.im else 0)) := by
  rw [cuspMeanZeroFormPart_coe, map_sub, formGradient_cuspTraceFree,
    formGradient_coreForm, cuspScalarFormLift_coreForm]
  change yComponent F - (formGradient (cuspScalarFormLiftCore F)).ofLp.2 =ᵐ[modularMeasure] _
  filter_upwards [Lp.coeFn_sub (yComponent F) (formGradient (cuspScalarFormLiftCore F)).ofLp.2,
    component_ae Complex.I (fun G => G.property.2.2.2.2) F,
    cuspScalarFormLiftCore_gradient_snd_ae F] with τ hsub hval hscalar
  rw [hsub]
  change (yComponent F) τ - ((formGradient (cuspScalarFormLiftCore F)).ofLp.2) τ = _
  change (yComponent F) τ = directional F.val Complex.I τ at hval
  rw [hval, hscalar, deriv_cuspHorizontalAverage_traceFreeCore F τ.im_pos]
  dsimp only [directional]
  by_cases hy : 1 < τ.im <;> simp only [hy, ite_true, ite_false] <;> ring

/-- Every actual constrained form is a graph-norm limit of these projected
core vectors; smoothness of the completed vector is not assumed. -/
theorem exists_cuspMeanZeroFormPart_core_tendsto (v : cuspMeanZeroForm) :
    ∃ F : ℕ → smoothCore,
      Tendsto (fun n => cuspMeanZeroFormPart (coreForm (F n))) atTop (𝓝 v) := by
  obtain ⟨F, hF⟩ := exists_coreForm_tendsto (v : FormDomain)
  refine ⟨F, ?_⟩
  simpa only [Function.comp_def, cuspMeanZeroFormPart_meanZero] using
    cuspMeanZeroFormPart.continuous.continuousAt.tendsto.comp hF

end GapFamily.Analytic
