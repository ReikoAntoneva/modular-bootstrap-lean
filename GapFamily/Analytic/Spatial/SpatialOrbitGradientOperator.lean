import GapFamily.Analytic.Spatial.SpatialOrbitFrameMeasurable
import GapFamily.Analytic.Spatial.SpatialOrbitFirstBound
import GapFamily.Analytic.Spatial.SpatialOrbitOperator
import GapFamily.Analytic.Modular.ModularGradientCore

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open MeasureTheory UpperHalfPlane ModularGradient SchurIntegralOperator
open scoped ContDiff

/-- Each literal frame component is bounded by the same positive real orbit kernel. -/
theorem norm_spatialOrbitFrameKernel_le (s : ℝ) (hs : 1 < s) (v : ℂ)
    (z w : UpperHalfPlane) :
    ‖spatialOrbitFrameKernel (s : ℂ) v (z, w)‖ ≤
      (s * ‖v‖) * ‖spatialOrbitKernel (s : ℂ) z w‖ := by
  have hd := spatialOrbitKernel_frame_fderiv_norm_le (s : ℂ) (by simpa using hs) z w
  simp only [Complex.ofReal_re, Complex.norm_real, Real.norm_of_nonneg (by linarith : 0 ≤ s)] at hd
  rw [spatialOrbitFrameKernel, norm_smul, Real.norm_of_nonneg z.im_pos.le]
  calc
    _ ≤ z.im * (‖fderiv ℝ (fun u : ℂ => spatialOrbitKernel (s : ℂ) (ofComplex u) w) (z : ℂ)‖ * ‖v‖) :=
      mul_le_mul_of_nonneg_left
        ((fderiv ℝ (fun u : ℂ => spatialOrbitKernel (s : ℂ) (ofComplex u) w) (z : ℂ)).le_opNorm v) z.im_pos.le
    _ = (z.im * ‖fderiv ℝ (fun u : ℂ => spatialOrbitKernel (s : ℂ) (ofComplex u) w) (z : ℂ)‖) * ‖v‖ := by ring
    _ ≤ (s * ‖spatialOrbitKernel (s : ℂ) z w‖) * ‖v‖ := mul_le_mul_of_nonneg_right hd (norm_nonneg _)
    _ = _ := by ring

/-- Every ordinary Schur hypothesis is discharged for the actual frame derivative. -/
theorem spatialOrbitFrameKernelData (s : ℝ) (hs : 1 < s) (v : ℂ) :
    KernelData modularMeasure (spatialOrbitFrameKernel (s : ℂ) v)
      ((s * ‖v‖) * (Real.pi / (s - 1))) where
  nonneg := by positivity
  measurable := aestronglyMeasurable_spatialOrbitFrameKernel (s : ℂ) (by simpa using hs) v _
  row_integrable := Filter.Eventually.of_forall (fun z => by
    apply ((integrable_norm_spatialOrbitKernel_column s hs z).const_mul (s * ‖v‖)).mono'
      (((continuous_spatialOrbitFrameKernel (s : ℂ) (by simpa using hs) v).comp
        (continuous_const.prodMk continuous_id)).norm.aestronglyMeasurable)
    exact Filter.Eventually.of_forall (fun w => by simpa only [norm_norm, Function.comp_def, id_eq] using norm_spatialOrbitFrameKernel_le s hs v z w))
  row_bound := Filter.Eventually.of_forall (fun z => by
    have hi := ((integrable_norm_spatialOrbitKernel_column s hs z).const_mul (s * ‖v‖)).mono'
      (((continuous_spatialOrbitFrameKernel (s : ℂ) (by simpa using hs) v).comp
        (continuous_const.prodMk continuous_id)).norm.aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun w => by simpa only [norm_norm, Function.comp_def, id_eq] using norm_spatialOrbitFrameKernel_le s hs v z w))
    calc
      _ ≤ ∫ w, (s * ‖v‖) * ‖spatialOrbitKernel (s : ℂ) z w‖ ∂modularMeasure :=
        integral_mono_ae hi ((integrable_norm_spatialOrbitKernel_column s hs z).const_mul _)
          (Filter.Eventually.of_forall (norm_spatialOrbitFrameKernel_le s hs v z))
      _ = _ := by rw [integral_const_mul, integral_norm_spatialOrbitKernel_column s hs z])
  column_integrable := Filter.Eventually.of_forall (fun w => by
    apply ((integrable_norm_spatialOrbitKernel s hs w).const_mul (s * ‖v‖)).mono'
      (((continuous_spatialOrbitFrameKernel (s : ℂ) (by simpa using hs) v).comp
        (continuous_id.prodMk continuous_const)).norm.aestronglyMeasurable)
    exact Filter.Eventually.of_forall (fun z => by simpa only [norm_norm, Function.comp_def, id_eq] using norm_spatialOrbitFrameKernel_le s hs v z w))
  column_bound := Filter.Eventually.of_forall (fun w => by
    have hi := ((integrable_norm_spatialOrbitKernel s hs w).const_mul (s * ‖v‖)).mono'
      (((continuous_spatialOrbitFrameKernel (s : ℂ) (by simpa using hs) v).comp
        (continuous_id.prodMk continuous_const)).norm.aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun z => by simpa only [norm_norm, Function.comp_def, id_eq] using norm_spatialOrbitFrameKernel_le s hs v z w))
    calc
      _ ≤ ∫ z, (s * ‖v‖) * ‖spatialOrbitKernel (s : ℂ) z w‖ ∂modularMeasure :=
        integral_mono_ae hi ((integrable_norm_spatialOrbitKernel s hs w).const_mul _)
          (Filter.Eventually.of_forall (fun z => norm_spatialOrbitFrameKernel_le s hs v z w))
      _ = _ := by rw [integral_const_mul, integral_norm_spatialOrbitKernel s hs w])

/-- The actual L² class of the ordinary frame derivative kernel integral. -/
def spatialOrbitFrameOperator (s : ℝ) (hs : 1 < s) (v : ℂ) :
    ModularHilbert →L[ℂ] ModularHilbert :=
  integralOperator (spatialOrbitFrameKernelData s hs v)

theorem spatialOrbitFrameOperator_integrable_ae (s : ℝ) (hs : 1 < s) (v : ℂ) (f : ModularHilbert) :
    ∀ᵐ z : UpperHalfPlane ∂modularMeasure,
      Integrable (fun w : UpperHalfPlane => spatialOrbitFrameKernel (s : ℂ) v (z, w) * f w) modularMeasure :=
  kernelIntegral_integrable_ae (spatialOrbitFrameKernelData s hs v) f

theorem spatialOrbitFrameOperator_ae (s : ℝ) (hs : 1 < s) (v : ℂ) (f : ModularHilbert) :
    spatialOrbitFrameOperator s hs v f =ᵐ[modularMeasure]
      fun z : UpperHalfPlane => ∫ w : UpperHalfPlane, spatialOrbitFrameKernel (s : ℂ) v (z, w) * f w ∂modularMeasure :=
  integralOperator_ae (spatialOrbitFrameKernelData s hs v) f

theorem norm_spatialOrbitFrameOperator_le (s : ℝ) (hs : 1 < s) (v : ℂ) :
    ‖spatialOrbitFrameOperator s hs v‖ ≤ (s * ‖v‖) * (Real.pi / (s - 1)) :=
  norm_integralOperator_le (spatialOrbitFrameKernelData s hs v)

/-- Both actual frame components, in the existing Hilbert gradient target. -/
def spatialOrbitGradientOperator (s : ℝ) (hs : 1 < s) :
    ModularHilbert →L[ℂ] GradientSpace :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ ModularHilbert ModularHilbert).symm.toContinuousLinearMap.comp
    ((spatialOrbitFrameOperator s hs 1).prod (spatialOrbitFrameOperator s hs Complex.I))

@[simp] theorem spatialOrbitGradientOperator_fst (s : ℝ) (hs : 1 < s) (f : ModularHilbert) :
    (WithLp.ofLp (spatialOrbitGradientOperator s hs f)).1 = spatialOrbitFrameOperator s hs 1 f := rfl

@[simp] theorem spatialOrbitGradientOperator_snd (s : ℝ) (hs : 1 < s) (f : ModularHilbert) :
    (WithLp.ofLp (spatialOrbitGradientOperator s hs f)).2 = spatialOrbitFrameOperator s hs Complex.I f := rfl

end GapFamily.Analytic.SpatialPoint
