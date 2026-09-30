import GapFamily.Analytic.Kernel.SchurIntegralSelfAdjoint
import GapFamily.Analytic.Spatial.SpatialOrbitContinuity
import GapFamily.Analytic.Spatial.SpatialOrbitReal

/-! The literal spatial orbit kernel defines an actual bounded selfadjoint L² operator.
The proof uses its true row/column mass, not any spectral, positivity or PDE premise. -/
noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open MeasureTheory UpperHalfPlane
open SchurIntegralOperator

/-- Every Schur input is proved for the literal normalized orbit sum. -/
theorem spatialOrbitKernelData (s : ℝ) (hs : 1 < s) :
    KernelData modularMeasure (fun p : UpperHalfPlane × UpperHalfPlane =>
      spatialOrbitKernel (s : ℂ) p.1 p.2) (Real.pi / (s - 1)) where
  nonneg := (div_pos Real.pi_pos (sub_pos.mpr hs)).le
  measurable := aestronglyMeasurable_spatialOrbitKernel (s : ℂ) (by simpa using hs) _
  row_integrable := Filter.Eventually.of_forall (integrable_norm_spatialOrbitKernel_column s hs)
  row_bound := Filter.Eventually.of_forall (fun z => (integral_norm_spatialOrbitKernel_column s hs z).le)
  column_integrable := Filter.Eventually.of_forall (integrable_norm_spatialOrbitKernel s hs)
  column_bound := Filter.Eventually.of_forall (fun w => (integral_norm_spatialOrbitKernel s hs w).le)

/-- The operator is the actual L² class of the ordinary spatial-kernel integral. -/
def spatialOrbitIntegralOperator (s : ℝ) (hs : 1 < s) :
    ModularHilbert →L[ℂ] ModularHilbert := integralOperator (spatialOrbitKernelData s hs)

/-- For every actual L² vector its literal kernel product is ordinarily integrable in almost every row. -/
theorem spatialOrbitIntegralOperator_integrable_ae (s : ℝ) (hs : 1 < s) (f : ModularHilbert) :
    ∀ᵐ z : UpperHalfPlane ∂modularMeasure,
      Integrable (fun w : UpperHalfPlane => spatialOrbitKernel (s : ℂ) z w * f w) modularMeasure :=
  kernelIntegral_integrable_ae (spatialOrbitKernelData s hs) f

/-- The completed operator has the stated literal ordinary integral representative. -/
theorem spatialOrbitIntegralOperator_ae (s : ℝ) (hs : 1 < s) (f : ModularHilbert) :
    spatialOrbitIntegralOperator s hs f =ᵐ[modularMeasure]
      (fun z : UpperHalfPlane => ∫ w : UpperHalfPlane,
        spatialOrbitKernel (s : ℂ) z w * f w ∂modularMeasure) :=
  integralOperator_ae (spatialOrbitKernelData s hs) f

/-- The norm keeps exactly the original mass constant, with no extra group or measure factor. -/
theorem norm_spatialOrbitIntegralOperator_le (s : ℝ) (hs : 1 < s) :
    ‖spatialOrbitIntegralOperator s hs‖ ≤ Real.pi / (s - 1) :=
  norm_integralOperator_le (spatialOrbitKernelData s hs)

/-- Real symmetry gives selfadjointness of the actual integral operator.
Pointwise nonnegativity is not used to infer positivity of the operator. -/
theorem isSelfAdjoint_spatialOrbitIntegralOperator (s : ℝ) (hs : 1 < s) :
    IsSelfAdjoint (spatialOrbitIntegralOperator s hs) := by
  apply isSelfAdjoint_integralOperator (spatialOrbitKernelData s hs)
  apply Filter.Eventually.of_forall
  intro p
  have hreal : star (spatialOrbitKernel (s : ℂ) p.2 p.1) = spatialOrbitKernel (s : ℂ) p.2 p.1 := by
    apply Complex.ext <;> simp [spatialOrbitKernel_im_eq_zero s hs]
  simpa only [Prod.fst_swap, Prod.snd_swap] using
    (spatialOrbitKernel_symm (s : ℂ) p.1 p.2).trans hreal.symm

end GapFamily.Analytic.SpatialPoint
