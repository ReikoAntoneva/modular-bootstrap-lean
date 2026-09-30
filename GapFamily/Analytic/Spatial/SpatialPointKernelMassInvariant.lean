import GapFamily.Analytic.Spatial.SpatialPointKernelCovariance
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.MeasureTheory.Group.Integral

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open MeasureTheory UpperHalfPlane Matrix
open scoped MatrixGroups

/-- Actual whole-upper-half-plane integrability is independent of the center. -/
theorem integrable_pointKernel_iff_I (s : ℂ) (w : UpperHalfPlane) :
    Integrable (fun z : UpperHalfPlane => pointKernel s z w) volume ↔
      Integrable (fun z : UpperHalfPlane => pointKernel s z UpperHalfPlane.I) volume := by
  let γ : GL (Fin 2) ℝ := w.toSL2R
  have heq (z : UpperHalfPlane) : pointKernel s (γ • z : UpperHalfPlane) w =
      pointKernel s z UpperHalfPlane.I := by
    change pointKernel s (w.toSL2R • z : UpperHalfPlane) w = _
    simpa only [UpperHalfPlane.toSL2R_smul_I] using
      pointKernel_smul s w.toSL2R z UpperHalfPlane.I
  have h := (measurePreserving_smul γ (volume : Measure UpperHalfPlane)).integrable_comp_emb
    (measurableEmbedding_const_smul γ)
    (g := fun z : UpperHalfPlane => pointKernel s z w)
  simpa only [Function.comp_def, heq] using h.symm

/-- The point-kernel integral is invariant under moving the center, with
respect to the literal full hyperbolic volume dx dy/y². -/
theorem integral_pointKernel_eq_I (s : ℂ) (w : UpperHalfPlane) :
    (∫ z : UpperHalfPlane, pointKernel s z w) =
      ∫ z : UpperHalfPlane, pointKernel s z UpperHalfPlane.I := by
  let γ : GL (Fin 2) ℝ := w.toSL2R
  have heq (z : UpperHalfPlane) : pointKernel s (γ • z : UpperHalfPlane) w =
      pointKernel s z UpperHalfPlane.I := by
    change pointKernel s (w.toSL2R • z : UpperHalfPlane) w = _
    simpa only [UpperHalfPlane.toSL2R_smul_I] using
      pointKernel_smul s w.toSL2R z UpperHalfPlane.I
  have h := integral_smul_eq_self (G := GL (Fin 2) ℝ) (μ := (volume : Measure UpperHalfPlane))
    (g := γ) (fun z : UpperHalfPlane => pointKernel s z w)
  simpa only [heq] using h.symm

end GapFamily.Analytic.SpatialPoint
