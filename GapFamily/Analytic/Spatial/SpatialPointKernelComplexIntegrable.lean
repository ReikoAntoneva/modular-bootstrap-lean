import GapFamily.Analytic.Spatial.SpatialPointKernelMassAll

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open MeasureTheory UpperHalfPlane

theorem continuous_pointKernel_left (s : ℂ) (w : UpperHalfPlane) :
    Continuous (fun z : UpperHalfPlane => pointKernel s z w) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  exact (pointKernel_contDiffAt_left s z.im_pos w.im_pos).continuousAt.comp
    UpperHalfPlane.continuous_coe.continuousAt

/-- Positive spatial bases make the norm depend only on the exponent's real part. -/
theorem norm_pointKernel_eq_realPart (s : ℂ) (z w : UpperHalfPlane) :
    ‖pointKernel s z w‖ = ‖pointKernel (s.re : ℂ) z w‖ := by
  simp only [pointKernel, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (pointParameter_pos z.im_pos w.im_pos),
    Complex.neg_re, Complex.ofReal_re]

/-- The complex convergence half-plane has genuine whole-H integrability. -/
theorem integrable_pointKernel_complex (s : ℂ) (hs : 1 < s.re) (w : UpperHalfPlane) :
    Integrable (fun z : UpperHalfPlane => pointKernel s z w) volume := by
  apply (integrable_pointKernel s.re hs w).congr'
    (continuous_pointKernel_left s w).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun z => (norm_pointKernel_eq_realPart s z w).symm)

end GapFamily.Analytic.SpatialPoint
