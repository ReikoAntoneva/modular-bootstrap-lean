import GapFamily.Analytic.Spatial.SpatialCayleyGeometry
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open Set UpperHalfPlane

/-- The actual upper-half-plane-valued Cayley map, on its positive-imaginary-part domain. -/
def cayleyUpper (ζ : ℂ) : UpperHalfPlane :=
  UpperHalfPlane.ofComplex (cayleyToUpper ζ)

/-- The inverse Cayley coordinate of an actual upper-half-plane point. -/
def cayleyFromUpper (τ : UpperHalfPlane) : ℂ :=
  ((τ : ℂ) - Complex.I) / ((τ : ℂ) + Complex.I)

theorem coe_cayleyUpper {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    (cayleyUpper ζ : ℂ) = cayleyToUpper ζ := by
  rw [cayleyUpper, UpperHalfPlane.ofComplex_apply_of_im_pos (cayleyToUpper_im_pos hζ)]

theorem cayleyFromUpper_den_ne_zero (τ : UpperHalfPlane) :
    (τ : ℂ) + Complex.I ≠ 0 := by
  intro he
  have hi := congrArg Complex.im he
  simp only [Complex.add_im, Complex.I_im, Complex.zero_im] at hi
  have ht := τ.im_pos
  change 0 < (τ : ℂ).im at ht
  linarith

theorem norm_cayleyFromUpper_lt_one (τ : UpperHalfPlane) :
    ‖cayleyFromUpper τ‖ < 1 := by
  have hs : Complex.normSq (cayleyFromUpper τ) < 1 := by
    rw [cayleyFromUpper, Complex.normSq_div]
    apply (div_lt_one (Complex.normSq_pos.mpr (cayleyFromUpper_den_ne_zero τ))).mpr
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im, sub_zero, add_zero]
    have ht := τ.im_pos
    change 0 < (τ : ℂ).im at ht
    nlinarith
  rw [Complex.normSq_eq_norm_sq] at hs
  nlinarith [norm_nonneg (cayleyFromUpper τ)]

theorem cayleyToUpper_cayleyFromUpper (τ : UpperHalfPlane) :
    cayleyToUpper (cayleyFromUpper τ) = (τ : ℂ) := by
  unfold cayleyToUpper
  apply (div_eq_iff (cayleyToUpper_den_ne_zero (norm_cayleyFromUpper_lt_one τ))).mpr
  unfold cayleyFromUpper
  field_simp [cayleyFromUpper_den_ne_zero τ]
  ring

theorem cayleyUpper_cayleyFromUpper (τ : UpperHalfPlane) :
    cayleyUpper (cayleyFromUpper τ) = τ := by
  apply UpperHalfPlane.coe_injective
  rw [coe_cayleyUpper (norm_cayleyFromUpper_lt_one τ), cayleyToUpper_cayleyFromUpper]

theorem cayleyFromUpper_cayleyUpper {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    cayleyFromUpper (cayleyUpper ζ) = ζ := by
  apply cayleyToUpper_injOn_ball
    (by simpa only [Metric.mem_ball, dist_zero_right] using
      norm_cayleyFromUpper_lt_one (cayleyUpper ζ))
    (by simpa only [Metric.mem_ball, dist_zero_right] using hζ)
  rw [cayleyToUpper_cayleyFromUpper, coe_cayleyUpper hζ]

@[simp] theorem cayleyUpper_zero : cayleyUpper 0 = UpperHalfPlane.I := by
  apply UpperHalfPlane.coe_injective
  rw [coe_cayleyUpper (by simp)]
  simp [cayleyToUpper]

theorem continuous_cayleyFromUpper : Continuous cayleyFromUpper := by
  exact (UpperHalfPlane.continuous_coe.sub continuous_const).div
    (UpperHalfPlane.continuous_coe.add continuous_const) cayleyFromUpper_den_ne_zero

theorem continuousAt_cayleyUpper {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    ContinuousAt cayleyUpper ζ := by
  have hsrc : cayleyToUpper ζ ∈ UpperHalfPlane.ofComplex.source := by
    simp only [UpperHalfPlane.ofComplex, OpenPartialHomeomorph.symm_source,
      Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target, UpperHalfPlane.range_coe]
    exact cayleyToUpper_im_pos hζ
  exact (UpperHalfPlane.ofComplex.continuousAt hsrc).comp
    (cayleyToUpper_hasDerivAt hζ).continuousAt

theorem continuousOn_cayleyUpper :
    ContinuousOn cayleyUpper (Metric.ball (0 : ℂ) 1) := by
  intro ζ hζ
  exact (continuousAt_cayleyUpper
    (by simpa only [Metric.mem_ball, dist_zero_right] using hζ)).continuousWithinAt

theorem continuousAt_cayleyUpper_zero : ContinuousAt cayleyUpper 0 :=
  continuousAt_cayleyUpper (by simp)

end GapFamily.Analytic.SpatialPoint
