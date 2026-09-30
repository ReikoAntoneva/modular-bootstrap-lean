import GapFamily.Analytic.Spatial.SpatialPointKernelMassAll
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-! Actual bounded-test averages for the integrable hyperbolic point kernel. -/
noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open Set Filter MeasureTheory UpperHalfPlane
open scoped Topology BoundedContinuousFunction

/-- At real exponent the literal kernel is the cast of its positive real power. -/
theorem pointKernel_real_eq (s : ℝ) (z w : UpperHalfPlane) :
    pointKernel (s : ℂ) z w =
      ((1 / 4 * pointParameter z w ^ (-s) : ℝ) : ℂ) := by
  rw [pointKernel, Complex.ofReal_mul,
    Complex.ofReal_cpow (pointParameter_pos z.im_pos w.im_pos).le]
  simp

/-- The real kernel is strictly positive for every pair of upper-half-plane points. -/
theorem pointKernel_real_re_pos (s : ℝ) (z w : UpperHalfPlane) :
    0 < (pointKernel (s : ℂ) z w).re := by
  rw [pointKernel_real_eq, Complex.ofReal_re]
  exact mul_pos (by norm_num)
    (Real.rpow_pos_of_pos (pointParameter_pos z.im_pos w.im_pos) _)

/-- Its complex norm has the exact real positive-kernel value. -/
theorem norm_pointKernel_real (s : ℝ) (z w : UpperHalfPlane) :
    ‖pointKernel (s : ℂ) z w‖ = 1 / 4 * pointParameter z w ^ (-s) := by
  rw [pointKernel_real_eq]
  exact Complex.norm_of_nonneg (mul_nonneg (by norm_num)
    (Real.rpow_nonneg (pointParameter_pos z.im_pos w.im_pos).le _))

/-- Symmetry gives genuine hyperbolic integrability in the averaging variable. -/
theorem integrable_pointKernel_right (s : ℝ) (hs : 1 < s) (z : UpperHalfPlane) :
    Integrable (fun w : UpperHalfPlane => pointKernel (s : ℂ) z w) volume := by
  exact (integrable_pointKernel s hs z).congr
    (Eventually.of_forall fun w => pointKernel_symm (s : ℂ) w z)

/-- The averaging variable has the same exact whole-half-plane mass. -/
theorem integral_pointKernel_right (s : ℝ) (hs : 1 < s) (z : UpperHalfPlane) :
    (∫ w : UpperHalfPlane, pointKernel (s : ℂ) z w ∂volume) =
      (Real.pi / (s - 1) : ℝ) := by
  calc
    _ = ∫ w : UpperHalfPlane, pointKernel (s : ℂ) w z ∂volume :=
      integral_congr_ae (Eventually.of_forall fun w => pointKernel_symm (s : ℂ) z w)
    _ = _ := integral_pointKernel s hs z

/-- The ordinary integral of the kernel norm is its exact positive mass. -/
theorem integral_norm_pointKernel (s : ℝ) (hs : 1 < s) (z : UpperHalfPlane) :
    (∫ w : UpperHalfPlane, ‖pointKernel (s : ℂ) z w‖ ∂volume) =
      Real.pi / (s - 1) := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  calc
    _ = ∫ w : UpperHalfPlane, pointKernel (s : ℂ) z w ∂volume := by
      apply integral_congr_ae
      exact Eventually.of_forall fun w => by
        change (‖pointKernel (s : ℂ) z w‖ : ℂ) = pointKernel (s : ℂ) z w
        rw [norm_pointKernel_real, pointKernel_real_eq]
    _ = _ := integral_pointKernel_right s hs z

/-- Bounded continuous tests give genuinely integrable kernel products. -/
theorem integrable_pointKernel_mul_bounded (s : ℝ) (hs : 1 < s)
    (z : UpperHalfPlane) (f : UpperHalfPlane →ᵇ ℂ) :
    Integrable (fun w : UpperHalfPlane => pointKernel (s : ℂ) z w * f w) volume :=
  (integrable_pointKernel_right s hs z).mul_bdd f.continuous.aestronglyMeasurable
    (Eventually.of_forall f.norm_coe_le_norm)

/-- The actual centered test error also has an ordinary integrable kernel product. -/
theorem integrable_pointKernel_mul_sub_value (s : ℝ) (hs : 1 < s)
    (z : UpperHalfPlane) (f : UpperHalfPlane →ᵇ ℂ) :
    Integrable (fun w : UpperHalfPlane =>
      pointKernel (s : ℂ) z w * (f w - f z)) volume := by
  have he : (fun w : UpperHalfPlane => pointKernel (s : ℂ) z w * (f w - f z)) =
      (fun w : UpperHalfPlane => pointKernel (s : ℂ) z w * f w) -
        (fun w : UpperHalfPlane => pointKernel (s : ℂ) z w * f z) := by
    funext w
    simp only [Pi.sub_apply, mul_sub]
  rw [he]
  exact (integrable_pointKernel_mul_bounded s hs z f).sub
    ((integrable_pointKernel_right s hs z).mul_const (f z))

/-- The mass-normalized average against the literal whole hyperbolic kernel. -/
def pointAverage (s : ℝ) (z : UpperHalfPlane) (f : UpperHalfPlane →ᵇ ℂ) : ℂ :=
  (((s - 1) / Real.pi : ℝ) : ℂ) *
    ∫ w : UpperHalfPlane, pointKernel (s : ℂ) z w * f w ∂volume

/-- The genuine normalized average preserves every complex constant. -/
theorem pointAverage_const (s : ℝ) (hs : 1 < s) (z : UpperHalfPlane) (c : ℂ) :
    pointAverage s z (BoundedContinuousFunction.const UpperHalfPlane c) = c := by
  have hmass : (((s - 1) / Real.pi : ℝ) : ℂ) *
      ((Real.pi / (s - 1) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul]
    norm_cast
    field_simp [Real.pi_ne_zero, (sub_pos.mpr hs).ne']
  unfold pointAverage
  simp only [BoundedContinuousFunction.const_apply]
  rw [integral_mul_const, integral_pointKernel_right s hs z, ← mul_assoc, hmass, one_mul]

/-- The actual error is exactly the normalized integral of the centered bounded test. -/
theorem pointAverage_sub_value (s : ℝ) (hs : 1 < s)
    (z : UpperHalfPlane) (f : UpperHalfPlane →ᵇ ℂ) :
    pointAverage s z f - f z = (((s - 1) / Real.pi : ℝ) : ℂ) *
      ∫ w : UpperHalfPlane, pointKernel (s : ℂ) z w * (f w - f z) ∂volume := by
  have hconstant : (((s - 1) / Real.pi : ℝ) : ℂ) *
      (∫ w : UpperHalfPlane, pointKernel (s : ℂ) z w * f z ∂volume) = f z :=
    pointAverage_const s hs z (f z)
  have hdiff : (∫ w : UpperHalfPlane,
      pointKernel (s : ℂ) z w * (f w - f z) ∂volume) =
      (∫ w : UpperHalfPlane, pointKernel (s : ℂ) z w * f w ∂volume) -
        ∫ w : UpperHalfPlane, pointKernel (s : ℂ) z w * f z ∂volume := by
    simp only [mul_sub]
    exact integral_sub (integrable_pointKernel_mul_bounded s hs z f)
      ((integrable_pointKernel_right s hs z).mul_const (f z))
  rw [pointAverage, hdiff, mul_sub, hconstant]

end GapFamily.Analytic.SpatialPoint
