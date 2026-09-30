import Homogenization.Sobolev.W1p.ConvexApproxSmoothing.Continuity
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# One common smooth approximation for a weak Hessian

The concrete normalized convex smoothing is evaluated at a shifted scale, so
every term has scale strictly between zero and one. Its first and second
classical derivatives agree on the original open domain with the same smoothing
of the actual weak derivatives, with the affine scaling factors included.
-/

noncomputable section

namespace GapFamily.Analytic.LocalWeakHessian

open Set MeasureTheory Homogenization Filter
open scoped ContDiff Topology

/-- Shift the concrete scale once to obtain a strict interior contraction at every index. -/
def smoothApproxScale (n : ℕ) : ℝ := unitConvexApproxScale (n + 1)

theorem smoothApproxScale_pos (n : ℕ) : 0 < smoothApproxScale n := by
  simp only [smoothApproxScale, unitConvexApproxScale]
  positivity

theorem smoothApproxScale_lt_one (n : ℕ) : smoothApproxScale n < 1 := by
  simp only [smoothApproxScale, unitConvexApproxScale, Nat.cast_add, Nat.cast_one]
  apply (div_lt_one (by positivity : (0 : ℝ) < (n : ℝ) + 1 + 1)).mpr
  have hn : (0 : ℝ) ≤ n := by positivity
  linarith

theorem smoothApproxScale_tendsto : Tendsto smoothApproxScale atTop (𝓝 0) := by
  exact (tendsto_add_atTop_iff_nat 1).2 tendsto_unitConvexApproxScale_zero

/-- The actual globally smooth representative of the common convex smoothing sequence. -/
def smoothApprox {d : ℕ} (U : Set (Vec d)) (f : Vec d → ℝ)
    (x0 : Vec d) (r : ℝ) (n : ℕ) : Vec d → ℝ :=
  convexApproxSmoothRepresentative U unitConvexApproxKernel f x0 r (smoothApproxScale n)

theorem smoothApprox_contDiff {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) {f : Vec d → ℝ}
    (hf : MemLpOn U 2 f) {x0 : Vec d} {r : ℝ} (hr : 0 < r) (n : ℕ) :
    ContDiff ℝ ∞ (smoothApprox U f x0 r n) :=
  contDiff_convexApproxSmoothRepresentative hU.1.measurableSet
    isConvexApproxKernel_unitConvexApproxKernel (by norm_num) hf hr (smoothApproxScale_pos n)

/-- On the original domain this representative is the existing concrete approximation sequence. -/
theorem smoothApprox_eq_unitConvexApproxSequence {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (f : Vec d → ℝ)
    {x0 : Vec d} {r : ℝ} (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 < r)
    (n : ℕ) {x : Vec d} (hx : x ∈ U) :
    smoothApprox U f x0 r n x = unitConvexApproxSequence f x0 r (n + 1) x :=
  convexApproxSmoothRepresentative_eq_convexApproxSmoothing_of_mem hU
    isConvexApproxKernel_unitConvexApproxKernel hx hball hr
    (smoothApproxScale_pos n) (smoothApproxScale_lt_one n)

/-- The classical first derivative is the smoothing of the actual weak derivative. -/
theorem smoothApprox_fderiv_basis {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) {f gi : Vec d → ℝ} {i : Fin d}
    (hf : MemLpOn U 2 f) (hgi : MemLpOn U 2 gi)
    (hweak : HasWeakPartialDerivOn U i f gi)
    {x0 : Vec d} {r : ℝ} (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 < r)
    (n : ℕ) {x : Vec d} (hx : x ∈ U) :
    fderiv ℝ (smoothApprox U f x0 r n) x (basisVec i) =
      (1 - smoothApproxScale n) * smoothApprox U gi x0 r n x := by
  have heq := ae_eq_fderiv_convexApproxSmoothRepresentative_apply_basisVec hU
    isConvexApproxKernel_unitConvexApproxKernel (by norm_num : (1 : ENNReal) ≤ 2)
    hf hgi hweak hball hr (smoothApproxScale_pos n) (smoothApproxScale_lt_one n)
  exact Measure.eqOn_open_of_ae_eq heq hU.1
    (((smoothApprox_contDiff hU hf hr n).continuous_fderiv (by simp)).clm_apply
      continuous_const).continuousOn
    (continuous_const.mul (smoothApprox_contDiff hU hgi hr n).continuous).continuousOn hx

/-- Iterating the actual weak derivative identity gives the classical second derivative,
with no weak derivative of the Hessian required. -/
theorem smoothApprox_second_fderiv_basis {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) {f gi hij : Vec d → ℝ} {i j : Fin d}
    (hf : MemLpOn U 2 f) (hgi : MemLpOn U 2 gi) (hhij : MemLpOn U 2 hij)
    (hfirst : HasWeakPartialDerivOn U i f gi)
    (hsecond : HasWeakPartialDerivOn U j gi hij)
    {x0 : Vec d} {r : ℝ} (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 < r)
    (n : ℕ) {x : Vec d} (hx : x ∈ U) :
    fderiv ℝ (fun y => fderiv ℝ (smoothApprox U f x0 r n) y (basisVec i))
        x (basisVec j) =
      (1 - smoothApproxScale n) ^ 2 * smoothApprox U hij x0 r n x := by
  have heq : (fun y => fderiv ℝ (smoothApprox U f x0 r n) y (basisVec i)) =ᶠ[𝓝 x]
      (fun y => (1 - smoothApproxScale n) * smoothApprox U gi x0 r n y) := by
    filter_upwards [hU.1.mem_nhds hx] with y hy
    exact smoothApprox_fderiv_basis hU hf hgi hfirst hball hr n hy
  rw [heq.fderiv_eq,
    fderiv_const_mul ((smoothApprox_contDiff hU hgi hr n).differentiable (by simp) x)]
  simp only [smul_apply, smul_eq_mul,
    smoothApprox_fderiv_basis hU hgi hhij hsecond hball hr n hx]
  ring

end GapFamily.Analytic.LocalWeakHessian
