import GapFamily.Analytic.Elliptic.LocalWeakHessianApproximationBase
import Homogenization.Sobolev.W1p.ConvexApproxSmoothing.Convergence

/-!
# Ordinary L² convergence of the common local smoothing sequence

The smooth representatives agree on the convex domain with the actual smoothing
operator. Its genuine L² approximation theorem therefore applies to the chosen
sequence. The first and second derivative scaling factors tend to one and preserve
the same L² limit.
-/

noncomputable section

namespace GapFamily.Analytic.LocalWeakHessian

open Set MeasureTheory Filter Homogenization
open scoped ENNReal Topology

variable {d : ℕ} {U : Set (Vec d)} {f : Vec d → ℝ} {x0 : Vec d} {r : ℝ}

private theorem smoothApprox_ae_eq_smoothing
    (hU : IsOpenBoundedConvexDomain U)
    (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 < r) (n : ℕ) :
    smoothApprox U f x0 r n =ᵐ[volume.restrict U]
      convexApproxSmoothing unitConvexApproxKernel f x0 r (smoothApproxScale n) := by
  filter_upwards [ae_restrict_mem hU.isOpen.measurableSet] with x hx
  exact convexApproxSmoothRepresentative_eq_convexApproxSmoothing_of_mem
    hU isConvexApproxKernel_unitConvexApproxKernel hx hball hr
    (smoothApproxScale_pos n) (smoothApproxScale_lt_one n)

/-- Every chosen smooth representative has finite ordinary L² norm on the domain. -/
theorem smoothApprox_memLp (hU : IsOpenBoundedConvexDomain U) (hf : MemLpOn U 2 f)
    (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 < r) (n : ℕ) :
    MemLpOn U 2 (smoothApprox U f x0 r n) :=
  (memLpOn_convexApproxSmoothing hU isConvexApproxKernel_unitConvexApproxKernel
    (by norm_num) (by norm_num) hf hball hr
    (smoothApproxScale_pos n) (smoothApproxScale_lt_one n)).ae_eq
      (smoothApprox_ae_eq_smoothing hU hball hr n).symm

theorem one_sub_mul_smoothApprox_memLp
    (hU : IsOpenBoundedConvexDomain U) (hf : MemLpOn U 2 f)
    (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 < r) (n : ℕ) :
    MemLpOn U 2 (fun x => (1 - smoothApproxScale n) * smoothApprox U f x0 r n x) :=
  (smoothApprox_memLp hU hf hball hr n).const_mul _

theorem one_sub_sq_mul_smoothApprox_memLp
    (hU : IsOpenBoundedConvexDomain U) (hf : MemLpOn U 2 f)
    (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 < r) (n : ℕ) :
    MemLpOn U 2 (fun x => (1 - smoothApproxScale n) ^ 2 * smoothApprox U f x0 r n x) :=
  (smoothApprox_memLp hU hf hball hr n).const_mul _

/-- The actual common smooth representatives converge in ordinary L². -/
theorem tendsto_eLpNorm_smoothApprox_sub
    (hU : IsOpenBoundedConvexDomain U) (hf : MemLpOn U 2 f)
    (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 < r) :
    Tendsto (fun n => eLpNorm (fun x => smoothApprox U f x0 r n x - f x)
      2 (volume.restrict U)) atTop (𝓝 0) := by
  have h := tendsto_eLpNorm_sub_zero_convexApproxSmoothing_of_memLpOn
    hU isConvexApproxKernel_unitConvexApproxKernel
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    hf hball hr smoothApproxScale_tendsto
    (Eventually.of_forall smoothApproxScale_pos) (Eventually.of_forall smoothApproxScale_lt_one)
  apply h.congr'
  filter_upwards with n
  apply eLpNorm_congr_ae
  filter_upwards [smoothApprox_ae_eq_smoothing (f := f) hU hball hr n] with x hx
  rw [hx]

/-- A scalar sequence tending to one preserves an existing L² approximation. -/
private theorem tendsto_eLpNorm_mul_sub_of_tendsto
    {F : ℕ → Vec d → ℝ} {a : ℕ → ℝ} (hf : MemLpOn U 2 f)
    (hF : Tendsto (fun n => eLpNorm (fun x => F n x - f x) 2 (volume.restrict U))
      atTop (𝓝 0)) (ha : Tendsto a atTop (𝓝 1)) :
    Tendsto (fun n => eLpNorm (fun x => a n * F n x - f x) 2 (volume.restrict U))
      atTop (𝓝 0) := by
  have ha_norm : Tendsto (fun n => ‖a n‖ₑ) atTop (𝓝 1) := by
    simpa [Real.enorm_eq_ofReal_abs] using ENNReal.tendsto_ofReal ha.abs
  have ha_sub : Tendsto (fun n => ‖a n - 1‖ₑ) atTop (𝓝 0) := by
    simpa [Real.enorm_eq_ofReal_abs] using
      ENNReal.tendsto_ofReal (ha.sub (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))).abs
  have hfirst : Tendsto
      (fun n => ‖a n‖ₑ * eLpNorm (fun x => F n x - f x) 2 (volume.restrict U))
      atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul ha_norm (Or.inl one_ne_zero) hF
      (Or.inr ENNReal.one_ne_top)
  have hsecond : Tendsto
      (fun n => ‖a n - 1‖ₑ * eLpNorm f 2 (volume.restrict U)) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const ha_sub (Or.inr hf.eLpNorm_lt_top.ne)
  have hsum := hfirst.add hsecond
  simp only [add_zero] at hsum
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le) (fun n => ?_)
  have hdecomp : (fun x => a n * F n x - f x) =
      a n • (fun x => F n x - f x) + (a n - 1) • f := by
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hdecomp]
  exact (eLpNorm_add_le (by norm_num)).trans_eq (by
    rw [eLpNorm_const_smul, eLpNorm_const_smul])

/-- The affine first-derivative factor retains the same ordinary L² limit. -/
theorem tendsto_eLpNorm_one_sub_mul_smoothApprox_sub
    (hU : IsOpenBoundedConvexDomain U) (hf : MemLpOn U 2 f)
    (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 < r) :
    Tendsto (fun n => eLpNorm
      (fun x => (1 - smoothApproxScale n) * smoothApprox U f x0 r n x - f x)
      2 (volume.restrict U)) atTop (𝓝 0) := by
  apply tendsto_eLpNorm_mul_sub_of_tendsto hf
    (tendsto_eLpNorm_smoothApprox_sub hU hf hball hr)
  simpa using tendsto_const_nhds.sub smoothApproxScale_tendsto

/-- The two affine derivative factors retain the same ordinary L² limit. -/
theorem tendsto_eLpNorm_one_sub_sq_mul_smoothApprox_sub
    (hU : IsOpenBoundedConvexDomain U) (hf : MemLpOn U 2 f)
    (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 < r) :
    Tendsto (fun n => eLpNorm
      (fun x => (1 - smoothApproxScale n) ^ 2 * smoothApprox U f x0 r n x - f x)
      2 (volume.restrict U)) atTop (𝓝 0) := by
  apply tendsto_eLpNorm_mul_sub_of_tendsto hf
    (tendsto_eLpNorm_smoothApprox_sub hU hf hball hr)
  simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub
    smoothApproxScale_tendsto).pow 2

end GapFamily.Analytic.LocalWeakHessian
