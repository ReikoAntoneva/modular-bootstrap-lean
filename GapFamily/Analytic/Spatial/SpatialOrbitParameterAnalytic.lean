import GapFamily.Analytic.Spatial.SpatialOrbitNormal
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open Set Filter UpperHalfPlane
open scoped Topology MatrixGroups

/-- The literal point summand is entire in its spectral parameter. -/
theorem analyticAt_pointKernel_parameter (z w : UpperHalfPlane) (s : ℂ) :
    AnalyticAt ℂ (fun t : ℂ => pointKernel t z w) s := by
  have hq : (pointParameter z w : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (pointParameter_pos z.im_pos w.im_pos).ne'
  exact ((differentiable_id.neg.const_cpow (Or.inl hq)).const_mul (1 / 4 : ℂ)).analyticAt s

/-- Actual normal convergence gives pointwise parameter analyticity of the
prescribed orbit kernel on its original convergence half-plane. -/
theorem analyticAt_spatialOrbitKernel_parameter (z w : UpperHalfPlane)
    {s : ℂ} (hs : 1 < s.re) :
    AnalyticAt ℂ (fun t : ℂ => spatialOrbitKernel t z w) s := by
  obtain ⟨r, σ, hr, hσ, hsum, hbound⟩ := exists_pointKernel_orbit_joint_majorant s hs z w
  have hd : DifferentiableOn ℂ
      (fun t : ℂ => ∑' γ : SL(2, ℤ), pointKernel t z (γ • w : UpperHalfPlane))
      (Metric.ball s r) := by
    apply Complex.differentiableOn_tsum_of_summable_norm hsum
    · intro γ t _
      exact (analyticAt_pointKernel_parameter z (γ • w) t).differentiableAt.differentiableWithinAt
    · exact Metric.isOpen_ball
    · intro γ t ht
      exact hbound t z w (by simpa only [Metric.mem_ball, dist_eq_norm] using ht)
        (by simpa using half_pos z.im_pos) (by simpa using half_pos w.im_pos) γ
  have ha := (hd.const_mul (1 / 2 : ℂ)).analyticAt (Metric.ball_mem_nhds s hr)
  simpa only [spatialOrbitKernel_eq_half_tsum_right] using ha

end GapFamily.Analytic.SpatialPoint
