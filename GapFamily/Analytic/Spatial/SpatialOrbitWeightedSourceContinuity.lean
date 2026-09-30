import GapFamily.Analytic.Foundation.L2DominatedContinuity
import GapFamily.Analytic.Spatial.SpatialOrbitWeightedSource

/-! Continuity in the location of an actual weighted spatial point source. -/

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open Set Filter MeasureTheory UpperHalfPlane
open scoped Topology

/-- The actual weighted point source varies continuously in the source location,
in the norm of modular L², throughout the original convergence half-plane. -/
theorem continuousAt_spatialOrbitWeightedSource_source (α : ℝ) (hα : 0 ≤ α)
    (hhalf : α < 1 / 2) (s : ℂ) (hs : 1 < s.re) (w : UpperHalfPlane) :
    ContinuousAt (spatialOrbitWeightedSource α hα hhalf s) w := by
  obtain ⟨C, _, hb⟩ := exists_spatialOrbitKernel_locally_uniform_bound s.re hs w
  let S : Set UpperHalfPlane := {w' | ‖(w' : ℂ) - (w : ℂ)‖ < w.im / 2}
  have hS : S ∈ 𝓝 w := by
    apply (isOpen_lt
      (UpperHalfPlane.continuous_coe.sub continuous_const).norm continuous_const).mem_nhds
    change ‖(w : ℂ) - (w : ℂ)‖ < w.im / 2
    simpa only [sub_self, norm_zero] using half_pos w.im_pos
  let B : UpperHalfPlane → ℝ := fun z => C * ‖((z.im ^ α : ℝ) : ℂ)‖
  have hB : MemLp B 2 modularMeasure :=
    (memLp_modularHeightPower α hα hhalf).norm.const_mul C
  apply DominatedL2.continuousAt_L2_of_dominated
    (spatialOrbitWeightedSource α hα hhalf s)
    (fun w' z => ((z.im ^ α : ℝ) : ℂ) * spatialOrbitKernel s z w') w S B hS
  · intro w' _
    exact spatialOrbitWeightedSource_ae α hα hhalf s hs w'
  · apply Eventually.of_forall
    intro z
    exact (continuous_const.mul ((continuous_spatialOrbitKernel s hs).comp
      (continuous_const.prodMk continuous_id))).continuousAt
  · apply Eventually.of_forall
    intro z w' hw'
    dsimp only [B]
    rw [norm_mul, mul_comm C]
    exact mul_le_mul_of_nonneg_left (hb s w' z le_rfl hw'.le) (norm_nonneg _)
  · exact hB

/-- Source-location continuity of the genuine weighted L² kernel family. -/
theorem continuous_spatialOrbitWeightedSource_source (α : ℝ) (hα : 0 ≤ α)
    (hhalf : α < 1 / 2) (s : ℂ) (hs : 1 < s.re) :
    Continuous (spatialOrbitWeightedSource α hα hhalf s) :=
  continuous_iff_continuousAt.mpr
    (continuousAt_spatialOrbitWeightedSource_source α hα hhalf s hs)

end GapFamily.Analytic.SpatialPoint
