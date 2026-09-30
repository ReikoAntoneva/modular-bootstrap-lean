import GapFamily.Analytic.Spatial.SpatialOrbitWeightedSource
import GapFamily.Analytic.Spatial.SpatialOrbitWeightedSourceContinuity
import GapFamily.Analytic.Kernel.PositiveKernelIntegral

/-! Norm bounds for actual weighted spatial sources in a closed exponent half-plane. -/

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open Set Filter MeasureTheory UpperHalfPlane

/-- The norm of the actual complex weighted source is dominated by the source at
any smaller real exponent in the convergence half-plane. -/
theorem norm_spatialOrbitWeightedSource_le_real_exponent
    (α : ℝ) (hα : 0 ≤ α) (hhalf : α < 1 / 2)
    {σ : ℝ} (hσ : 1 < σ) {t : ℂ} (hσt : σ ≤ t.re) (w : UpperHalfPlane) :
    ‖spatialOrbitWeightedSource α hα hhalf t w‖ ≤
      ‖spatialOrbitWeightedSource α hα hhalf (σ : ℂ) w‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [spatialOrbitWeightedSource_ae α hα hhalf t (hσ.trans_le hσt) w,
    spatialOrbitWeightedSource_ae α hα hhalf (σ : ℂ) (by simpa using hσ) w]
    with z hzt hzσ
  rw [hzt, hzσ, norm_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left
    (spatialOrbitKernel_norm_le_real_exponent hσ hσt z w) (norm_nonneg _)

/-- A compact set of source locations has a uniform weighted L² bound throughout
the closed exponent half-plane. -/
theorem exists_spatialOrbitWeightedSource_compact_bound
    (α : ℝ) (hα : 0 ≤ α) (hhalf : α < 1 / 2)
    (σ : ℝ) (hσ : 1 < σ) {K : Set UpperHalfPlane} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ K, ∀ t : ℂ, σ ≤ t.re →
      ‖spatialOrbitWeightedSource α hα hhalf t w‖ ≤ C := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    (continuous_spatialOrbitWeightedSource_source α hα hhalf (σ : ℂ)
      (by simpa using hσ)).continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro w hw t ht
  exact (norm_spatialOrbitWeightedSource_le_real_exponent α hα hhalf hσ ht w).trans
    ((hC w hw).trans (le_max_left _ _))

/-- A fixed Laplace height has a source norm bound uniform over the closed unit
interval and all exponents to the right of a fixed real exponent greater than one. -/
theorem exists_spatialOrbitWeightedSource_laplacePoint_bound
    (α : ℝ) (hα : 0 ≤ α) (hhalf : α < 1 / 2)
    (σ : ℝ) (hσ : 1 < σ) (l : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Icc (0 : ℝ) 1, ∀ t : ℂ, σ ≤ t.re →
      ‖spatialOrbitWeightedSource α hα hhalf t (laplacePoint l x)‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := exists_spatialOrbitWeightedSource_compact_bound α hα hhalf σ hσ
    (isCompact_Icc.image (continuous_laplacePoint l))
  exact ⟨C, hC, fun x hx t ht => hb _ (mem_image_of_mem _ hx) t ht⟩

end GapFamily.Analytic.SpatialPoint
