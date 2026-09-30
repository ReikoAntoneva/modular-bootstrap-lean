import GapFamily.Analytic.Foundation.AnalyticL2Family
import GapFamily.Analytic.Spatial.SpatialOrbitWeightedSource

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open Set Filter MeasureTheory Metric UpperHalfPlane

/-- The literal weighted modular L2 point source is norm analytic in its genuine
convergence half-plane. The cusp weight is square integrable precisely in the
proved range used here; no continuation outside that half-plane is asserted. -/
theorem analyticAt_spatialOrbitWeightedSource_parameter (α : ℝ) (hα : 0 ≤ α)
    (hhalf : α < 1 / 2) (w : UpperHalfPlane) {s : ℂ} (hs : 1 < s.re) :
    AnalyticAt ℂ (fun t => spatialOrbitWeightedSource α hα hhalf t w) s := by
  let σ : ℝ := (1 + s.re) / 2
  let r : ℝ := (s.re - 1) / 2
  have hσ : 1 < σ := by dsimp [σ]; linarith
  have hr : 0 < r := by dsimp [r]; linarith
  have hstrip {t : ℂ} (ht : t ∈ ball s r) : σ ≤ t.re := by
    have hd : ‖t - s‖ < r := by simpa only [mem_ball, dist_eq_norm] using ht
    have he' := Complex.abs_re_le_norm (t - s)
    have hlo := neg_abs_le (t - s).re
    simp only [Complex.sub_re] at he' hlo
    dsimp [σ, r] at *
    linarith
  obtain ⟨C, _, hb⟩ := exists_spatialOrbitKernel_bound σ hσ w
  let B : UpperHalfPlane → ℝ := fun z => C * ‖((z.im ^ α : ℝ) : ℂ)‖
  have hB : MemLp B 2 modularMeasure :=
    (memLp_modularHeightPower α hα hhalf).norm.const_mul C
  apply DominatedL2.analyticAt_L2_of_dominated
    (F := fun t z => ((z.im ^ α : ℝ) : ℂ) * spatialOrbitKernel t z w)
    (B := B) hr
  · intro t ht
    exact spatialOrbitWeightedSource_ae α hα hhalf t (hσ.trans_le (hstrip ht)) w
  · apply Eventually.of_forall
    intro z t ht
    exact analyticAt_const.mul
      (analyticAt_spatialOrbitKernel_parameter z w (hσ.trans_le (hstrip ht)))
  · apply Eventually.of_forall
    intro z t ht
    dsimp only [B]
    rw [norm_mul, mul_comm C]
    exact mul_le_mul_of_nonneg_left
      ((spatialOrbitKernel_norm_le_real_exponent hσ (hstrip ht) z w).trans (hb z))
      (norm_nonneg _)
  · exact hB

/-- Norm analyticity on the full original half-plane, for every actual fixed source. -/
theorem analyticOnNhd_spatialOrbitWeightedSource_parameter (α : ℝ) (hα : 0 ≤ α)
    (hhalf : α < 1 / 2) (w : UpperHalfPlane) :
    AnalyticOnNhd ℂ (fun s => spatialOrbitWeightedSource α hα hhalf s w)
      {s : ℂ | 1 < s.re} := by
  intro s hs
  exact analyticAt_spatialOrbitWeightedSource_parameter α hα hhalf w hs

end GapFamily.Analytic.SpatialPoint
