import GapFamily.Analytic.Cusp.Green.CuspGreenOperatorTrace

/-! Continuity of the ordinary primitive of an arbitrary finite-collar `L²` source. -/

noncomputable section

namespace GapFamily.Analytic

open MeasureTheory Set Filter
open scoped Topology

theorem measurableSet_cuspCollarPrimitiveSlice (T t : ℝ) :
    MeasurableSet {u : CuspGreenCollar 0 T | (u : ℝ) ≤ t} :=
  measurableSet_le measurable_subtype_coe measurable_const

/-- The ordinary source primitive is continuous even when its source is only in `L²`. -/
theorem continuous_cuspCollarPrimitiveIntegral (T : ℝ)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure 0 T)) :
    Continuous (fun t : ℝ =>
      ∫ u in {u : CuspGreenCollar 0 T | (u : ℝ) ≤ t},
        f u ∂cuspGreenCollarMeasure 0 T) := by
  let μ := cuspGreenCollarMeasure 0 T
  let F : ℝ → CuspGreenCollar 0 T → ℂ :=
    fun t => {u : CuspGreenCollar 0 T | (u : ℝ) ≤ t}.indicator f
  have hf : Integrable f μ := cuspGreenCollarSource_integrable 0 T f
  have heq : (fun t : ℝ =>
      ∫ u in {u : CuspGreenCollar 0 T | (u : ℝ) ≤ t}, f u ∂μ) =
      fun t => ∫ u, F t u ∂μ := by
    funext t
    exact (integral_indicator (measurableSet_cuspCollarPrimitiveSlice T t)).symm
  change Continuous (fun t : ℝ =>
    ∫ u in {u : CuspGreenCollar 0 T | (u : ℝ) ≤ t}, f u ∂μ)
  rw [heq, continuous_iff_continuousAt]
  intro t₀
  apply continuousAt_of_dominated (bound := fun u => ‖f u‖)
  · exact Eventually.of_forall fun t =>
      hf.aestronglyMeasurable.indicator (measurableSet_cuspCollarPrimitiveSlice T t)
  · exact Eventually.of_forall fun t => Eventually.of_forall fun u => by
      dsimp [F, indicator]
      split_ifs <;> simp
  · exact hf.norm
  · have hne : ∀ᵐ (u : CuspGreenCollar 0 T) ∂μ, (u : ℝ) ≠ t₀ :=
      (ae_restrict_iff_subtype measurableSet_Icc).mp
        (ae_restrict_of_ae ((volume : Measure ℝ).ae_ne t₀))
    filter_upwards [hne] with u hu
    rcases lt_or_gt_of_ne hu with hu | hu
    · apply (continuousAt_const : ContinuousAt (fun _ : ℝ => f u) t₀).congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds hu] with t ht
      have ht' : (u : ℝ) < t := ht
      simp [F, ht'.le]
    · apply (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℂ)) t₀).congr_of_eventuallyEq
      filter_upwards [Iio_mem_nhds hu] with t ht
      have ht' : t < (u : ℝ) := ht
      simp [F, not_le.mpr ht']

end GapFamily.Analytic
