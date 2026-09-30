import GapFamily.Analytic.Modular.Elliptic.ModularInteriorCompactUpperOperator
import GapFamily.Analytic.Modular.Elliptic.ModularInteriorCompactUpperRellich

/-!
# Compactness of actual upper-half-plane cutoffs on the modular form domain

The actual graph-core approximation transfers the proved Euclidean Rellich
compactness to the completed modular form domain, including cutoffs crossing seams. No local Sobolev or
compactness hypothesis is assumed.
-/

noncomputable section

namespace GapFamily.Analytic.ModularGradient

open Set MeasureTheory Filter UpperHalfPlane
open scoped ContDiff Topology

/-- A smooth compact upper-half-plane cutoff gives an actual compact operator from the
completed modular form domain into the literal local Euclidean L² space. -/
theorem isCompactOperator_upperCutoffOperator (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ upperHalfPlaneSet)
    (T : Set ℂ) [CompactSpace T] :
    IsCompactOperator (upperCutoffOperator χ hχ hc hs T) := by
  let S : Set (Lp ℂ 2 (LocalSobolev.restrictedVolume T)) :=
    range (fun F : {F : smoothCore // ‖coreForm F‖ ≤ 2} =>
      upperCutoffCoreMap χ hχ hs T F.val)
  have hS : TotallyBounded S := totallyBounded_upperCutoff_core hχ hc hs T (by norm_num)
  refine ⟨closure S, hS.closure.isCompact_of_isClosed isClosed_closure, ?_⟩
  apply mem_of_superset (Metric.ball_mem_nhds (0 : FormDomain) (by norm_num : 0 < (1 : ℝ)))
  intro u hu
  change upperCutoffOperator χ hχ hc hs T u ∈ closure S
  have hun : ‖u‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hu
  obtain ⟨F, hF, hb⟩ := exists_coreForm_tendsto_bounded u
  have hlim := (upperCutoffOperator χ hχ hc hs T).continuous.continuousAt.tendsto.comp hF
  apply mem_closure_of_tendsto hlim
  refine Eventually.of_forall fun n => ?_
  change upperCutoffOperator χ hχ hc hs T (coreForm (F n)) ∈ S
  rw [upperCutoffOperator_coreForm]
  exact ⟨⟨F n, by have h := hb n; linarith⟩, rfl⟩

/-- Every form-norm bounded ball has relatively compact actual cutoff image. -/
theorem upperCutoffOperator_isCompact_closure_image_closedBall
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet) (T : Set ℂ) [CompactSpace T] (R : ℝ) :
    IsCompact (closure ((upperCutoffOperator χ hχ hc hs T) '' Metric.closedBall 0 R)) :=
  (isCompactOperator_upperCutoffOperator χ hχ hc hs T).isCompact_closure_image_closedBall R

end GapFamily.Analytic.ModularGradient
