import GapFamily.Analytic.Poincare.Continuation.PoincareLaplaceDifferenceContinuation
import GapFamily.Analytic.Transform.LaplaceThresholdReference

/-!
# The actual threshold difference against the physical reference measure

At the threshold the same-parameter cone factor becomes exactly the ordinary
reference density. The resulting reference-measure integral of the actual
continued seed is absolutely integrable, including in the scalar spin row,
and evaluates to the actual general threshold seed.
-/

noncomputable section
namespace GapFamily.Analytic.PoincareEnergyContinuation
open Set Filter MeasureTheory UpperHalfPlane CuspFourierCutoff PoincareCanonical

private theorem zero_mem_chosen_continuation (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) :
    (0 : ℂ) ∈ continuationRegion (chosenContinuation K hKH).radius := by
  exact Or.inl (by simpa only [Metric.mem_ball, dist_self] using
    (chosenContinuation K hKH).radius_pos)

/-- The reference-measure version of the actual threshold seed difference
is ordinarily absolutely integrable in compact spatial norm. -/
theorem integrable_seedLaplaceDifference_reference (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (J : ℤ) {t d : ℝ} (ht : 0 < t) (hd : 0 ≤ d) :
    Integrable (fun E : ℝ => (thermalHeightDifference t d E : ℂ) •
      continuedSeedOn K hKH E J 0) (referenceMeasure J) := by
  apply (integrable_cpow_one_half_smul_iff_referenceMeasure J _).mp
  have hi := integrableOn_seedLaplaceDifferenceOn K hKH J ht hd
    (zero_mem_chosen_continuation K hKH)
  simpa only [coneLaplaceDifferenceWeight, exponent, add_zero,
    show (1 / 2 : ℂ) - 1 = -(1 / 2 : ℂ) by norm_num, mul_smul] using hi

/-- Exact identification with the actual physical reference measure. The
preceding theorem proves ordinary integrability at positive thermal heights. -/
theorem seedLaplaceDifferenceOn_zero_eq_reference (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (J : ℤ) (t d : ℝ) :
    seedLaplaceDifferenceOn K hKH J t d 0 =
      ∫ E : ℝ, (thermalHeightDifference t d E : ℂ) •
        continuedSeedOn K hKH E J 0 ∂referenceMeasure J := by
  unfold seedLaplaceDifferenceOn
  simpa only [coneLaplaceDifferenceWeight, exponent, add_zero,
    show (1 / 2 : ℂ) - 1 = -(1 / 2 : ℂ) by norm_num, mul_smul] using
      integral_cpow_one_half_smul_eq_referenceMeasure J
        (fun E : ℝ => (thermalHeightDifference t d E : ℂ) • continuedSeedOn K hKH E J 0)

/-- Point evaluation of the actual threshold finite difference is an
ordinary absolutely integrable function under the physical reference measure. -/
theorem integrable_thermalHeightDifference_generalThresholdSeed
    (K : Set ℂ) [CompactSpace K] (hKH : K ⊆ upperHalfPlaneSet) (J : ℤ)
    {t d : ℝ} (ht : 0 < t) (hd : 0 ≤ d) (τ : UpperHalfPlane) (hτ : (τ : ℂ) ∈ K) :
    Integrable (fun E : ℝ => (thermalHeightDifference t d E : ℂ) *
      generalThresholdSeed E J τ) (referenceMeasure J) := by
  have hi := (ContinuousMap.evalCLM ℂ (⟨τ, hτ⟩ : K)).integrable_comp
    (integrable_seedLaplaceDifference_reference K hKH J ht hd)
  apply hi.congr
  filter_upwards [] with E
  change (thermalHeightDifference t d E : ℂ) *
    continuedSeedOn K hKH E J 0 ⟨τ, hτ⟩ = _
  rw [generalThresholdSeed_eq_compact K hKH E J τ hτ]

/-- The analytically continued compact cone integral evaluates at threshold
to the actual general seed integrated against the actual reference measure. -/
theorem seedLaplaceDifferenceOn_zero_apply (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (J : ℤ) {t d : ℝ} (ht : 0 < t) (hd : 0 ≤ d)
    (τ : UpperHalfPlane) (hτ : (τ : ℂ) ∈ K) :
    seedLaplaceDifferenceOn K hKH J t d 0 ⟨τ, hτ⟩ =
      ∫ E : ℝ, (thermalHeightDifference t d E : ℂ) *
        generalThresholdSeed E J τ ∂referenceMeasure J := by
  rw [seedLaplaceDifferenceOn_zero_eq_reference]
  have hi := integrable_seedLaplaceDifference_reference K hKH J ht hd
  calc
    _ = ∫ E : ℝ, (thermalHeightDifference t d E : ℂ) *
        continuedSeedOn K hKH E J 0 ⟨τ, hτ⟩ ∂referenceMeasure J :=
      ((ContinuousMap.evalCLM ℂ (⟨τ, hτ⟩ : K)).integral_comp_comm hi).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with E
      rw [generalThresholdSeed_eq_compact K hKH E J τ hτ]

end GapFamily.Analytic.PoincareEnergyContinuation
