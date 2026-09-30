import GapFamily.Analytic.Poincare.Continuation.PoincareCompactEnergyAnalytic
import GapFamily.Analytic.Poincare.Threshold.PoincareThresholdValue

/-! The actual energy correction combined with the constructed spinning base. -/
noncomputable section
namespace GapFamily.Analytic.PoincareEnergyContinuation
open Set UpperHalfPlane CuspFourierCutoff PoincareCanonical
open PoincareEnergyConvergentAnalytic

/-- The genuine compact family at arbitrary complex energy. -/
def continuedSeedOn (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (E : ℂ) (J : ℤ) (κ : ℂ) : C(K, ℂ) :=
  (chosenContinuation K hKH).family J κ + compactEnergySeries K hKH E J (exponent κ)

/-- The whole chosen continuation region stays in the correction's convergence range. -/
theorem re_gt_neg_half_of_mem_continuation {K : Set ℂ} [CompactSpace K]
    (D : Continuation K) {κ : ℂ} (hκ : κ ∈ continuationRegion D.radius) :
    (-1 / 2 : ℝ) < κ.re := by
  rcases hκ with hκ | hκ
  · have hn : ‖κ‖ < D.radius := by simpa only [Metric.mem_ball, dist_zero_right] using hκ
    have ha := (abs_le.mp (Complex.abs_re_le_norm κ)).1
    have hr := D.radius_le_eighth
    linarith
  · linarith [hκ.1]

/-- Norm analyticity through threshold and on the complete physical region,
at every complex energy and integer spin. -/
theorem analyticOnNhd_continuedSeedOn (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (E : ℂ) (J : ℤ) :
    AnalyticOnNhd ℂ (continuedSeedOn K hKH E J)
      (continuationRegion (chosenContinuation K hKH).radius) := by
  intro κ hκ
  exact ((chosenContinuation K hKH).analytic_family J κ hκ).add
    (compactEnergySeries_analyticAt_parameter K hKH E J
      (re_gt_neg_half_of_mem_continuation (chosenContinuation K hKH) hκ))

/-- Equality with the original general-energy series in the genuine common region. -/
theorem continuedSeedOn_eq_series (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (E : ℂ) (J : ℤ) {κ : ℂ}
    (hκ : (3 / 2 : ℝ) < κ.re) (z : K) :
    continuedSeedOn K hKH E J κ z =
      complexPoincareSeries E J (exponent κ) (ofComplex z) := by
  have hs : 1 < (exponent κ).re := by
    norm_num [exponent, Complex.add_re]
    linarith
  change (chosenContinuation K hKH).family J κ z +
    compactEnergySeries K hKH E J (exponent κ) z = _
  rw [(chosenContinuation K hKH).common_region J κ hκ z,
    compactEnergySeries_apply K hKH E J (by linarith),
    complexPoincareEnergyDifference_eq_sub E J hs]
  ring

/-- One disk works for every spin and every energy in a fixed bounded range;
the correction retains its linear factor in the energy norm. -/
theorem exists_continuedSeedOn_norm_bound (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (B : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (E : ℂ), ‖E‖ ≤ B → ∀ (J : ℤ) (κ : ℂ),
      ‖κ‖ ≤ (chosenContinuation K hKH).radius →
      ‖continuedSeedOn K hKH E J κ‖ ≤ C * (1 + (J : ℝ) ^ 2 + ‖E‖) := by
  obtain ⟨C, hC, hbound⟩ := exists_compactEnergySeries_parameter_norm_bound K hKH B
  let D := chosenContinuation K hKH
  refine ⟨D.bound + C, add_pos D.bound_pos hC, ?_⟩
  intro E hE J κ hκ
  calc
    _ ≤ ‖D.family J κ‖ + ‖compactEnergySeries K hKH E J (exponent κ)‖ :=
      norm_add_le _ _
    _ ≤ D.bound * (1 + (J : ℝ) ^ 2) + C * ‖E‖ :=
      add_le_add (D.uniform_bound J κ hκ) (hbound E hE J κ (hκ.trans D.radius_le_eighth))
    _ ≤ _ := by
      nlinarith [mul_nonneg D.bound_pos.le (norm_nonneg E),
        mul_nonneg hC.le (sq_nonneg (J : ℝ))]

/-- The compact continuation exists with an energy- and spin-independent radius. -/
theorem exists_generalEnergyContinuation (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (B : ℝ) :
    ∃ (P : ℂ → ℤ → ℂ → C(K, ℂ)) (r C : ℝ),
      0 < r ∧ r ≤ 1 / 8 ∧ 0 < C ∧
      (∀ (E : ℂ) (J : ℤ), AnalyticOnNhd ℂ (P E J) (continuationRegion r)) ∧
      (∀ (E : ℂ), ‖E‖ ≤ B → ∀ (J : ℤ) (κ : ℂ), ‖κ‖ ≤ r →
        ‖P E J κ‖ ≤ C * (1 + (J : ℝ) ^ 2 + ‖E‖)) ∧
      ∀ (E : ℂ) (J : ℤ) (κ : ℂ), (3 / 2 : ℝ) < κ.re → ∀ z : K,
        P E J κ z = complexPoincareSeries E J (exponent κ) (ofComplex z) := by
  obtain ⟨C, hC, hb⟩ := exists_continuedSeedOn_norm_bound K hKH B
  refine ⟨continuedSeedOn K hKH, (chosenContinuation K hKH).radius, C,
    (chosenContinuation K hKH).radius_pos, (chosenContinuation K hKH).radius_le_eighth,
    hC, analyticOnNhd_continuedSeedOn K hKH, hb, ?_⟩
  intro E J κ hκ z
  exact continuedSeedOn_eq_series K hKH E J hκ z

end GapFamily.Analytic.PoincareEnergyContinuation
