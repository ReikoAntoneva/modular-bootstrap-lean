import GapFamily.Analytic.Poincare.Continuation.PoincareLaplaceDifferenceReference
import GapFamily.Analytic.Transform.LaplaceTest

/-!
# Same-parameter continuation of actual Laplace tests

The exponent domain is the translated genuine seed-continuation domain. It
connects original convergence to `s = 1/2` by going around the excluded pole
`s = 1`. The energy integral uses the actual compact continued seed and the
literal finite Laplace test.
-/

noncomputable section
namespace GapFamily.Analytic.PoincareEnergyContinuation
open Set Filter MeasureTheory UpperHalfPlane CuspFourierCutoff PoincareCanonical
open scoped Topology

/-- The original `s` coordinate of the actual seed-continuation region. -/
def exponentContinuationRegion (r : ℝ) : Set ℂ :=
  {s | s - (1 / 2 : ℂ) ∈ continuationRegion r}

theorem exponentContinuationRegion_eq (r : ℝ) :
    exponentContinuationRegion r =
      Metric.ball (1 / 2 : ℂ) r ∪ {s : ℂ | (1 / 2 : ℝ) < s.re ∧ s ≠ 1} := by
  ext s
  have he : s - (1 / 2 : ℂ) ≠ (1 / 2 : ℂ) ↔ s ≠ 1 := by
    constructor
    · intro h hs
      apply h
      rw [hs]
      norm_num
    · intro h hs
      apply h
      calc s = (s - 1 / 2) + 1 / 2 := by ring
           _ = 1 := by rw [hs]; norm_num
  have hr : 0 < (s - (1 / 2 : ℂ)).re ↔ (1 / 2 : ℝ) < s.re := by
    norm_num [Complex.sub_re]
  change ((s - (1 / 2 : ℂ)) ∈ Metric.ball 0 r ∨
    (0 < (s - (1 / 2 : ℂ)).re ∧ s - 1 / 2 ≠ 1 / 2)) ↔ _
  rw [hr, he]
  simp only [mem_union, mem_ofPred_eq, Metric.mem_ball, dist_eq_norm, sub_zero]

theorem isOpen_exponentContinuationRegion (r : ℝ) :
    IsOpen (exponentContinuationRegion r) :=
  (isOpen_continuationRegion r).preimage (continuous_id.sub continuous_const)

theorem exponentContinuationRegion_eq_image (r : ℝ) :
    exponentContinuationRegion r = exponent '' continuationRegion r := by
  ext s
  constructor
  · intro hs
    refine ⟨s - 1 / 2, hs, ?_⟩
    simp [exponent]
  · rintro ⟨κ, hκ, rfl⟩
    change exponent κ - 1 / 2 ∈ continuationRegion r
    simpa [exponent] using hκ

theorem isPreconnected_exponentContinuationRegion {r : ℝ} (hr : 0 < r) :
    IsPreconnected (exponentContinuationRegion r) := by
  rw [exponentContinuationRegion_eq_image]
  exact (isPreconnected_continuationRegion hr).image _ (by unfold exponent; fun_prop)

theorem one_half_mem_exponentContinuationRegion {r : ℝ} (hr : 0 < r) :
    (1 / 2 : ℂ) ∈ exponentContinuationRegion r := by
  change (1 / 2 : ℂ) - 1 / 2 ∈ continuationRegion r
  left
  simpa using hr

theorem mem_exponentContinuationRegion_of_re_gt_one {s : ℂ} (hs : 1 < s.re) (r : ℝ) :
    s ∈ exponentContinuationRegion r := by
  rw [exponentContinuationRegion_eq]
  right
  refine ⟨by linarith, ?_⟩
  intro h
  simp [h] at hs

theorem thermalHeightDifference_eq_laplaceTest (k : ℕ) (E : ℝ) :
    thermalHeightDifference ((k : ℝ) + 1) 1 E = laplaceTest k E := by
  rw [thermalHeightDifference_eq]
  simp only [laplaceTest, neg_mul, one_mul]

/-- The actual input Laplace test, using the original exponent `s`. -/
def laplaceSeedOn (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (J : ℤ) (l : ℕ) (s : ℂ) : C(K, ℂ) :=
  seedLaplaceDifferenceOn K hKH J ((l : ℝ) + 1) 1 (s - 1 / 2)

private theorem exponent_sub_half (s : ℂ) : exponent (s - 1 / 2) = s := by
  unfold exponent
  ring

/-- The Banach-valued family is literally the requested same-parameter cone integral. -/
theorem laplaceSeedOn_eq_integral (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (J : ℤ) (l : ℕ) (s : ℂ) :
    laplaceSeedOn K hKH J l s =
      ∫ E : ℝ in Ioi |(J : ℝ)|,
        (((E ^ 2 - (J : ℝ) ^ 2 : ℝ) : ℂ) ^ (s - 1) * (laplaceTest l E : ℂ)) •
          continuedSeedOn K hKH E J (s - 1 / 2) := by
  simp only [laplaceSeedOn, seedLaplaceDifferenceOn, coneLaplaceDifferenceWeight,
    exponent_sub_half, thermalHeightDifference_eq_laplaceTest]

/-- Ordinary integrability of the actual cone integral throughout its continuation domain. -/
theorem integrableOn_laplaceSeedOn (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (J : ℤ) (l : ℕ) {s : ℂ}
    (hs : s ∈ exponentContinuationRegion (chosenContinuation K hKH).radius) :
    IntegrableOn (fun E : ℝ =>
      (((E ^ 2 - (J : ℝ) ^ 2 : ℝ) : ℂ) ^ (s - 1) * (laplaceTest l E : ℂ)) •
        continuedSeedOn K hKH E J (s - 1 / 2)) (Ioi |(J : ℝ)|) := by
  simpa only [coneLaplaceDifferenceWeight, exponent_sub_half,
    thermalHeightDifference_eq_laplaceTest] using
      integrableOn_seedLaplaceDifferenceOn K hKH J
        (show 0 < (l : ℝ) + 1 by positivity) (show (0 : ℝ) ≤ 1 by norm_num) hs

/-- Norm analyticity follows from proved physical energy domination, with the same
parameter as the spatial orbit kernel. -/
theorem analyticOnNhd_laplaceSeedOn (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (J : ℤ) (l : ℕ) :
    AnalyticOnNhd ℂ (laplaceSeedOn K hKH J l)
      (exponentContinuationRegion (chosenContinuation K hKH).radius) := by
  intro s hs
  exact (analyticOnNhd_seedLaplaceDifferenceOn K hKH J
    (show 0 < (l : ℝ) + 1 by positivity) (show (0 : ℝ) ≤ 1 by norm_num)
      (s - 1 / 2) hs).comp_of_eq
    (show AnalyticAt ℂ (fun ξ : ℂ => ξ - (1 / 2 : ℂ)) s from
      analyticAt_id.sub analyticAt_const) rfl

/-- Compact evaluation commutes with the ordinary same-parameter energy integral. -/
theorem laplaceSeedOn_apply (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (J : ℤ) (l : ℕ) {s : ℂ}
    (hs : s ∈ exponentContinuationRegion (chosenContinuation K hKH).radius) (z : K) :
    laplaceSeedOn K hKH J l s z =
      ∫ E : ℝ in Ioi |(J : ℝ)|,
        ((E ^ 2 - (J : ℝ) ^ 2 : ℝ) : ℂ) ^ (s - 1) * (laplaceTest l E : ℂ) *
          continuedSeedOn K hKH E J (s - 1 / 2) z := by
  simpa only [laplaceSeedOn, coneLaplaceDifferenceWeight, exponent_sub_half,
    thermalHeightDifference_eq_laplaceTest] using
      seedLaplaceDifferenceOn_apply K hKH J
        (show 0 < (l : ℝ) + 1 by positivity) (show (0 : ℝ) ≤ 1 by norm_num) hs z

/-- The family recovers the literal original Poincaré series for `Re s > 1`. -/
theorem laplaceSeedOn_eq_original (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (J : ℤ) (l : ℕ) {s : ℂ} (hs : 1 < s.re) (z : K) :
    laplaceSeedOn K hKH J l s z =
      ∫ E : ℝ in Ioi |(J : ℝ)|,
        ((E ^ 2 - (J : ℝ) ^ 2 : ℝ) : ℂ) ^ (s - 1) * (laplaceTest l E : ℂ) *
          complexPoincareSeries E J s (ofComplex z) := by
  rw [laplaceSeedOn_apply K hKH J l (mem_exponentContinuationRegion_of_re_gt_one hs _) z]
  apply integral_congr_ae
  exact Eventually.of_forall fun E => by
    dsimp only
    rw [continuedSeedOn_eq_series_full_convergence K hKH E J
      (show (1 / 2 : ℝ) < (s - (1 / 2 : ℂ)).re by
        norm_num [Complex.sub_re]; linarith) z, exponent_sub_half]

/-- At the endpoint the continued family is the actual canonical threshold seed,
under the same literal cone density and finite input Laplace test. -/
theorem laplaceSeedOn_one_half (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (J : ℤ) (l : ℕ) (τ : UpperHalfPlane)
    (hτ : (τ : ℂ) ∈ K) :
    laplaceSeedOn K hKH J l (1 / 2) ⟨τ, hτ⟩ =
      ∫ E : ℝ in Ioi |(J : ℝ)|,
        ((E ^ 2 - (J : ℝ) ^ 2 : ℝ) : ℂ) ^ (-(1 / 2) : ℂ) * (laplaceTest l E : ℂ) *
          generalThresholdSeed E J τ := by
  rw [laplaceSeedOn_apply K hKH J l
    (one_half_mem_exponentContinuationRegion (chosenContinuation K hKH).radius_pos)]
  apply integral_congr_ae
  exact Eventually.of_forall fun E => by
    norm_num only [sub_self, show (1 / 2 : ℂ) - 1 = -(1 / 2) by norm_num]
    rw [generalThresholdSeed_eq_compact K hKH E J τ hτ]

/-- The endpoint compact value is exactly the ordinary physical reference integral. -/
theorem laplaceSeedOn_one_half_eq_reference (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (J : ℤ) (l : ℕ) :
    laplaceSeedOn K hKH J l (1 / 2) =
      ∫ E : ℝ, (laplaceTest l E : ℂ) • continuedSeedOn K hKH E J 0 ∂referenceMeasure J := by
  simp only [laplaceSeedOn, sub_self, seedLaplaceDifferenceOn_zero_eq_reference,
    thermalHeightDifference_eq_laplaceTest]

/-- Every actual point threshold seed is integrable against the input reference test. -/
theorem integrable_laplaceTest_generalThresholdSeed (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (J : ℤ) (l : ℕ) (τ : UpperHalfPlane)
    (hτ : (τ : ℂ) ∈ K) :
    Integrable (fun E : ℝ => (laplaceTest l E : ℂ) * generalThresholdSeed E J τ)
      (referenceMeasure J) := by
  simpa only [thermalHeightDifference_eq_laplaceTest] using
    integrable_thermalHeightDifference_generalThresholdSeed K hKH J
      (show 0 < (l : ℝ) + 1 by positivity) (show (0 : ℝ) ≤ 1 by norm_num) τ hτ

/-- Exact actual seed/reference identification of the continued spatial-side input test. -/
theorem laplaceSeedOn_one_half_apply_reference (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (J : ℤ) (l : ℕ) (τ : UpperHalfPlane)
    (hτ : (τ : ℂ) ∈ K) :
    laplaceSeedOn K hKH J l (1 / 2) ⟨τ, hτ⟩ =
      ∫ E : ℝ, (laplaceTest l E : ℂ) * generalThresholdSeed E J τ ∂referenceMeasure J := by
  simpa only [laplaceSeedOn, sub_self, thermalHeightDifference_eq_laplaceTest] using
    seedLaplaceDifferenceOn_zero_apply K hKH J
      (show 0 < (l : ℝ) + 1 by positivity) (show (0 : ℝ) ≤ 1 by norm_num) τ hτ

/-- Convergence from the physical real interval to threshold holds in the actual
compact spatial norm, as a consequence of the proved analytic energy integral. -/
theorem laplaceSeedOn_tendsto_one_half (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (J : ℤ) (l : ℕ) :
    Tendsto (fun s : ℝ => laplaceSeedOn K hKH J l (s : ℂ))
      (nhdsWithin (1 / 2 : ℝ) (Ioi (1 / 2)))
      (𝓝 (laplaceSeedOn K hKH J l (1 / 2))) := by
  have ha := analyticOnNhd_laplaceSeedOn K hKH J l (1 / 2)
    (one_half_mem_exponentContinuationRegion (chosenContinuation K hKH).radius_pos)
  have hcont : ContinuousAt (fun s : ℝ => laplaceSeedOn K hKH J l (s : ℂ)) (1 / 2) :=
    ha.continuousAt.comp_of_eq Complex.continuous_ofReal.continuousAt (by norm_num)
  simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
    hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (1 / 2 : ℝ)))

end GapFamily.Analytic.PoincareEnergyContinuation
