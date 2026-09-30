import GapFamily.Analytic.Spatial.SpatialOrbitContinuedOperator
import GapFamily.Analytic.Spatial.SpatialOrbitFourierInput
import GapFamily.Analytic.Spatial.SpatialOrbitFourierLaplace
import GapFamily.Analytic.Poincare.Continuation.PoincareLaplaceContinuation

/-! Analytic uniqueness connects the actual spatial Fourier/height test to
the actual Poincaré input Laplace integral. Both families are already
constructed and analytic on their common connected domain; the original
convergent-region identity fixes the threshold value. -/

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open Set Filter MeasureTheory UpperHalfPlane UpperWeightedCoherence
open PoincareCanonical PoincareEnergyContinuation PoincareEnergyFourier CuspFourierCutoff
open scoped Topology

theorem spatialOrbitPhysicalOperator_sourceHeight
    (K : Set ℂ) [CompactSpace K] (D : Evaluation (1 / 4) (by norm_num) K)
    (s : ℂ) (hs : 1 < s.re) (J : ℤ) (l : ℕ) (z : UpperHalfPlane) (hz : (z : ℂ) ∈ K) :
    spatialOrbitPhysicalOperator D.cutoff D.cutoff_smooth D.cutoff_compact D.cutoff_support
      D.region D.open_region D.one_region K D.compact_subset (s - 1 / 2)
      (spatialSourceFourierHeightInput s J l) ⟨(z : ℂ), hz⟩ =
        spatialOrbitSourceHeightDifference s J l z := by
  rw [eval_map_spatialSourceFourierHeightInput _ _ s (by linarith)]
  have hp (n : ℕ) (x : ℝ) :
      spatialOrbitPhysicalOperator D.cutoff D.cutoff_smooth D.cutoff_compact D.cutoff_support
        D.region D.open_region D.one_region K D.compact_subset (s - 1 / 2)
        (spatialOrbitThresholdInput s (laplacePoint n x)) ⟨(z : ℂ), hz⟩ =
          spatialOrbitKernel s z (laplacePoint n x) :=
    spatialOrbitPhysicalOperator_spatialInput D.cutoff D.cutoff_smooth D.cutoff_compact
      D.cutoff_support D.region D.open_region D.one_region K D.compact_subset s hs _ z hz
  simp_rw [hp, horizontalPhase_eq_cuspFourierMode]
  simp only [spatialOrbitSourceHeightDifference, Complex.cpow_neg, div_eq_mul_inv]
  ring

private theorem exponent_re_pos_of_region {r : ℝ} (hr : r ≤ 1 / 4)
    {κ : ℂ} (hκ : κ ∈ continuationRegion r) : 0 < (exponent κ).re := by
  rcases hκ with hκ | hκ
  · have hn : ‖κ‖ < r := by simpa only [Metric.mem_ball, dist_zero_right] using hκ
    have ha := Complex.abs_re_le_norm κ
    have hl := neg_abs_le κ.re
    dsimp [exponent]
    norm_num only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re]
    linarith
  · dsimp [exponent]
    norm_num only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re]
    linarith [hκ.1]

/-- The canonical threshold spatial source test equals the ordinary compact
energy integral. No spatial continuation or positivity premise is supplied. -/
theorem weightedThresholdValue_sourceHeight_eq_laplaceSeedOn
    (K : Set ℂ) [CompactSpace K] (hKH : K ⊆ upperHalfPlaneSet)
    (J : ℤ) (l : ℕ) (z : UpperHalfPlane) (hz : (z : ℂ) ∈ K) :
    weightedThresholdValue (1 / 4) (by norm_num)
      (spatialSourceFourierHeightInput (1 / 2) J l) z =
        laplaceSeedOn K hKH J l (1 / 2) ⟨(z : ℂ), hz⟩ := by
  obtain ⟨D, A, R, hR, hRq, _, _, hA, hphysical, hzero⟩ :=
    exists_spatialOrbitContinuedOperator K hKH
  let r := min R (chosenContinuation K hKH).radius
  have hr : 0 < r := lt_min hR (chosenContinuation K hKH).radius_pos
  have hrR : r ≤ R := min_le_left _ _
  have hrP : r ≤ (chosenContinuation K hKH).radius := min_le_right _ _
  have hrq : r ≤ 1 / 4 := hrR.trans hRq
  let F : ℂ → C(K, ℂ) := fun κ => A κ (spatialSourceFourierHeightInput (exponent κ) J l)
  let G : ℂ → C(K, ℂ) := fun κ => spatialLaplaceConstantComplex (exponent κ) •
    laplaceSeedOn K hKH J l (exponent κ)
  have hF : AnalyticOnNhd ℂ F (continuationRegion r) := by
    intro κ hκ
    have hinput := (analyticAt_spatialSourceFourierHeightInput J l
      (exponent_re_pos_of_region hrq hκ)).comp
        (show AnalyticAt ℂ exponent κ by unfold exponent; exact analyticAt_const.add analyticAt_id)
    exact ((ContinuousLinearMap.apply ℂ C(K, ℂ)).analyticAt_bilinear _).comp₂ hinput
      (hA κ (continuationRegion_mono hrR hκ))
  have hG : AnalyticOnNhd ℂ G (continuationRegion r) := by
    intro κ hκ
    have he : exponent κ ∈ exponentContinuationRegion (chosenContinuation K hKH).radius := by
      change exponent κ - 1 / 2 ∈ continuationRegion (chosenContinuation K hKH).radius
      simpa [exponent] using continuationRegion_mono hrP hκ
    have he' : AnalyticAt ℂ exponent κ := by
      unfold exponent
      exact analyticAt_const.add analyticAt_id
    exact ((analyticAt_spatialLaplaceConstantComplex _).comp he').smul
      ((analyticOnNhd_laplaceSeedOn K hKH J l _ he).comp he')
  have heq : EqOn F G (continuationRegion r) :=
    eqOn_continuationRegion_of_common hr hF hG (by
      intro κ hκ
      have hs : 1 < (exponent κ).re := by
        dsimp [exponent]
        norm_num only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re]
        linarith
      have hp : 0 < κ.re := by linarith
      have hne : κ ≠ (1 / 2 : ℂ) := by
        intro he
        rw [he] at hκ
        norm_num at hκ
      apply ContinuousMap.ext
      intro v
      let w : UpperHalfPlane := ⟨v, hKH v.property⟩
      have hw : (w : ℂ) ∈ K := v.property
      change A κ (spatialSourceFourierHeightInput (exponent κ) J l) v =
        spatialLaplaceConstantComplex (exponent κ) * laplaceSeedOn K hKH J l (exponent κ) v
      rw [hphysical κ hp hne]
      have hk : exponent κ - (1 / 2 : ℂ) = κ := by unfold exponent; ring
      have hval := spatialOrbitPhysicalOperator_sourceHeight K D (exponent κ) hs J l w hw
      rw [hk] at hval
      rw [hval,
        spatialOrbitSourceHeightDifference_eq_poincare_laplaceTest _ hs,
        laplaceSeedOn_eq_original K hKH J l hs]
      congr 2
      funext E
      rw [show (ofComplex (v : ℂ) : UpperHalfPlane) = w from ofComplex_apply w])
  have hz0 : (0 : ℂ) ∈ continuationRegion r := by
    left
    simpa using hr
  have hv := congrArg (fun f : C(K, ℂ) => f ⟨(z : ℂ), hz⟩) (heq hz0)
  simpa only [F, G, exponent, add_zero, spatialLaplaceConstantComplex_one_half,
    one_smul, hzero] using hv

/-- The actual threshold spatial source test has the same ordinary reference
measure as the actual energy kernel and canonical seed. -/
theorem weightedThresholdValue_sourceHeight_eq_reference
    (K : Set ℂ) [CompactSpace K] (hKH : K ⊆ upperHalfPlaneSet)
    (J : ℤ) (l : ℕ) (z : UpperHalfPlane) (hz : (z : ℂ) ∈ K) :
    weightedThresholdValue (1 / 4) (by norm_num)
      (spatialSourceFourierHeightInput (1 / 2) J l) z =
        ∫ E : ℝ, (laplaceTest l E : ℂ) * generalThresholdSeed E J z ∂referenceMeasure J := by
  rw [weightedThresholdValue_sourceHeight_eq_laplaceSeedOn K hKH J l z hz,
    laplaceSeedOn_one_half_apply_reference]

/-- Pointwise form of the actual threshold spatial-to-energy identity. -/
theorem weightedThresholdValue_sourceHeight_eq_reference_point
    (J : ℤ) (l : ℕ) (z : UpperHalfPlane) :
    weightedThresholdValue (1 / 4) (by norm_num)
      (spatialSourceFourierHeightInput (1 / 2) J l) z =
        ∫ E : ℝ, (laplaceTest l E : ℂ) * generalThresholdSeed E J z ∂referenceMeasure J := by
  let K : Set ℂ := {(z : ℂ)}
  let : CompactSpace K := isCompact_iff_compactSpace.mp isCompact_singleton
  have hKH : K ⊆ upperHalfPlaneSet := by
    intro w hw
    have hwz : w = (z : ℂ) := Set.mem_singleton_iff.mp hw
    subst w
    exact z.im_pos
  exact weightedThresholdValue_sourceHeight_eq_reference K hKH J l z (by simp [K])

end GapFamily.Analytic.SpatialPoint
