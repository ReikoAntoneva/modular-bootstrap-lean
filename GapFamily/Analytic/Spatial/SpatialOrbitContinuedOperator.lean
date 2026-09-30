import GapFamily.Analytic.Spatial.SpatialOrbitThresholdEvaluation
import GapFamily.Analytic.Spatial.SpatialOrbitPhysicalValue
import GapFamily.Analytic.Cusp.Schur.CuspSchurPhysicalGraphAnalytic
import GapFamily.Analytic.Foundation.AnalyticBallGlue
import GapFamily.Analytic.Poincare.Continuation.PoincareContinuationRegion

noncomputable section
namespace GapFamily.Analytic.SpatialPoint

open Set Filter MeasureTheory ModularGradient UpperHalfPlane CuspSchurLocal Dirichlet
open CuspSchurPhysicalGraphAnalytic PoincareCanonical UpperWeightedCoherence
open scoped ContDiff Topology

/-- Actual weighted-source evaluation on a compact chart throughout the
punctured physical half-plane, with the parameter `κ = s - 1/2`. -/
def spatialOrbitPhysicalOperator
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ upperHalfPlaneSet)
    (U : Set ℂ) (hU : IsOpen U) (hχU : EqOn χ (fun _ => 1) U)
    (K : Set ℂ) [CompactSpace K] (hKU : K ⊆ U) (κ : ℂ) :
    ModularHilbert →L[ℂ] C(K, ℂ) :=
  (laplacianUpperCompactRestriction χ hχ hc hsχ U hU hχU K hKU).comp
    ((actualSchurGraphResolvent κ).comp (cuspWeightedInput (1 / 4) (by norm_num)))

theorem analyticAt_spatialOrbitPhysicalOperator
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ upperHalfPlaneSet)
    (U : Set ℂ) (hU : IsOpen U) (hχU : EqOn χ (fun _ => 1) U)
    (K : Set ℂ) [CompactSpace K] (hKU : K ⊆ U)
    {κ : ℂ} (hκ : 0 < κ.re) (hp : κ ≠ (1 / 2 : ℂ)) :
    AnalyticAt ℂ (spatialOrbitPhysicalOperator χ hχ hc hsχ U hU hχU K hKU) κ := by
  have hgraph := actualSchurGraphResolvent_analyticAt_physical hκ hp
  let Q : (ModularHilbert →L[ℂ] LaplacianGraphDomain) →L[ℂ]
      ModularHilbert →L[ℂ] LaplacianGraphDomain :=
    { toFun := fun T => T.comp (cuspWeightedInput (1 / 4) (by norm_num))
      map_add' := by intro T S; ext f; rfl
      map_smul' := by intro a T; ext f; rfl
      cont := continuous_id.clm_comp_const _ }
  have hright := (ContinuousLinearMap.analyticAt (𝕜 := ℂ)
    (E := ModularHilbert →L[ℂ] LaplacianGraphDomain)
    (F := ModularHilbert →L[ℂ] LaplacianGraphDomain) Q
    (actualSchurGraphResolvent κ)).comp_of_eq hgraph rfl
  let P : (ModularHilbert →L[ℂ] LaplacianGraphDomain) →L[ℂ]
      ModularHilbert →L[ℂ] C(K, ℂ) :=
    ContinuousLinearMap.compL ℂ ModularHilbert LaplacianGraphDomain C(K, ℂ)
      (laplacianUpperCompactRestriction χ hχ hc hsχ U hU hχU K hKU)
  exact (ContinuousLinearMap.analyticAt (𝕜 := ℂ)
    (E := ModularHilbert →L[ℂ] LaplacianGraphDomain)
    (F := ModularHilbert →L[ℂ] C(K, ℂ)) P _).comp_of_eq hright rfl

theorem spatialOrbitPhysicalOperator_eq_gradientLift
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ upperHalfPlaneSet)
    (U : Set ℂ) (hU : IsOpen U) (hχU : EqOn χ (fun _ => 1) U)
    (K : Set ℂ) [CompactSpace K] (hKU : K ⊆ U)
    {κ : ℂ} (hκ : 0 < κ.re) (hp : κ ≠ (1 / 2 : ℂ)) (f : ModularHilbert)
    (hu : CuspSchur.actualSchurResolvent (parameter κ)
      (cuspWeightedInput (1 / 4) (by norm_num) f) ∈ laplacian.domain) :
    spatialOrbitPhysicalOperator χ hχ hc hsχ U hU hχU K hKU κ f =
      laplacianUpperCompactRestriction χ hχ hc hsχ U hU hχU K hKU
        (gradientLift laplacian
          ⟨CuspSchur.actualSchurResolvent (parameter κ)
            (cuspWeightedInput (1 / 4) (by norm_num) f), hu⟩) := by
  change laplacianUpperCompactRestriction χ hχ hc hsχ U hU hχU K hKU
    (actualSchurGraphResolvent κ (cuspWeightedInput (1 / 4) (by norm_num) f)) = _
  rw [actualSchurGraphResolvent_eq_gradientLift_physical hκ hp]
  rfl

/-- On the original convergence half-plane, applying the actual operator to
the actual shifted point input recovers every literal orbit-kernel value. -/
theorem spatialOrbitPhysicalOperator_spatialInput
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ upperHalfPlaneSet)
    (U : Set ℂ) (hU : IsOpen U) (hχU : EqOn χ (fun _ => 1) U)
    (K : Set ℂ) [CompactSpace K] (hKU : K ⊆ U)
    (s : ℂ) (hs : 1 < s.re) (w z : UpperHalfPlane) (hz : (z : ℂ) ∈ K) :
    spatialOrbitPhysicalOperator χ hχ hc hsχ U hU hχU K hKU (s - 1 / 2)
      (spatialOrbitThresholdInput s w) ⟨(z : ℂ), hz⟩ = spatialOrbitKernel s z w := by
  have hp : 0 < (s - (1 / 2 : ℂ)).re := by
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
    linarith
  have hh : s - (1 / 2 : ℂ) ≠ (1 / 2 : ℂ) := by
    intro he
    have he' : s = 1 := by linear_combination he
    rw [he'] at hs
    norm_num at hs
  obtain ⟨hdom, _⟩ := exists_spatialOrbitPoint_laplacian s hs w
  have hg : actualSchurGraphResolvent (s - 1 / 2)
      (cuspWeightedInput (1 / 4) (by norm_num) (spatialOrbitThresholdInput s w)) =
      gradientLift laplacian ⟨spatialOrbitPointSource s w, hdom⟩ := by
    rw [actualSchurGraphResolvent_eq_gradientLift_physical hp hh]
    apply congrArg (gradientLift laplacian)
    apply Subtype.ext
    change CuspSchur.actualSchurResolvent ((1 / 4 : ℂ) - (s - 1 / 2) ^ 2)
      (cuspWeightedInput (1 / 4) (by norm_num) (spatialOrbitThresholdInput s w)) = _
    rw [cuspWeightedInput_spatialOrbitThresholdInput s (by linarith),
      show (1 / 4 : ℂ) - (s - 1 / 2) ^ 2 = s * (1 - s) by ring]
    exact actualSchurResolvent_spatialOrbitPointSource s hs w
  change laplacianUpperCompactRestriction χ hχ hc hsχ U hU hχU K hKU
    (actualSchurGraphResolvent (s - 1 / 2)
      (cuspWeightedInput (1 / 4) (by norm_num) (spatialOrbitThresholdInput s w)))
      ⟨(z : ℂ), hz⟩ = _
  rw [hg]
  exact laplacianUpperCompactRestriction_spatialOrbitPointSource
    χ hχ hc hsχ U hU hχU K hKU s hs w hdom z hz

/-- A single actual operator-valued continuation, analytic on an open connected
region containing the threshold and the whole punctured physical half-plane.
Its threshold value is the canonical weighted evaluation for every input. -/
theorem exists_spatialOrbitContinuedOperator
    (K : Set ℂ) [CompactSpace K] (hKH : K ⊆ upperHalfPlaneSet) :
    ∃ (D : Evaluation (1 / 4) (by norm_num) K)
      (E : ℂ → ModularHilbert →L[ℂ] C(K, ℂ)) (r : ℝ),
      0 < r ∧ r ≤ 1 / 4 ∧ IsOpen (continuationRegion r) ∧
      IsPreconnected (continuationRegion r) ∧
      AnalyticOnNhd ℂ E (continuationRegion r) ∧
      (∀ κ, 0 < κ.re → κ ≠ (1 / 2 : ℂ) →
        E κ = spatialOrbitPhysicalOperator D.cutoff D.cutoff_smooth D.cutoff_compact
          D.cutoff_support D.region D.open_region D.one_region K D.compact_subset κ) ∧
      ∀ (f : ModularHilbert) (z : UpperHalfPlane) (hz : (z : ℂ) ∈ K),
        E 0 f ⟨(z : ℂ), hz⟩ = weightedThresholdValue (1 / 4) (by norm_num) f z := by
  classical
  obtain ⟨D⟩ := nonempty_evaluation K hKH (by norm_num : (0 : ℝ) < 1 / 4)
  let r : ℝ := min D.radius (1 / 4)
  have hr : 0 < r := lt_min D.radius_pos (by norm_num)
  have hrr : r ≤ D.radius := min_le_left _ _
  have hr4 : r ≤ 1 / 4 := min_le_right _ _
  let V : Set ℂ := {κ : ℂ | 0 < κ.re ∧ κ ≠ (1 / 2 : ℂ)}
  let A := spatialOrbitPhysicalOperator D.cutoff D.cutoff_smooth D.cutoff_compact
    D.cutoff_support D.region D.open_region D.one_region K D.compact_subset
  let E := analyticBallGlue r D.family A
  have hV : IsOpen V :=
    (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_ne
  have hDA : EqOn D.family A (Metric.ball 0 r ∩ V) := by
    intro κ hκ
    have hn : ‖κ‖ < D.radius :=
      (by simpa only [Metric.mem_ball, dist_zero_right] using hκ.1 : ‖κ‖ < r).trans_le hrr
    apply ContinuousLinearMap.ext
    intro f
    obtain ⟨hu, he⟩ := D.physical κ hn hκ.2.1 f
    exact he.trans (spatialOrbitPhysicalOperator_eq_gradientLift
      D.cutoff D.cutoff_smooth D.cutoff_compact D.cutoff_support
      D.region D.open_region D.one_region K D.compact_subset hκ.2.1 hκ.2.2 f hu).symm
  refine ⟨D, E, r, hr, hr4, isOpen_continuationRegion r,
    isPreconnected_continuationRegion hr, ?_, ?_, ?_⟩
  · exact analyticBallGlue_analyticOnNhd r hV
      (D.analytic_family.mono (Metric.ball_subset_ball hrr))
      (fun κ hκ => analyticAt_spatialOrbitPhysicalOperator
        D.cutoff D.cutoff_smooth D.cutoff_compact D.cutoff_support
        D.region D.open_region D.one_region K D.compact_subset hκ.1 hκ.2) hDA
  · intro κ hp hh
    exact analyticBallGlue_eqOn_of_eqOn r D.family A hDA ⟨hp, hh⟩
  · intro f z hz
    have he : E 0 = D.family 0 :=
      analyticBallGlue_eqOn_ball r D.family A (Metric.mem_ball_self hr)
    rw [he]
    exact (weightedThresholdValue_eq_evaluation (by norm_num : (0 : ℝ) < 1 / 4)
      D f z hz).symm

end GapFamily.Analytic.SpatialPoint
