import GapFamily.Analytic.Cusp.Schur.CuspSchurPhysicalGraphAnalytic
import GapFamily.Analytic.Foundation.UpperWeightedSchurEvaluation
import GapFamily.Analytic.Cusp.CuspResidualSpinBound
import GapFamily.Analytic.Cusp.CuspPoincareResidualWeightedInput

/-!
Actual compact-chart residual response on the physical half-plane and its
threshold analytic germ. The graph response, source, and spatial restriction
are the already constructed operators. One threshold disk works for every spin.
-/

noncomputable section
namespace GapFamily.Analytic.PoincarePhysicalResponse
open Set MeasureTheory ModularGradient UpperHalfPlane CuspSchurLocal Dirichlet
open CuspSchurPhysicalGraphAnalytic UpperWeightedJet
open scoped ContDiff

/-- The actual physical residual response in the genuine compact-chart sup norm. -/
def physicalResidualResponse
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet)
    (U : Set ℂ) (hU : IsOpen U) (hχU : EqOn χ (fun _ => 1) U)
    (K : Set ℂ) [CompactSpace K] (hKU : K ⊆ U) (J : ℤ) (κ : ℂ) : C(K, ℂ) :=
  laplacianUpperCompactRestriction χ hχ hc hs U hU hχU K hKU
    (actualSchurGraphResolvent κ (cuspPoincareResidualSource J 0 (by norm_num) κ))

/-- Norm analyticity on every physical parameter except the constant pole. -/
theorem physicalResidualResponse_analyticAt
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet)
    (U : Set ℂ) (hU : IsOpen U) (hχU : EqOn χ (fun _ => 1) U)
    (K : Set ℂ) [CompactSpace K] (hKU : K ⊆ U) (J : ℤ)
    {κ : ℂ} (hκ : 0 < κ.re) (hp : κ ≠ (1 / 2 : ℂ)) :
    AnalyticAt ℂ (physicalResidualResponse χ hχ hc hs U hU hχU K hKU J) κ := by
  have hF : AnalyticAt ℂ (cuspPoincareResidualSource J 0 (by norm_num)) κ :=
    cuspPoincareResidualSource_analyticAt J 0 (by norm_num) (by linarith)
  have hG := actualSchurGraphResolvent_analyticAt_physical hκ hp
  have happly := ((ContinuousLinearMap.apply ℂ LaplacianGraphDomain).analyticAt_bilinear
    (cuspPoincareResidualSource J 0 (by norm_num) κ, actualSchurGraphResolvent κ)).comp_of_eq
      (hF.prod hG) rfl
  exact ((laplacianUpperCompactRestriction χ hχ hc hs U hU hχU K hKU).analyticAt _).comp_of_eq
    happly rfl

theorem physicalResidualResponse_analyticOnNhd
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet)
    (U : Set ℂ) (hU : IsOpen U) (hχU : EqOn χ (fun _ => 1) U)
    (K : Set ℂ) [CompactSpace K] (hKU : K ⊆ U) (J : ℤ) :
    AnalyticOnNhd ℂ (physicalResidualResponse χ hχ hc hs U hU hχU K hKU J)
      {κ : ℂ | 0 < κ.re ∧ κ ≠ (1 / 2 : ℂ)} :=
  fun _ hκ => physicalResidualResponse_analyticAt χ hχ hc hs U hU hχU K hKU J hκ.1 hκ.2

/-- At a physical parameter the graph package is the actual domain lift,
independent of the proof chosen for domain membership. -/
theorem physicalResidualResponse_eq_gradientLift
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet)
    (U : Set ℂ) (hU : IsOpen U) (hχU : EqOn χ (fun _ => 1) U)
    (K : Set ℂ) [CompactSpace K] (hKU : K ⊆ U) (J : ℤ)
    {κ : ℂ} (hκ : 0 < κ.re) (hp : κ ≠ (1 / 2 : ℂ))
    (hu : CuspSchur.actualSchurResolvent (parameter κ)
      (cuspPoincareResidualSource J 0 (by norm_num) κ) ∈ laplacian.domain) :
    physicalResidualResponse χ hχ hc hs U hU hχU K hKU J κ =
      laplacianUpperCompactRestriction χ hχ hc hs U hU hχU K hKU
        (gradientLift laplacian
          ⟨CuspSchur.actualSchurResolvent (parameter κ)
            (cuspPoincareResidualSource J 0 (by norm_num) κ), hu⟩) := by
  unfold physicalResidualResponse
  rw [actualSchurGraphResolvent_eq_gradientLift_physical hκ hp]
  rfl

/-- A single threshold disk, fixed before the spin, carries the actual physical
residual response germ on the given upper chart and a quadratic spin bound. -/
theorem exists_thresholdResidualResponse
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet)
    (U : Set ℂ) (hU : IsOpen U) (hχU : EqOn χ (fun _ => 1) U)
    (K : Set ℂ) [CompactSpace K] (hKU : K ⊆ U) :
    ∃ (R : ℤ → ℂ → C(K, ℂ)) (r C : ℝ),
      0 < r ∧ r ≤ 1 / 8 ∧ 0 < C ∧
      (∀ J : ℤ, AnalyticOnNhd ℂ (R J) (Metric.ball 0 r)) ∧
      (∀ (J : ℤ) (κ : ℂ), ‖κ‖ ≤ r → ‖R J κ‖ ≤ C * (1 + (J : ℝ) ^ 2)) ∧
      ∀ (J : ℤ) (κ : ℂ), ‖κ‖ < r → 0 < κ.re →
        R J κ = physicalResidualResponse χ hχ hc hs U hU hχU K hKU J κ := by
  obtain ⟨E, ε, hε, hE, hphysical⟩ :=
    exists_analytic_upperSchurEvaluation_on_plateau χ hχ hc hs U hU hχU K hKU
      (by norm_num : (0 : ℝ) < 1 / 4)
  let r : ℝ := min (ε / 2) (1 / 8)
  have hr : 0 < r := lt_min (by positivity) (by norm_num)
  have hr8 : r ≤ 1 / 8 := min_le_right _ _
  have hre : r < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hEcontinuous : ContinuousOn E (Metric.closedBall 0 r) := by
    intro κ hκ
    have hn : ‖κ‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_zero_right] using hκ
    exact (hE κ (by simpa only [Metric.mem_ball, dist_zero_right] using (hn.trans_lt hre))).continuousAt.continuousWithinAt
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) r).exists_bound_of_continuousOn hEcontinuous
  obtain ⟨A, hA, hFbound⟩ := cuspPoincareResidualSource_quarter_uniform_spin_bound
  let F (J : ℤ) : ℂ → ModularHilbert := cuspPoincareResidualSource J (1 / 4) (by norm_num)
  let R (J : ℤ) (κ : ℂ) : C(K, ℂ) := E κ (F J κ)
  have hFanalytic (J : ℤ) {κ : ℂ} (hn : ‖κ‖ ≤ r) : AnalyticAt ℂ (F J) κ := by
    apply cuspPoincareResidualSource_analyticAt
    have hl := (abs_le.mp ((Complex.abs_re_le_norm κ).trans (hn.trans hr8))).1
    linarith
  refine ⟨R, r, (|B| + 1) * A, hr, hr8, by positivity, ?_, ?_, ?_⟩
  · intro J κ hκ
    have hn : ‖κ‖ < r := by simpa only [Metric.mem_ball, dist_zero_right] using hκ
    have hEk := hE κ (by simpa only [Metric.mem_ball, dist_zero_right] using hn.trans hre)
    exact ((ContinuousLinearMap.apply ℂ C(K, ℂ)).analyticAt_bilinear
      (F J κ, E κ)).comp_of_eq ((hFanalytic J hn.le).prod hEk) rfl
  · intro J κ hn
    have hEn : ‖E κ‖ ≤ |B| + 1 :=
      (hB κ (by simpa only [Metric.mem_closedBall, dist_zero_right] using hn)).trans
        (by linarith [le_abs_self B])
    calc
      ‖R J κ‖ ≤ ‖E κ‖ * ‖F J κ‖ := (E κ).le_opNorm _
      _ ≤ (|B| + 1) * (A * (1 + (J : ℝ) ^ 2)) :=
        mul_le_mul hEn (hFbound J κ (hn.trans hr8)) (norm_nonneg _) (by positivity)
      _ = ((|B| + 1) * A) * (1 + (J : ℝ) ^ 2) := by ring
  · intro J κ hn hp
    have he := hphysical κ (hn.trans hre) hp (F J κ)
    have hw : cuspWeightedInput (1 / 4) (by norm_num) (F J κ) =
        cuspPoincareResidualSource J 0 (by norm_num) κ :=
      cuspWeightedInput_poincareResidualSource J (1 / 4) (by norm_num) (by linarith)
    rw [hw] at he
    obtain ⟨hu, hEval⟩ := he
    have hhalf : κ ≠ (1 / 2 : ℂ) := by
      intro h
      have hn' := hn.trans_le hr8
      rw [h] at hn'
      norm_num at hn'
    exact hEval.trans
      (physicalResidualResponse_eq_gradientLift χ hχ hc hs U hU hχU K hKU J hp hhalf hu).symm

end GapFamily.Analytic.PoincarePhysicalResponse
