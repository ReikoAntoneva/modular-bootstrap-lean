import GapFamily.Analytic.Poincare.Continuation.PoincareContinuationPhysical
import GapFamily.Analytic.Poincare.Threshold.PoincareThresholdTest
import GapFamily.Analytic.Foundation.UpperWeightedSchurEvaluation

/-! Actual local weak-Poisson data for the canonical threshold residual. -/
noncomputable section
namespace GapFamily.Analytic.PoincareThresholdJet
open Set Filter MeasureTheory UpperHalfPlane ModularGradient Dirichlet CuspSchurLocal
  PoincareCanonical PoincareThresholdWeak PoincarePhysicalResponse
  PoincareHighCuspAnalytic PoincareHighCusp UpperWeightedJet
  UpperSource LocalPoisson
open scoped Topology ContDiff

/-- The canonical threshold seed minus the smooth high-cusp lift is the
continuous representative of an actually constructed local Poisson jet.
In particular, its first weak gradients exist in L²; no regularity premise
is imposed on the canonical threshold seed. -/
theorem exists_thresholdResidualJet
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet)
    (U : Set ℂ) (hU : IsOpen U) (hχU : EqOn χ (fun _ => 1) U) (J : ℤ) :
    ∃ j : JetSpace U, EqOn (fun z => thresholdSeed J (ofComplex z))
      (fun z => representative U hU j z + continuedHighCusp J 0 z) U := by
  obtain ⟨A, Q, r, hr, _hA, hQ, hcoordinates⟩ :=
    exists_analytic_continuedJet χ hχ hc hs U hU hχU (by norm_num : (0 : ℝ) < 1 / 4)
  let F : ℂ → ModularHilbert := cuspPoincareResidualSource J (1 / 4) (by norm_num)
  have hF : AnalyticAt ℂ F 0 := cuspPoincareResidualSource_analyticAt J (1 / 4)
    (by norm_num) (by norm_num)
  have hQ0 : AnalyticAt ℂ Q 0 := hQ 0 (Metric.mem_ball_self hr)
  have hUH : U ⊆ upperHalfPlaneSet := by
    intro z hz
    apply hs
    apply subset_tsupport χ
    rw [Function.mem_support, hχU hz]
    exact one_ne_zero
  refine ⟨Q 0 (F 0), ?_⟩
  intro z hz
  let K : Set ℂ := {z}
  let : CompactSpace K := isCompact_iff_compactSpace.mp isCompact_singleton
  have hKU : K ⊆ U := Set.singleton_subset_iff.mpr hz
  have hKH : K ⊆ upperHalfPlaneSet := hKU.trans hUH
  let D := chosenContinuation K hKH
  let R := restriction U hU K hKU
  let B : ℂ → C(K, ℂ) := fun κ => R (Q κ (F κ))
  let C : ℂ → C(K, ℂ) := fun κ => D.family J κ - highCuspComplexOn K hKH J κ
  have hB : AnalyticAt ℂ B 0 := by
    have happ := ((ContinuousLinearMap.apply ℂ (JetSpace U)).analyticAt_bilinear
      (F 0, Q 0)).comp_of_eq (hF.prod hQ0) rfl
    exact (R.analyticAt _).comp happ
  have hD0 : AnalyticAt ℂ (D.family J) 0 :=
    D.analytic_family J 0 (Or.inl (Metric.mem_ball_self D.radius_pos))
  have hC : AnalyticAt ℂ C 0 := hD0.sub (analyticAt_highCuspComplexOn K hKH J 0)
  have heq : C =ᶠ[𝓝 (0 : ℂ)] B := by
    apply CuspSchurCoherence.analyticAt_eventuallyEq_of_physical hC hB
    refine ⟨min r (1 / 8), lt_min hr (by norm_num), ?_⟩
    intro κ hn hp
    have hnr : ‖κ‖ < r := hn.trans_le (min_le_left _ _)
    have hn8 : ‖κ‖ < (1 / 8 : ℝ) := hn.trans_le (min_le_right _ _)
    have hh : κ ≠ (1 / 2 : ℂ) := by
      intro he
      rw [he] at hn8
      norm_num at hn8
    change D.family J κ - highCuspComplexOn K hKH J κ = R (Q κ (F κ))
    rw [continuation_sub_highCusp_eq_physical D hKH χ hχ hc hs U hU hχU hKU J hp hh]
    obtain ⟨hsub, hphysical⟩ := hcoordinates κ hnr
    have hphys := hphysical hp (F κ)
    have hw : cuspWeightedInput (1 / 4) (by norm_num) (F κ) =
        cuspPoincareResidualSource J 0 (by norm_num) κ :=
      cuspWeightedInput_poincareResidualSource J (1 / 4) (by norm_num) (by linarith)
    rw [hw] at hphys
    obtain ⟨hu, hj⟩ := hphys
    let u : laplacian.domain :=
      ⟨CuspSchur.actualSchurResolvent (parameter κ)
        (cuspPoincareResidualSource J 0 (by norm_num) κ), hu⟩
    have hq : Q κ (F κ) =
        ⟨actualJet χ hχ hc hs u, actualJet_mem χ hχ hc hs U hU hχU u⟩ := by
      apply Subtype.ext
      have he := congrArg (fun T : ModularHilbert →L[ℂ] Jet => T (F κ)) hsub
      exact he.trans hj
    rw [physicalResidualResponse_eq_gradientLift χ hχ hc hs U hU hχU K hKU J hp hh hu]
    symm
    rw [hq]
    exact actualJet_restriction χ hχ hc hs U hU hχU K hKU u
  have he0 := congrArg (fun a : C(K, ℂ) => a ⟨z, Set.mem_singleton z⟩) heq.self_of_nhds
  change D.family J 0 ⟨z, Set.mem_singleton z⟩ - continuedHighCusp J 0 z =
    representative U hU (Q 0 (F 0)) z at he0
  rw [thresholdSeed_ofComplex_eq_continuation hKH D J ⟨z, Set.mem_singleton z⟩] at he0
  exact sub_eq_iff_eq_add.mp he0

end GapFamily.Analytic.PoincareThresholdJet
