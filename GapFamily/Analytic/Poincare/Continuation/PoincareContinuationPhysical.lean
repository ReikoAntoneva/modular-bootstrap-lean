import GapFamily.Analytic.Poincare.Continuation.PoincareCompactCoherence

/-! Every actual compact continuation has the same residual on the entire physical region. -/
noncomputable section
namespace GapFamily.Analytic.PoincareThresholdJet
open Set Filter UpperHalfPlane ModularGradient CuspFourierCutoff
open PoincareCanonical PoincarePhysicalResponse
open PoincareResidualContinuation PoincareHighCuspAnalytic
open scoped ContDiff Topology

/-- The physical residual is fixed by the literal original-series identity on
its common half-plane and analytic uniqueness on the full punctured physical region. -/
theorem continuation_sub_highCusp_eq_physical {K : Set ℂ} [CompactSpace K]
    (D : Continuation K) (hKH : K ⊆ upperHalfPlaneSet)
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet)
    (U : Set ℂ) (hU : IsOpen U) (hχU : EqOn χ (fun _ => 1) U)
    (hKU : K ⊆ U) (J : ℤ) {κ : ℂ}
    (hp : 0 < κ.re) (hh : κ ≠ (1 / 2 : ℂ)) :
    D.family J κ - highCuspComplexOn K hKH J κ =
      physicalResidualResponse χ hχ hc hs U hU hχU K hKU J κ := by
  let V : Set ℂ := {ξ : ℂ | 0 < ξ.re ∧ ξ ≠ (1 / 2 : ℂ)}
  let f : ℂ → C(K, ℂ) := fun ξ => D.family J ξ - highCuspComplexOn K hKH J ξ
  let g : ℂ → C(K, ℂ) := physicalResidualResponse χ hχ hc hs U hU hχU K hKU J
  have hf : AnalyticOnNhd ℂ f V := by
    intro ξ hξ
    exact (D.analytic_family J ξ (Or.inr hξ)).sub
      (analyticAt_highCuspComplexOn K hKH J ξ)
  have hg : AnalyticOnNhd ℂ g V :=
    physicalResidualResponse_analyticOnNhd χ hχ hc hs U hU hχU K hKU J
  have htwo : (2 : ℂ) ∈ V := by norm_num [V]
  have hnear : f =ᶠ[𝓝 (2 : ℂ)] g := by
    have ho : IsOpen {ξ : ℂ | (3 / 2 : ℝ) < ξ.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    have ht : (2 : ℂ) ∈ {ξ : ℂ | (3 / 2 : ℝ) < ξ.re} := by norm_num
    filter_upwards [ho.mem_nhds ht] with ξ hξ
    apply ContinuousMap.ext
    intro z
    change D.family J ξ z - highCuspComplexOn K hKH J ξ z =
      physicalResidualResponse χ hχ hc hs U hU hχU K hKU J ξ z
    rw [highCuspComplexOn_apply, D.common_region J ξ hξ z]
    exact sub_eq_iff_eq_add.mpr
      (physicalResidualResponse_add_highCusp_eq_series χ hχ hc hs U hU hχU K hKU J hξ z).symm
  have heq : EqOn f g V := hf.eqOn_of_preconnected_of_eventuallyEq hg
    isPreconnected_puncturedRightHalfPlane htwo hnear
  exact heq ⟨hp, hh⟩

end GapFamily.Analytic.PoincareThresholdJet
