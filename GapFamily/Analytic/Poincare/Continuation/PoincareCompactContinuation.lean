import GapFamily.Analytic.Poincare.PoincareResidualContinuation
import GapFamily.Analytic.Poincare.PoincareHighCuspComplexAnalytic

noncomputable section
namespace GapFamily.Analytic.PoincareCompactContinuation
open Set ModularGradient UpperHalfPlane CuspFourierCutoff
open PoincareResidualContinuation PoincareHighCuspAnalytic
open scoped ContDiff

/-- Every compact upper observation admits a genuine uniform-norm analytic
continuation of the original zero-energy spinning Poincaré series through the
threshold. A single disk and a quadratic spin bound work for every integer spin. -/
theorem exists_compactPoincareContinuation (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) :
    ∃ (P : ℤ → ℂ → C(K, ℂ)) (r C : ℝ),
      0 < r ∧ r ≤ 1 / 8 ∧ 0 < C ∧
      (∀ J : ℤ, AnalyticOnNhd ℂ (P J)
        (Metric.ball 0 r ∪ {κ : ℂ | 0 < κ.re ∧ κ ≠ (1 / 2 : ℂ)})) ∧
      (∀ (J : ℤ) (κ : ℂ), ‖κ‖ ≤ r → ‖P J κ‖ ≤ C * (1 + (J : ℝ) ^ 2)) ∧
      ∀ (J : ℤ) (κ : ℂ), (3 / 2 : ℝ) < κ.re → ∀ z : K,
        P J κ z = complexPoincareSeries 0 J (exponent κ) (ofComplex z) := by
  obtain ⟨L, U, χ, _hL, _hreg, hKL, hU, hLU, _hUc, _hUH, hχ, hc, hs, hχU⟩ :=
    exists_upperEvaluationCutoff (isCompact_iff_compactSpace.mpr inferInstance) hKH
  have hKU : K ⊆ U := hKL.trans (interior_subset.trans hLU)
  obtain ⟨G, r, C₁, hr, hr8, hC₁, hG, _hphysical, hbound, hcommon⟩ :=
    exists_continuedResidualResponse χ hχ hc hs U hU hχU K hKU
  obtain ⟨C₂, hC₂, hhigh⟩ := exists_highCuspComplexOn_norm_bound K hKH
  let P (J : ℤ) (κ : ℂ) : C(K, ℂ) := G J κ + highCuspComplexOn K hKH J κ
  refine ⟨P, r, C₁ + C₂, hr, hr8, by positivity, ?_, ?_, ?_⟩
  · intro J κ hκ
    exact (hG J κ hκ).add (analyticAt_highCuspComplexOn K hKH J κ)
  · intro J κ hn
    calc
      ‖P J κ‖ ≤ ‖G J κ‖ + ‖highCuspComplexOn K hKH J κ‖ := norm_add_le _ _
      _ ≤ C₁ * (1 + (J : ℝ) ^ 2) + C₂ :=
        add_le_add (hbound J κ hn) (hhigh J κ (hn.trans hr8))
      _ ≤ (C₁ + C₂) * (1 + (J : ℝ) ^ 2) := by
        nlinarith [mul_nonneg hC₂.le (sq_nonneg (J : ℝ))]
  · intro J κ hκ z
    change G J κ z + highCuspComplexOn K hKH J κ z = _
    rw [highCuspComplexOn_apply]
    exact hcommon J κ hκ z

end GapFamily.Analytic.PoincareCompactContinuation
