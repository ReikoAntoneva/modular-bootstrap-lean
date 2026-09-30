import GapFamily.Analytic.Poincare.PoincareHighCuspTermAnalytic
import GapFamily.Analytic.Poincare.PoincareHighCuspFinite

/-! Entire parameter dependence in the uniform norm on actual compact targets. -/
noncomputable section
namespace GapFamily.Analytic.PoincareHighCuspAnalytic
open Set UpperHalfPlane CuspFourierCutoff PoincareHighCusp
open scoped Topology MatrixGroups

/-- Proper discontinuity gives one literal finite C(K)-valued sum for all
parameters and all spins. The existing normalized periodization is preserved. -/
theorem continuedHighCuspOn_eq_finite (K : Set UpperHalfPlane) [CompactSpace K] :
    ∃ Γ : Finset SL(2, ℤ), ∀ (J : ℤ) (κ : ℂ),
      continuedHighCuspOn K J κ =
        (1 / 2 : ℂ) • ∑ γ ∈ Γ, orbitTerm K J γ (exponent κ) := by
  obtain ⟨Γ, hΓ⟩ := exists_finset_highCuspLift_eq_on_compact
    (isCompact_iff_compactSpace.mpr inferInstance : IsCompact K)
  refine ⟨Γ, fun J κ => ?_⟩
  ext τ
  simpa only [continuedHighCuspOn_apply, continuedHighCusp,
    ContinuousMap.smul_apply, smul_eq_mul, ContinuousMap.sum_apply, orbitTerm_apply] using
      hΓ J (exponent κ) τ.val τ.property

/-- The actual global high-cusp lift is entire in C(K), with its uniform norm.
This is a finite-sum theorem on each compact K, not a pointwise criterion. -/
theorem differentiable_continuedHighCuspOn (K : Set UpperHalfPlane) [CompactSpace K]
    (J : ℤ) : Differentiable ℂ (continuedHighCuspOn K J) := by
  obtain ⟨Γ, hΓ⟩ := continuedHighCuspOn_eq_finite K
  have heq : continuedHighCuspOn K J =
      fun κ => (1 / 2 : ℂ) • ∑ γ ∈ Γ, orbitTerm K J γ (exponent κ) := by
    funext κ
    exact hΓ J κ
  rw [heq]
  have hexp : Differentiable ℂ exponent := by
    unfold exponent
    fun_prop
  exact (Differentiable.fun_sum fun γ hγ =>
    (differentiable_orbitTerm K J γ).comp hexp).const_smul (1 / 2 : ℂ)

/-- Norm analyticity holds at every complex parameter, including the threshold. -/
theorem analyticAt_continuedHighCuspOn (K : Set UpperHalfPlane) [CompactSpace K]
    (J : ℤ) (κ : ℂ) : AnalyticAt ℂ (continuedHighCuspOn K J) κ :=
  (differentiable_continuedHighCuspOn K J).analyticAt κ

end GapFamily.Analytic.PoincareHighCuspAnalytic
