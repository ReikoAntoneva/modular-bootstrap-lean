import Mathlib.NumberTheory.Modular
import Mathlib.Data.Finset.Card

/-! A fixed three-tile cover of the high cusp, with the source height retained.
The closed fundamental domain includes both vertical boundary seams. -/

noncomputable section
namespace GapFamily.Analytic.CuspThreeTileCover

open Set UpperHalfPlane ModularGroup
open scoped MatrixGroups Pointwise

/-- Exactly the three integer-translation tiles required by the width-two strip. -/
def cuspThreeTiles : Finset SL(2, ℤ) := {T ^ (-1 : ℤ), 1, T}

theorem cuspThreeTiles_card_le : cuspThreeTiles.card ≤ 3 := by
  classical
  exact Finset.card_le_three

private theorem mem_fd_of_high {τ : UpperHalfPlane} (hy : 1 ≤ τ.im)
    (hx : |τ.re| ≤ (1 / 2 : ℝ)) : τ ∈ ModularGroup.fd := by
  refine ⟨?_, hx⟩
  rw [Complex.normSq_apply]
  change 1 ≤ τ.re * τ.re + τ.im * τ.im
  nlinarith [sq_nonneg τ.re]

/-- All points of the high width-two strip lie in these three translated
high-cusp pieces of the actual closed fundamental domain. -/
theorem cuspThreeTiles_cover (H : ℝ) (hH : 1 ≤ H) :
    {τ : UpperHalfPlane | |τ.re| ≤ 1 ∧ H < τ.im} ⊆
      ⋃ γ ∈ cuspThreeTiles, γ • {τ : UpperHalfPlane | τ ∈ ModularGroup.fd ∧ H < τ.im} := by
  intro τ hτ
  have hreal := abs_le.mp hτ.1
  by_cases hxlo : τ.re < -(1 / 2 : ℝ)
  · have hbase : T • τ ∈ {σ : UpperHalfPlane | σ ∈ ModularGroup.fd ∧ H < σ.im} := by
      refine ⟨mem_fd_of_high ?_ ?_, ?_⟩
      · rw [im_T_smul]; exact hH.trans hτ.2.le
      · rw [re_T_smul, abs_le]
        constructor <;> linarith
      · simpa only [im_T_smul] using hτ.2
    refine mem_iUnion.mpr ⟨T ^ (-1 : ℤ), mem_iUnion.mpr ⟨by simp [cuspThreeTiles], ?_⟩⟩
    change τ ∈ (fun σ : UpperHalfPlane => T ^ (-1 : ℤ) • σ) '' _
    exact ⟨T • τ, hbase, by simp⟩
  · by_cases hxhi : (1 / 2 : ℝ) < τ.re
    · have hbase : T⁻¹ • τ ∈ {σ : UpperHalfPlane | σ ∈ ModularGroup.fd ∧ H < σ.im} := by
        refine ⟨mem_fd_of_high ?_ ?_, ?_⟩
        · rw [im_T_inv_smul]; exact hH.trans hτ.2.le
        · rw [re_T_inv_smul, abs_le]
          constructor <;> linarith
        · simpa only [im_T_inv_smul] using hτ.2
      refine mem_iUnion.mpr ⟨T, mem_iUnion.mpr ⟨by simp [cuspThreeTiles], ?_⟩⟩
      change τ ∈ (fun σ : UpperHalfPlane => T • σ) '' _
      exact ⟨T⁻¹ • τ, hbase, by simp⟩
    · have hbase : τ ∈ {σ : UpperHalfPlane | σ ∈ ModularGroup.fd ∧ H < σ.im} := by
        refine ⟨mem_fd_of_high (hH.trans hτ.2.le) ?_, hτ.2⟩
        exact abs_le.mpr ⟨le_of_not_gt hxlo, le_of_not_gt hxhi⟩
      refine mem_iUnion.mpr ⟨1, mem_iUnion.mpr ⟨by simp [cuspThreeTiles], ?_⟩⟩
      simpa only [one_smul] using hbase

/-- Forgetting only the source-height restriction gives the same uniform
three-tile cover by full closed fundamental domains. -/
theorem cuspThreeTiles_cover_fd (H : ℝ) (hH : 1 ≤ H) :
    {τ : UpperHalfPlane | |τ.re| ≤ 1 ∧ H < τ.im} ⊆
      ⋃ γ ∈ cuspThreeTiles, γ • ModularGroup.fd := by
  apply (cuspThreeTiles_cover H hH).trans
  apply Set.iUnion_mono
  intro γ
  apply Set.iUnion_mono
  intro hγ
  exact Set.image_mono (fun _ hτ => hτ.1)

end GapFamily.Analytic.CuspThreeTileCover
