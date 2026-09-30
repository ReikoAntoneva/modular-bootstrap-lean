import GapFamily.Analytic.Modular.ModularBoundary

noncomputable section

namespace GapFamily.Analytic

open Set
open scoped MatrixGroups Classical

/-- The full matrix group has precisely its central pair over an interior tile. -/
theorem modularAction_mem_fd_iff_eq_or_eq_neg
    {τ : UpperHalfPlane} {γ₀ γ : SL(2, ℤ)}
    (hγ₀ : γ₀ • τ ∈ ModularGroup.fdo) :
    γ • τ ∈ ModularGroup.fd ↔ γ = γ₀ ∨ γ = -γ₀ := by
  constructor
  · intro hγ
    have hmem : (γ * γ₀⁻¹) • (γ₀ • τ) ∈ ModularGroup.fd := by
      simpa only [mul_smul, inv_smul_smul] using hγ
    rcases ModularGroup.eq_one_or_neg_one_of_mem_fdo_mem_fd hγ₀ hmem with h | h
    · left
      have heq := congrArg (fun δ : SL(2, ℤ) => δ * γ₀) h
      simpa only [mul_assoc, inv_mul_cancel, mul_one, one_mul] using heq
    · right
      have heq := congrArg (fun δ : SL(2, ℤ) => δ * γ₀) h
      simpa only [mul_assoc, inv_mul_cancel, mul_one, neg_mul, one_mul] using heq
  · rintro (rfl | rfl)
    · exact ModularGroup.fdo_subset_fd hγ₀
    · simpa only [ModularGroup.SL_neg_smul] using ModularGroup.fdo_subset_fd hγ₀

/-- The actual `SL(2, ℤ)` tile fibre is the two central translates. -/
theorem modularAction_fd_fiber_eq_pair
    {τ : UpperHalfPlane} {γ₀ : SL(2, ℤ)}
    (hγ₀ : γ₀ • τ ∈ ModularGroup.fdo) :
    {γ : SL(2, ℤ) | γ • τ ∈ ModularGroup.fd} = {γ₀, -γ₀} := by
  ext γ
  exact (modularAction_mem_fd_iff_eq_or_eq_neg hγ₀).trans (by simp)

/-- A determinant-one integral matrix is distinct from its negative. -/
theorem modularMatrix_ne_neg (γ : SL(2, ℤ)) : γ ≠ -γ := by
  intro h
  have hi : (1 : SL(2, ℤ)) = -1 := by
    simpa only [mul_inv_cancel, neg_mul] using
      congrArg (fun δ : SL(2, ℤ) => δ * γ⁻¹) h
  have hentry := congrArg (fun δ : SL(2, ℤ) => δ 0 0) hi
  norm_num at hentry

/-- The full matrix-group count of a tile is exactly two away from the seams. -/
theorem modularAction_fd_indicator_tsum_eq_two
    {τ : UpperHalfPlane} {γ₀ : SL(2, ℤ)}
    (hγ₀ : γ₀ • τ ∈ ModularGroup.fdo) :
    (∑' γ : SL(2, ℤ), if γ • τ ∈ ModularGroup.fd then (1 : ENNReal) else 0) = 2 := by
  classical
  rw [tsum_eq_sum (s := {γ₀, -γ₀})]
  · rw [Finset.sum_pair (modularMatrix_ne_neg γ₀)]
    simp only [ModularGroup.fdo_subset_fd hγ₀, ModularGroup.SL_neg_smul, ite_true]
    norm_num
  · intro γ hγ
    have hnot : γ • τ ∉ ModularGroup.fd := by
      intro hmem
      apply hγ
      simpa only [Finset.mem_insert, Finset.mem_singleton] using
        (modularAction_mem_fd_iff_eq_or_eq_neg hγ₀).mp hmem
    simp only [hnot, ite_false]

end GapFamily.Analytic
