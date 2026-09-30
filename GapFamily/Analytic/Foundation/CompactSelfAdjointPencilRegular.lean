import GapFamily.Analytic.Foundation.CompactSelfAdjointPencilBasic

/-! # Regular parameters of the actual affine pencil -/

noncomputable section

namespace GapFamily.Analytic

open Filter
open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Away from minus one, regular pencil parameters correspond to the ordinary resolvent set. -/
theorem compactSelfAdjointPencil_isUnit_iff (R : H →L[ℂ] H) {z : ℂ} (hz : z ≠ -1) :
    IsUnit (compactSelfAdjointPencil R z) ↔ (z + 1)⁻¹ ∉ spectrum ℂ R := by
  have ha : z + 1 ≠ 0 := by simpa only [ne_eq, add_eq_zero_iff_eq_neg] using hz
  rw [spectrum.notMem_iff]
  have heq : (z + 1) • (algebraMap ℂ (H →L[ℂ] H) (z + 1)⁻¹ - R) =
      compactSelfAdjointPencil R z := by
    simp only [Algebra.algebraMap_eq_smul_one, smul_sub, smul_smul,
      mul_inv_cancel₀ ha, one_smul, compactSelfAdjointPencil]
  rw [← heq]
  exact isUnit_smul_iff (Units.mk0 (z + 1) ha) _

variable [CompleteSpace H]

/-- Actual regularity persists on a neighborhood of a regular parameter. -/
theorem compactSelfAdjointPencil_eventually_isUnit (R : H →L[ℂ] H) (z : ℂ)
    (hz : IsUnit (compactSelfAdjointPencil R z)) :
    ∀ᶠ w in 𝓝 z, IsUnit (compactSelfAdjointPencil R w) :=
  (compactSelfAdjointPencil_analyticAt R z).continuousAt
    (Units.isOpen.mem_nhds hz)

end GapFamily.Analytic
