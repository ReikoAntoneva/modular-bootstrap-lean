import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.Order

/-! Finite positive matrices from bounded positive operators and their
entrywise limits. This avoids a separate point-kernel Hermitian argument. -/

noncomputable section
namespace GapFamily.Analytic.PositiveOperatorGram
open Filter
open scoped ComplexOrder Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {ι : Type*} [Fintype ι]

theorem operatorGram_posSemidef (B : H →L[ℂ] H) (hB : B.IsPositive) (v : ι → H) :
    Matrix.PosSemidef (fun i j => inner ℂ (v i) (B (v j))) := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    change (starRingEnd ℂ) (inner ℂ (v j) (B (v i))) = inner ℂ (v i) (B (v j))
    rw [inner_conj_symm]
    exact hB.isSymmetric (v i) (v j)
  · intro c
    have he : star c ⬝ᵥ (Matrix.mulVec (fun i j => inner ℂ (v i) (B (v j))) c) =
        inner ℂ (∑ i, c i • v i) (B (∑ j, c j • v j)) := by
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum,
        map_sum, map_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right]
      conv_rhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      change star (c i) * (inner ℂ (v i) (B (v j)) * c j) =
        c j * (star (c i) * inner ℂ (v i) (B (v j)))
      ring
    rw [he]
    exact hB.inner_nonneg_right _

/-- A genuine pointwise matrix limit of positive matrices is positive. -/
theorem posSemidef_of_tendsto_entries {J : Type*} {l : Filter J} [l.NeBot]
    (A : J → Matrix ι ι ℂ) (M : Matrix ι ι ℂ)
    (hA : ∀ᶠ n in l, (A n).PosSemidef)
    (hlim : ∀ i j, Tendsto (fun n => A n i j) l (𝓝 (M i j))) : M.PosSemidef := by
  apply Matrix.posSemidef_is_closed.mem_of_tendsto _ hA
  exact tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => hlim i j

end GapFamily.Analytic.PositiveOperatorGram
