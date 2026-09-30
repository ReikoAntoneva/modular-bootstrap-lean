import Mathlib.Analysis.Matrix.Order

/-! Positivity on arbitrary index sets from actual finite Gram matrices. -/
noncomputable section
universe u
namespace GapFamily.Analytic.FiniteKernelPosSemidef
open scoped ComplexOrder

/-- Every finitely supported quadratic form is contained in a finite Gram
matrix. No countability or topology on the point space is needed. -/
theorem posSemidef_of_finite_gram {X : Type u} (K : X → X → ℂ)
    (hK : ∀ {ι : Type u} [Fintype ι] (p : ι → X),
      Matrix.PosSemidef (fun i j => K (p i) (p j))) :
    Matrix.PosSemidef (K : Matrix X X ℂ) := by
  classical
  refine ⟨Matrix.IsHermitian.ext ?_, ?_⟩
  · intro x y
    let S : Finset X := {x, y}
    have hS := hK (fun i : S => (i : X))
    exact hS.isHermitian.apply ⟨x, by simp [S]⟩ ⟨y, by simp [S]⟩
  · intro c
    have hS := hK (fun i : c.support => (i : X))
    have hc := hS.dotProduct_mulVec_nonneg (fun i : c.support => c i)
    change 0 ≤ ∑ i ∈ c.support, ∑ j ∈ c.support, star (c i) * K i j * c j
    simp_rw [← Finset.sum_coe_sort c.support]
    simpa only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, mul_assoc] using hc

/-- Finite indexed Gram positivity is equivalent to the unrestricted matrix
predicate, whose quadratic tests are finitely supported vectors. -/
theorem posSemidef_iff_finite_gram {X : Type u} (K : X → X → ℂ) :
    Matrix.PosSemidef (K : Matrix X X ℂ) ↔
      ∀ {ι : Type u} [Fintype ι] (p : ι → X),
        Matrix.PosSemidef (fun i j => K (p i) (p j)) := by
  refine ⟨?_, posSemidef_of_finite_gram K⟩
  intro hK ι _ p
  exact hK.submatrix p

end GapFamily.Analytic.FiniteKernelPosSemidef
