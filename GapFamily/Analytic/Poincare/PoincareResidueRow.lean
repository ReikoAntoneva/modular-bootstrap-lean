import GapFamily.Analytic.Poincare.PoincareCoprimeResidue
import GapFamily.Analytic.Poincare.PoincarePrimitiveSpin
import GapFamily.Analytic.Poincare.PoincareMatrixResiduePhase

/-! Actual primitive rows indexed by a unit residue and an integer translate. -/

noncomputable section
namespace GapFamily.Analytic.PoincareFourierUnfold

open PoincareFourier PoincareFourierArithmetic
open scoped MatrixGroups

/-- The literal primitive lower row associated to the canonical residue and translate. -/
def residueRow (n : ℕ) (u : (ZMod (n + 1))ˣ) (k : ℤ) : PrimitiveRow :=
  ⟨![(n + 1 : ℕ), ((coprimeResidueEquiv (n + 1)).symm (u, k)).val], by
    apply (EisensteinSeries.mem_gammaSet_one _).mpr
    exact ((coprimeResidueEquiv (n + 1)).symm (u, k)).property⟩

@[simp] theorem residueRow_zero (n : ℕ) (u : (ZMod (n + 1))ˣ) (k : ℤ) :
    (residueRow n u k).val 0 = (n + 1 : ℕ) := rfl

@[simp] theorem residueRow_one (n : ℕ) (u : (ZMod (n + 1))ˣ) (k : ℤ) :
    (residueRow n u k).val 1 = ((u : ZMod (n + 1)).val : ℤ) + k * (n + 1 : ℕ) := rfl

@[simp] theorem primitiveMatrix_residueRow_bottomLeft
    (n : ℕ) (u : (ZMod (n + 1))ˣ) (k : ℤ) :
    primitiveMatrix (residueRow n u k) 1 0 = (n + 1 : ℕ) := by
  rw [primitiveMatrix_bottomRow]
  rfl

@[simp] theorem primitiveMatrix_residueRow_bottomRight
    (n : ℕ) (u : (ZMod (n + 1))ˣ) (k : ℤ) :
    primitiveMatrix (residueRow n u k) 1 1 =
      ((u : ZMod (n + 1)).val : ℤ) + k * (n + 1 : ℕ) := by
  rw [primitiveMatrix_bottomRow]
  rfl

/-- Every proof of the actual lower-left entry gives the prescribed lower-right unit. -/
@[simp] theorem matrixBottomUnit_residueRow
    (n : ℕ) (u : (ZMod (n + 1))ˣ) (k : ℤ)
    (hc : primitiveMatrix (residueRow n u k) 1 0 = (n + 1 : ℕ)) :
    matrixBottomUnit (primitiveMatrix (residueRow n u k)) n hc = u := by
  apply Units.ext
  simp

/-- The actual matrix phase equals the existing Kloosterman phase for this residue. -/
theorem residueRow_fourier_phase_eq_kloostermanPhase
    (j J : ℤ) (n : ℕ) (u : (ZMod (n + 1))ˣ) (k : ℤ) :
    cuspFourierMode j ((primitiveMatrix (residueRow n u k) 1 1 : ℝ) / (n + 1 : ℕ)) *
      cuspFourierMode J ((primitiveMatrix (residueRow n u k) 0 0 : ℝ) / (n + 1 : ℕ)) =
        kloostermanPhase j J n u := by
  rw [matrix_fourier_phase_eq_kloostermanPhase j J
    (primitiveMatrix (residueRow n u k)) n
    (primitiveMatrix_residueRow_bottomLeft n u k), matrixBottomUnit_residueRow]

/-- The actual lower-right rational shift is the canonical fractional residue plus k. -/
theorem primitiveMatrix_residueRow_bottomRight_div
    (n : ℕ) (u : (ZMod (n + 1))ˣ) (k : ℤ) :
    (primitiveMatrix (residueRow n u k) 1 1 : ℝ) / (n + 1 : ℕ) =
      ((u : ZMod (n + 1)).val : ℝ) / (n + 1 : ℕ) + (k : ℝ) := by
  have hc : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  simp only [primitiveMatrix_residueRow_bottomRight, Int.cast_add, Int.cast_mul,
    Int.cast_natCast]
  rw [add_div, mul_div_cancel_right₀ _ hc]

end GapFamily.Analytic.PoincareFourierUnfold
