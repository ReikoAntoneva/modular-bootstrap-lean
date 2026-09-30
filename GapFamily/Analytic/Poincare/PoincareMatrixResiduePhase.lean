import GapFamily.Analytic.Arithmetic.Kloosterman
import GapFamily.Analytic.Poincare.Poincare
import GapFamily.Analytic.Cusp.Fourier.CuspFourierProfileCore
import Mathlib.Data.ZMod.Units

/-! The actual determinant-one top row gives the inverse-residue Kloosterman phase. -/
noncomputable section
namespace GapFamily.Analytic.PoincareFourierArithmetic
open Complex
open scoped MatrixGroups

/-- The literal lower-right residue of a matrix with positive lower-left entry. -/
def matrixBottomUnit (γ : SL(2, ℤ)) (n : ℕ) (hc : γ 1 0 = (n + 1 : ℕ)) :
    (ZMod (n + 1))ˣ :=
  ZMod.unitOfIsCoprime (γ 1 1) (by
    have h := ModularGroup.bottom_row_coprime γ
    rw [hc] at h
    exact h.symm)

@[simp] theorem matrixBottomUnit_coe (γ : SL(2, ℤ)) (n : ℕ)
    (hc : γ 1 0 = (n + 1 : ℕ)) :
    (matrixBottomUnit γ n hc : ZMod (n + 1)) = (γ 1 1 : ZMod (n + 1)) := rfl

/-- The actual upper-left residue is the inverse of the lower-right unit. -/
theorem matrixBottomUnit_inverse (γ : SL(2, ℤ)) (n : ℕ)
    (hc : γ 1 0 = (n + 1 : ℕ)) :
    (γ 0 0 : ZMod (n + 1)) = ((matrixBottomUnit γ n hc)⁻¹ : (ZMod (n + 1))ˣ) := by
  have hd := γ.det_coe
  rw [Matrix.det_fin_two, hc] at hd
  have hdZ : (γ 0 0 : ZMod (n + 1)) * (γ 1 1 : ZMod (n + 1)) = 1 := by
    have h := congrArg (fun k : ℤ => (k : ZMod (n + 1))) hd
    simpa using h
  calc
    (γ 0 0 : ZMod (n + 1)) = (γ 0 0 : ZMod (n + 1)) *
        ((matrixBottomUnit γ n hc : ZMod (n + 1)) *
          (((matrixBottomUnit γ n hc)⁻¹ : (ZMod (n + 1))ˣ) : ZMod (n + 1))) := by
      rw [Units.mul_inv, mul_one]
    _ = ((matrixBottomUnit γ n hc)⁻¹ : (ZMod (n + 1))ˣ) := by
      rw [← mul_assoc, matrixBottomUnit_coe, hdZ, one_mul]

/-- The existing integer Fourier phase at a rational point is the standard additive character. -/
theorem cuspFourierMode_div_eq_stdAddChar (J a : ℤ) (c : ℕ) [NeZero c] :
    cuspFourierMode J ((a : ℝ) / (c : ℝ)) =
      ZMod.stdAddChar ((J : ZMod c) * (a : ZMod c)) := by
  have h := ZMod.stdAddChar_coe (N := c) (J * a)
  rw [Int.cast_mul] at h
  rw [h]
  unfold cuspFourierMode
  congr 1
  push_cast
  ring

/-- The arithmetic phase produced by the actual matrix is exactly the existing
Kloosterman phase, with output residue d and input inverse residue a. -/
theorem matrix_fourier_phase_eq_kloostermanPhase (j J : ℤ) (γ : SL(2, ℤ)) (n : ℕ)
    (hc : γ 1 0 = (n + 1 : ℕ)) :
    cuspFourierMode j ((γ 1 1 : ℝ) / (n + 1 : ℕ)) *
      cuspFourierMode J ((γ 0 0 : ℝ) / (n + 1 : ℕ)) =
        kloostermanPhase j J n (matrixBottomUnit γ n hc) := by
  rw [cuspFourierMode_div_eq_stdAddChar, cuspFourierMode_div_eq_stdAddChar]
  rw [← AddChar.map_add_eq_mul]
  simp only [kloostermanPhase, matrixBottomUnit_coe, ← matrixBottomUnit_inverse γ n hc]

end GapFamily.Analytic.PoincareFourierArithmetic
