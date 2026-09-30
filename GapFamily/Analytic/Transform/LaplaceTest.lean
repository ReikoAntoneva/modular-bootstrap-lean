import GapFamily.Analytic.Foundation.ScalarNormalization
import GapFamily.Analytic.Poincare.Poincare
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Finite Laplace tests

The two adjacent positive heights give the actual regularized energy test,
kill a scalar threshold atom, and turn the spatial constant six into the
rank-one coefficient twelve. Finite tests preserve positive semidefiniteness.
The continued spatial kernel and its Fourier–Laplace identity are separate
analytic obligations; neither is assumed to exist in this module.
-/

namespace GapFamily.Analytic

open Real Set MeasureTheory
open scoped BigOperators ComplexOrder

noncomputable def horizontalPhase (j : ℤ) (x : ℝ) : ℂ :=
  Complex.exp ((j : ℂ) * (2 * π * Complex.I) * x)

theorem integral_horizontalPhase (j : ℤ) :
    (∫ x : ℝ in 0..1, horizontalPhase j x) = if j = 0 then 1 else 0 := by
  by_cases hj : j = 0
  · simp [hj, horizontalPhase]
  · have hc : (j : ℂ) * (2 * π * Complex.I) ≠ 0 := by
      exact mul_ne_zero (by exact_mod_cast hj)
        (mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
          Complex.I_ne_zero)
    simp [horizontalPhase, integral_exp_mul_complex hc,
      Complex.exp_int_mul_two_pi_mul_I, hj]

theorem horizontalPhase_neg_mul (j J : ℤ) (x : ℝ) :
    horizontalPhase (-j) x * horizontalPhase J x = horizontalPhase (J - j) x := by
  simp only [horizontalPhase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem horizontal_fourier_orthogonality (j J : ℤ) :
    (∫ x : ℝ in 0..1, horizontalPhase (-j) x * horizontalPhase J x) =
      if J = j then 1 else 0 := by
  simp_rw [horizontalPhase_neg_mul]
  rw [integral_horizontalPhase]
  simp only [sub_eq_zero]

noncomputable def laplaceHeight (k : ℕ) : ℝ := ((k : ℝ) + 1) / (2 * π)

theorem laplaceHeight_pos (k : ℕ) : 0 < laplaceHeight k := by
  unfold laplaceHeight
  positivity

noncomputable def laplacePoint (k : ℕ) (x : ℝ) : UpperHalfPlane :=
  ⟨⟨x, laplaceHeight k⟩, laplaceHeight_pos k⟩

theorem normalized_pointSeed_at_laplacePoint (E : ℝ) (J : ℤ) (k : ℕ) (x : ℝ) :
    pointSeed E J (1 / 2) (laplacePoint k x) / (Real.sqrt (laplaceHeight k) : ℂ) =
      (Real.exp (-2 * π * laplaceHeight k * E) : ℂ) * horizontalPhase J x := by
  have hn : (Real.sqrt (laplaceHeight k) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.2 (laplaceHeight_pos k))
  simp only [pointSeed, laplacePoint, UpperHalfPlane.im, UpperHalfPlane.re]
  rw [← Real.sqrt_eq_rpow, Complex.exp_add]
  have hr : ((-2 * π * E * laplaceHeight k : ℝ) : ℂ) =
      ((-2 * π * laplaceHeight k * E : ℝ) : ℂ) := by congr 1; ring
  rw [hr, ← Complex.ofReal_exp]
  have hp : ((2 * π * (J : ℝ) * x : ℝ) : ℂ) * Complex.I =
      (J : ℂ) * (2 * π * Complex.I) * x := by push_cast; ring
  rw [hp]
  unfold horizontalPhase
  field_simp

noncomputable def laplaceTest (k : ℕ) (E : ℝ) : ℝ :=
  Real.exp (-((k : ℝ) + 1) * E) * (1 - Real.exp (-E))

theorem laplaceTest_eq_height_difference (k : ℕ) (E : ℝ) :
    laplaceTest k E = Real.exp (-2 * π * laplaceHeight k * E) -
      Real.exp (-2 * π * laplaceHeight (k + 1) * E) := by
  have h (n : ℕ) : -2 * π * laplaceHeight n * E = -((n : ℝ) + 1) * E := by
    unfold laplaceHeight
    field_simp
  rw [h, h]
  unfold laplaceTest
  rw [mul_sub, mul_one, ← Real.exp_add]
  congr 2
  push_cast
  ring

/-- The Fourier projection and the adjacent normalized point-seed evaluations
produce exactly the direct energy test in the requested spin row. -/
theorem pointSeed_fourier_height_difference (E : ℝ) (j J : ℤ) (k : ℕ) :
    (∫ x : ℝ in 0..1, horizontalPhase (-j) x *
      (pointSeed E J (1 / 2) (laplacePoint k x) / (Real.sqrt (laplaceHeight k) : ℂ) -
        pointSeed E J (1 / 2) (laplacePoint (k + 1) x) /
          (Real.sqrt (laplaceHeight (k + 1)) : ℂ))) =
      if J = j then (laplaceTest k E : ℂ) else 0 := by
  simp_rw [normalized_pointSeed_at_laplacePoint]
  have heq (x : ℝ) : horizontalPhase (-j) x *
      ((Real.exp (-2 * π * laplaceHeight k * E) : ℂ) * horizontalPhase J x -
        (Real.exp (-2 * π * laplaceHeight (k + 1) * E) : ℂ) * horizontalPhase J x) =
      (laplaceTest k E : ℂ) * (horizontalPhase (-j) x * horizontalPhase J x) := by
    rw [laplaceTest_eq_height_difference]
    push_cast
    ring
  simp_rw [heq]
  rw [intervalIntegral.integral_const_mul, horizontal_fourier_orthogonality]
  split_ifs <;> simp

theorem laplaceTest_eq_regularizer_mul_pow (k : ℕ) (E : ℝ) :
    laplaceTest k E =
      (Real.exp (-E) * (1 - Real.exp (-E))) * Real.exp (-E) ^ k := by
  rw [← Real.exp_nat_mul]
  unfold laplaceTest
  have h : -((k : ℝ) + 1) * E = -E + (k : ℝ) * -E := by ring
  rw [h, Real.exp_add]
  ring

@[simp] theorem laplaceTest_zero (k : ℕ) : laplaceTest k 0 = 0 := by
  simp [laplaceTest]

theorem laplaceTest_pos (k : ℕ) {E : ℝ} (hE : 0 < E) : 0 < laplaceTest k E := by
  unfold laplaceTest
  exact mul_pos (Real.exp_pos _) (sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hE)))

/-- Scalar endpoint domination: the vanishing factor gains one full power. -/
theorem laplaceTest_le_energy (k : ℕ) (E : ℝ) :
    laplaceTest k E ≤ E * Real.exp (-((k : ℝ) + 1) * E) := by
  have h := Real.add_one_le_exp (-E)
  have hh : 1 - Real.exp (-E) ≤ E := by linarith
  unfold laplaceTest
  nlinarith [Real.exp_pos (-((k : ℝ) + 1) * E)]

theorem laplaceTest_le_exp (k : ℕ) (E : ℝ) :
    laplaceTest k E ≤ Real.exp (-((k : ℝ) + 1) * E) := by
  unfold laplaceTest
  nlinarith [Real.exp_pos (-((k : ℝ) + 1) * E), Real.exp_pos (-E)]

/-- The normalized transform of an atom at zero is annihilated exactly. -/
theorem laplaceTest_origin_atom (k : ℕ) :
    (∫ E : ℝ, laplaceTest k E ∂Measure.dirac 0) = 0 := by
  simp

theorem scalar_laplaceTest_integrable (k : ℕ) :
    IntegrableOn (fun E : ℝ => E ^ (-(1 / 2 : ℝ)) * laplaceTest k E) (Ioi 0) := by
  have h := (scalar_rank_one_integrable (laplaceHeight_pos k)).sub
    (scalar_rank_one_integrable (laplaceHeight_pos (k + 1)))
  convert h using 1
  ext E
  simp only [laplaceTest_eq_height_difference, mul_sub, Pi.sub_apply]

theorem scalar_laplaceTest_integral (k : ℕ) :
    (∫ E : ℝ in Ioi 0, E ^ (-(1 / 2 : ℝ)) * laplaceTest k E) =
      1 / Real.sqrt (2 * laplaceHeight k) -
        1 / Real.sqrt (2 * laplaceHeight (k + 1)) := by
  simp_rw [laplaceTest_eq_height_difference, mul_sub]
  rw [integral_sub (scalar_rank_one_integrable (laplaceHeight_pos k))
    (scalar_rank_one_integrable (laplaceHeight_pos (k + 1))),
    scalar_rank_one_integral (laplaceHeight_pos k),
    scalar_rank_one_integral (laplaceHeight_pos (k + 1))]

/-- The four normalized evaluations of the spatial constant six have precisely
the coefficient twelve of the scalar rank-one density. -/
theorem rank_one_four_height_identity (k l : ℕ) :
    6 * ((1 / Real.sqrt (laplaceHeight k) - 1 / Real.sqrt (laplaceHeight (k + 1))) *
      (1 / Real.sqrt (laplaceHeight l) - 1 / Real.sqrt (laplaceHeight (l + 1)))) =
      12 * (∫ E : ℝ in Ioi 0, E ^ (-(1 / 2 : ℝ)) * laplaceTest k E) *
        (∫ E : ℝ in Ioi 0, E ^ (-(1 / 2 : ℝ)) * laplaceTest l E) := by
  rw [scalar_laplaceTest_integral, scalar_laplaceTest_integral]
  simp_rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  field_simp
  rw [hs]
  ring

/-- An arbitrary finite linear test of a positive kernel is positive. The
actual finite support is supplied by `x`; repeated points are allowed. -/
theorem posSemidef_finite_test {α ι κ : Type*} [Fintype ι] [Fintype κ]
    {K : Matrix α α ℂ} (hK : K.PosSemidef) (x : ι → α) (c : Matrix ι κ ℂ) :
    Matrix.PosSemidef (fun i j => ∑ a, ∑ b, star (c a i) * K (x a) (x b) * c b j) := by
  have h := (hK.submatrix x).conjTranspose_mul_mul_same c
  have heq : (fun i j => ∑ a, ∑ b, star (c a i) * K (x a) (x b) * c b j) =
      c.conjTranspose * K.submatrix x x * c := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply,
      Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [heq]
  exact h

end GapFamily.Analytic
