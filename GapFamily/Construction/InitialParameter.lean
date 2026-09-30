import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Integer parameter choice for the initial cell

The natural parameters set `a = R s² n`, `b = n`, `U = R n`, and
`k = R s n`. Their square-root identities keep the positive and negative
initial-cell exponents explicit. The repair band is `2 U + 4`.
-/

open Real

namespace GapFamily.Construction

/-- A single integer enlargement controls the threshold and the negative
mass exponent. -/
theorem exists_initialParameter_radius (R0 : ℕ) (C_N : ℝ) (hC : 0 ≤ C_N) :
    ∃ R : ℕ, 1 ≤ R ∧ 16 * R0 ≤ R ∧ C_N ≤ sqrt (R : ℝ) := by
  obtain ⟨R, hR⟩ := exists_nat_ge (max (1 : ℝ) (max (((16 * R0 : ℕ) : ℝ)) (C_N ^ 2)))
  have hR1 : (1 : ℝ) ≤ R := (le_max_left _ _).trans hR
  have hR0 : ((16 * R0 : ℕ) : ℝ) ≤ R :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hR)
  have hRC : C_N ^ 2 ≤ R := (le_max_right _ _).trans ((le_max_right _ _).trans hR)
  refine ⟨R, by exact_mod_cast hR1, by exact_mod_cast hR0, ?_⟩
  exact (le_sqrt hC (Nat.cast_nonneg R)).mpr hRC

/-- The positive initial-cell exponent is exactly the integer degree scale. -/
theorem initialParameter_sqrt_aU (R s n : ℕ) :
    sqrt (((R * s ^ 2 * n : ℕ) : ℝ) * ((R * n : ℕ) : ℝ)) =
      ((R * s * n : ℕ) : ℝ) := by
  have heq : ((R * s ^ 2 * n : ℕ) : ℝ) * ((R * n : ℕ) : ℝ) =
      (((R * s * n : ℕ) : ℝ)) ^ 2 := by push_cast; ring
  rw [heq, sqrt_sq (Nat.cast_nonneg _)]

/-- The negative-mass square-root exponent retains the radius factor. -/
theorem initialParameter_sqrt_ab (R s n : ℕ) :
    sqrt (((R * s ^ 2 * n : ℕ) : ℝ) * (n : ℝ)) =
      (s : ℝ) * sqrt (R : ℝ) * (n : ℝ) := by
  have heq : ((R * s ^ 2 * n : ℕ) : ℝ) * (n : ℝ) =
      (R : ℝ) * (((s * n : ℕ) : ℝ)) ^ 2 := by push_cast; ring
  rw [heq, sqrt_mul (Nat.cast_nonneg R), sqrt_sq (Nat.cast_nonneg _)]
  push_cast
  ring

/-- The chosen radius makes the negative-mass exponential rate at most
the integer initial degree. -/
theorem initialParameter_negative_exponent_le (R s n : ℕ) {C_N : ℝ}
    (hC : C_N ≤ sqrt (R : ℝ)) :
    C_N * sqrt (((R * s ^ 2 * n : ℕ) : ℝ) * (n : ℝ)) ≤
      ((R * s * n : ℕ) : ℝ) := by
  rw [initialParameter_sqrt_ab]
  calc
    _ ≤ sqrt (R : ℝ) * ((s : ℝ) * sqrt (R : ℝ) * (n : ℝ)) :=
      mul_le_mul_of_nonneg_right hC (by positivity)
    _ = (sqrt (R : ℝ)) ^ 2 * (s : ℝ) * (n : ℝ) := by ring
    _ = _ := by rw [sq_sqrt (Nat.cast_nonneg R)]; push_cast; ring

/-- The integer ratio `a / b` is larger than one hundred for `s ≥ 11`. -/
theorem initialParameter_ratio_gt_hundred {R s : ℕ} (hR : 1 ≤ R) (hs : 11 ≤ s) :
    100 < R * s ^ 2 := by
  have hs2 : 121 ≤ s ^ 2 := by nlinarith
  have hmul : s ^ 2 ≤ R * s ^ 2 := Nat.le_mul_of_pos_left _ hR
  omega

/-- The initial processing cutoff is below the vacuum scale. -/
theorem initialParameter_U_le_a (R n : ℕ) {s : ℕ} (hs : 1 ≤ s) :
    R * n ≤ R * s ^ 2 * n := by
  have hs2 : 1 ≤ s ^ 2 := one_le_pow₀ hs
  have hR : R ≤ R * s ^ 2 := by simpa using Nat.mul_le_mul_left R hs2
  exact Nat.mul_le_mul_right n hR

/-- Multiplication by `s` bounds the repair band by six times the initial
degree, with no division or asymptotic notation. -/
theorem initialParameter_scaled_repairBand_le {R n : ℕ} (hR : 1 ≤ R) (hn : 1 ≤ n)
    (s : ℕ) :
    (s : ℝ) * (2 * ((R * n : ℕ) : ℝ) + 4) ≤ 6 * ((R * s * n : ℕ) : ℝ) := by
  have hRnNat : 1 ≤ R * n := by simpa using Nat.mul_le_mul hR hn
  have hRn : (1 : ℝ) ≤ ((R * n : ℕ) : ℝ) := by exact_mod_cast hRnNat
  have hband : 2 * ((R * n : ℕ) : ℝ) + 4 ≤ 6 * ((R * n : ℕ) : ℝ) := by linarith
  calc
    _ ≤ (s : ℝ) * (6 * ((R * n : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hband (Nat.cast_nonneg s)
    _ = _ := by push_cast; ring

end GapFamily.Construction
