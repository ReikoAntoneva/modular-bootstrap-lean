import GapFamily.Analytic.Arithmetic.KloostermanDirichlet
import GapFamily.Analytic.Arithmetic.SelbergGcd
import GapFamily.Analytic.Arithmetic.SelbergLift
import GapFamily.Analytic.Arithmetic.SelbergUnit
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# The actual zero-frequency Ramanujan coefficient

The primitive additive-character sum is identified with the Möbius function
by decomposing all residues by their greatest common divisor. Orthogonality
gives its divisor sum, and inversion is carried out in the existing ring of
arithmetic functions. No character-sum formula is assumed.
-/

noncomputable section

namespace GapFamily.Analytic

/-- Inverting the unit in the actual phase leaves the primitive character sum. -/
theorem kloostermanCoefficient_zero_one_eq_unit_sum (c : ℕ) [NeZero c] :
    kloostermanCoefficient 0 1 c =
      ∑ u : (ZMod c)ˣ, ZMod.stdAddChar (u : ZMod c) := by
  cases c with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ k =>
    rw [kloostermanCoefficient_succ, kloostermanSum_symm]
    simp [kloostermanSum, kloostermanPhase]

private theorem stdAddChar_scale_left_of_mul (c d q : ℕ)
    [NeZero c] [NeZero d] [NeZero q] (hc : c = d * q) (k : ℤ) :
    ZMod.stdAddChar ((d * k : ℤ) : ZMod c) = ZMod.stdAddChar (k : ZMod q) := by
  subst c
  exact stdAddChar_scale_left d q k

/-- The character on a gcd stratum is exactly the primitive character at the
complementary modulus. -/
theorem stdAddChar_divisor_unit (c : ℕ) [NeZero c]
    (d : {d : ℕ // d ∣ c}) (u : (ZMod (c / d.val))ˣ) :
    ZMod.stdAddChar ((d.val * (u : ZMod (c / d.val)).val : ℕ) : ZMod c) =
      ZMod.stdAddChar (u : ZMod (c / d.val)) := by
  have h := stdAddChar_scale_left_of_mul c d.val (c / d.val)
    (Nat.mul_div_cancel' d.property).symm ((u : ZMod (c / d.val)).val : ℤ)
  simpa only [Int.cast_mul, Int.cast_natCast, Nat.cast_mul,
    ZMod.natCast_zmod_val] using h

/-- The sum of the standard character over all residues is the unit-modulus
delta, including the one-element ring. -/
theorem sum_stdAddChar_eq_modulus_delta (c : ℕ) [NeZero c] :
    (∑ x : ZMod c, ZMod.stdAddChar x) = if c = 1 then 1 else 0 := by
  have h := sum_stdAddChar_int_mul c 1
  simp only [Int.cast_one, one_mul] at h
  have hd : (c : ℤ) ∣ (1 : ℤ) ↔ c = 1 := by
    constructor
    · intro hc
      have hc' : c ∣ 1 := by exact_mod_cast hc
      exact Nat.dvd_one.mp hc'
    · intro hc
      simp [hc]
  rw [h]
  by_cases hc : c = 1 <;> simp [hd, hc]

/-- Summing the primitive character coefficients over divisors gives the
Dirichlet-convolution identity function. -/
theorem sum_divisors_kloostermanCoefficient_zero_one (c : ℕ) :
    (∑ d ∈ c.divisors, kloostermanCoefficient 0 1 d) =
      if c = 1 then 1 else 0 := by
  classical
  by_cases hc : c = 0
  · simp [hc]
  let : NeZero c := ⟨hc⟩
  have hsub : (∑ d ∈ c.divisors, kloostermanCoefficient 0 1 (c / d)) =
      ∑ d : {d : ℕ // d ∣ c}, kloostermanCoefficient 0 1 (c / d.val) := by
    exact Finset.sum_subtype c.divisors
      (fun d => by simp [Nat.mem_divisors, hc])
      (fun d => kloostermanCoefficient 0 1 (c / d))
  rw [← Nat.sum_div_divisors c (kloostermanCoefficient 0 1), hsub]
  simp_rw [kloostermanCoefficient_zero_one_eq_unit_sum]
  calc
    _ = ∑ d : {d : ℕ // d ∣ c}, ∑ u : (ZMod (c / d.val))ˣ,
        ZMod.stdAddChar ((d.val * (u : ZMod (c / d.val)).val : ℕ) : ZMod c) := by
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro u _
      exact (stdAddChar_divisor_unit c d u).symm
    _ = ∑ x : ZMod c, ZMod.stdAddChar x :=
      (sum_zmod_eq_sum_divisorUnit (fun x : ZMod c => ZMod.stdAddChar x)).symm
    _ = _ := sum_stdAddChar_eq_modulus_delta c

/-- The actual Ramanujan coefficient is the Möbius function at every
denominator, with both zero conventions included. -/
theorem kloostermanCoefficient_zero_one_eq_moebius (c : ℕ) :
    kloostermanCoefficient 0 1 c = (ArithmeticFunction.moebius c : ℂ) := by
  let F : ArithmeticFunction ℂ :=
    ⟨kloostermanCoefficient 0 1, kloostermanCoefficient_zero 0 1⟩
  have hconv : F * (ArithmeticFunction.zeta : ArithmeticFunction ℂ) = 1 := by
    ext k
    rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply]
    exact sum_divisors_kloostermanCoefficient_zero_one k
  have hF : F = (ArithmeticFunction.moebius : ArithmeticFunction ℂ) := by
    calc
      F = F * ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) *
          (ArithmeticFunction.moebius : ArithmeticFunction ℂ)) := by
        rw [ArithmeticFunction.coe_zeta_mul_coe_moebius, mul_one]
      _ = _ := by rw [← mul_assoc, hconv, one_mul]
  have h := congrArg (fun f : ArithmeticFunction ℂ => f c) hF
  simpa only [F, ArithmeticFunction.coe_mk, ArithmeticFunction.intCoe_apply] using h

/-- Exact coefficient substitution into the uncontinued Dirichlet series. -/
theorem kloostermanDirichlet_zero_one_eq_moebius_LSeries (s : ℂ) :
    kloostermanDirichlet 0 1 s =
      LSeries (fun c : ℕ => (ArithmeticFunction.moebius c : ℂ)) (2 * s) := by
  unfold kloostermanDirichlet
  exact LSeries_congr (fun {_} _ => kloostermanCoefficient_zero_one_eq_moebius _) (2 * s)

end GapFamily.Analytic
