import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Tactic

/-!
# Additive characters on a fibre of residue reduction

The fibre over a residue modulo `q` consists of the `d` distinct lifts modulo
`d*q`. Its signed-frequency character sum is computed by ordinary finite
character orthogonality. No coprimality of `d` and `q` is required.
-/

noncomputable section

namespace GapFamily.Analytic

/-- Reduction from modulus `d*q` to modulus `q`. -/
def residueReduction (d q : ℕ) : ZMod (d * q) →+* ZMod q :=
  ZMod.castHom (dvd_mul_left q d) (ZMod q)

@[simp] theorem residueReduction_natCast (d q k : ℕ) :
    residueReduction d q (k : ZMod (d * q)) = (k : ZMod q) :=
  map_natCast _ _

private theorem lift_val_lt (d q : ℕ) [NeZero d] [NeZero q]
    (x : ZMod q) (t : ZMod d) : x.val + q * t.val < d * q := by
  have hx := x.val_lt
  have ht := t.val_lt
  nlinarith

/-- An explicit parametrization of all lifts of one residue. -/
def residueLiftEquiv (d q : ℕ) [NeZero d] [NeZero q] (x : ZMod q) :
    ZMod d ≃ {y : ZMod (d * q) // residueReduction d q y = x} where
  toFun t := ⟨(x.val + q * t.val : ℕ), by simp⟩
  invFun y := (y.val.val / q : ℕ)
  left_inv t := by
    change (((((x.val + q * t.val : ℕ) : ZMod (d * q)).val / q : ℕ) : ZMod d)) = t
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (lift_val_lt d q x t)]
    rw [Nat.add_mul_div_left _ _ (NeZero.pos q), Nat.div_eq_of_lt x.val_lt]
    simp
  right_inv y := by
    apply Subtype.ext
    have hmod : y.val.val % q = x.val := by
      have h := congrArg ZMod.val y.prop
      have hy : residueReduction d q y.val = (y.val.val : ZMod q) := by
        conv_lhs => rw [← ZMod.natCast_zmod_val y.val]
        exact residueReduction_natCast d q y.val.val
      rw [hy, ZMod.val_natCast] at h
      exact h
    have hdiv : y.val.val / q < d := by
      exact (Nat.div_lt_iff_lt_mul (NeZero.pos q)).mpr (by simpa [mul_comm] using y.val.val_lt)
    change ((x.val + q * (((y.val.val / q : ℕ) : ZMod d).val) : ℕ) : ZMod (d * q)) = y.val
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hdiv, ← hmod, Nat.mod_add_div,
      ZMod.natCast_zmod_val]

@[simp] theorem residueLiftEquiv_apply (d q : ℕ) [NeZero d] [NeZero q]
    (x : ZMod q) (t : ZMod d) :
    (residueLiftEquiv d q x t).val = (x.val + q * t.val : ℕ) := rfl

/-- The character respects simultaneous scaling of the integer and modulus. -/
theorem stdAddChar_scale (d q : ℕ) [NeZero d] [NeZero q] (k : ℤ) :
    ZMod.stdAddChar ((q * k : ℤ) : ZMod (d * q)) =
      ZMod.stdAddChar (k : ZMod d) := by
  rw [ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  push_cast
  congr 1
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  field_simp

/-- The character also respects scaling by the left factor of the modulus. -/
theorem stdAddChar_scale_left (d q : ℕ) [NeZero d] [NeZero q] (k : ℤ) :
    ZMod.stdAddChar ((d * k : ℤ) : ZMod (d * q)) =
      ZMod.stdAddChar (k : ZMod q) := by
  rw [ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  push_cast
  congr 1
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  field_simp

/-- Orthogonality at an arbitrary signed integer frequency. -/
theorem sum_stdAddChar_int_mul (d : ℕ) [NeZero d] (n : ℤ) :
    (∑ t : ZMod d, ZMod.stdAddChar ((n : ZMod d) * t)) =
      if (d : ℤ) ∣ n then (d : ℂ) else 0 := by
  simpa [mul_comm, ZMod.intCast_zmod_eq_zero_iff_dvd, ZMod.card] using
    (AddChar.sum_mulShift (n : ZMod d) (ZMod.isPrimitive_stdAddChar d))

/-- The weighted sum over every lift of one residue. -/
theorem sum_stdAddChar_residue_lift (d q : ℕ) [NeZero d] [NeZero q]
    (x : ZMod q) (n : ℤ) :
    (∑ y : {y : ZMod (d * q) // residueReduction d q y = x},
      ZMod.stdAddChar ((n : ZMod (d * q)) * y.val)) =
      if (d : ℤ) ∣ n then
        (d : ℂ) * ZMod.stdAddChar (((n / d : ℤ) : ZMod q) * x) else 0 := by
  classical
  rw [← (residueLiftEquiv d q x).sum_comp]
  have hphase (t : ZMod d) :
      ZMod.stdAddChar ((n : ZMod (d * q)) * (residueLiftEquiv d q x t).val) =
        ZMod.stdAddChar ((n * x.val : ℤ) : ZMod (d * q)) *
          ZMod.stdAddChar ((n : ZMod d) * t) := by
    rw [residueLiftEquiv_apply, Nat.cast_add, Nat.cast_mul, mul_add,
      AddChar.map_add_eq_mul]
    congr 1
    · push_cast
      rfl
    · have h := stdAddChar_scale d q (n * t.val)
      push_cast at h
      simpa [mul_comm, mul_left_comm, mul_assoc] using h
  simp_rw [hphase]
  rw [← Finset.mul_sum, sum_stdAddChar_int_mul]
  split_ifs with hn
  · have heq : n = (d : ℤ) * (n / d) := (Int.mul_ediv_cancel' hn).symm
    have h := stdAddChar_scale_left d q ((n / d) * x.val)
    have hh : ZMod.stdAddChar ((n * x.val : ℤ) : ZMod (d * q)) =
        ZMod.stdAddChar (((n / d : ℤ) : ZMod q) * x) := by
      conv_lhs => rw [heq]
      simpa [mul_assoc] using h
    rw [hh, mul_comm]
  · simp

/-- Filtered-sum form of the lift character identity. -/
theorem sum_stdAddChar_residue_filter (d q : ℕ) [NeZero d] [NeZero q]
    (x : ZMod q) (n : ℤ) :
    (∑ y : ZMod (d * q) with residueReduction d q y = x,
      ZMod.stdAddChar ((n : ZMod (d * q)) * y)) =
      if (d : ℤ) ∣ n then
        (d : ℂ) * ZMod.stdAddChar (((n / d : ℤ) : ZMod q) * x) else 0 := by
  classical
  rw [Finset.sum_subtype (p := fun y => residueReduction d q y = x) _ (by simp)]
  exact sum_stdAddChar_residue_lift d q x n

/-- A constant phase divisible by the fibre size descends to the smaller modulus. -/
theorem sum_stdAddChar_residue_filter_affine (d q : ℕ) [NeZero d] [NeZero q]
    (x : ZMod q) (n k : ℤ) :
    (∑ y : ZMod (d * q) with residueReduction d q y = x,
      ZMod.stdAddChar ((n : ZMod (d * q)) * y + ((d * k : ℤ) : ZMod (d * q)))) =
      if (d : ℤ) ∣ n then
        (d : ℂ) * ZMod.stdAddChar (((n / d : ℤ) : ZMod q) * x + (k : ZMod q)) else 0 := by
  classical
  simp_rw [AddChar.map_add_eq_mul, stdAddChar_scale_left]
  rw [← Finset.sum_mul, sum_stdAddChar_residue_filter]
  split_ifs <;> simp [mul_assoc]

/-- The affine lift formula with a separately named ambient modulus. -/
theorem sum_stdAddChar_residue_filter_affine_of_mul (c d q : ℕ)
    [NeZero c] [NeZero d] [NeZero q] (hc : c = d * q) (hq : q ∣ c)
    (x : ZMod q) (n k : ℤ) :
    (∑ y : ZMod c with ZMod.castHom hq (ZMod q) y = x,
      ZMod.stdAddChar ((n : ZMod c) * y + ((d * k : ℤ) : ZMod c))) =
      if (d : ℤ) ∣ n then
        (d : ℂ) * ZMod.stdAddChar (((n / d : ℤ) : ZMod q) * x + (k : ZMod q)) else 0 := by
  subst c
  exact sum_stdAddChar_residue_filter_affine d q x n k

/-- Negated inversion puts the phase on a reduced congruence fibre into its
standard Kloosterman form. -/
theorem sum_stdAddChar_selberg_phase (q : ℕ) [NeZero q] (a b : ZMod q) :
    (∑ u : (ZMod q)ˣ,
      ZMod.stdAddChar (b * (-((u⁻¹ : (ZMod q)ˣ) : ZMod q) * a) - (u : ZMod q))) =
    ∑ u : (ZMod q)ˣ,
      ZMod.stdAddChar ((a * b) * (u : ZMod q) + ((u⁻¹ : (ZMod q)ˣ) : ZMod q)) := by
  classical
  let e : (ZMod q)ˣ ≃ (ZMod q)ˣ :=
    { toFun := fun u => -u⁻¹
      invFun := fun u => -u⁻¹
      left_inv := by intro u; simp
      right_inv := by intro u; simp }
  apply Fintype.sum_equiv e
  intro u
  congr 1
  change b * (-((u⁻¹ : (ZMod q)ˣ) : ZMod q) * a) - (u : ZMod q) =
    (a * b) * ((-u⁻¹ : (ZMod q)ˣ) : ZMod q) + (((-u⁻¹)⁻¹ : (ZMod q)ˣ) : ZMod q)
  simp only [Units.val_neg, inv_neg, inv_inv]
  ring

end GapFamily.Analytic
