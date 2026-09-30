import GapFamily.Analytic.Arithmetic.SelbergLift

/-!
# Linear congruence in a divisor stratum

Dividing a congruence modulo `d*q` by `d` requires `d` to divide its
inhomogeneous integer frequency. After this divisibility check, a unit
coefficient modulo `q` determines exactly one fibre of residue reduction.
All integer frequencies are signed.
-/

noncomputable section

namespace GapFamily.Analytic

@[simp] theorem residueReduction_intCast (d q : ℕ) (m : ℤ) :
    residueReduction d q (m : ZMod (d * q)) = (m : ZMod q) :=
  map_intCast _ _

theorem residueReduction_eq_val (d q : ℕ) [NeZero d] [NeZero q]
    (y : ZMod (d * q)) :
    residueReduction d q y = (y.val : ZMod q) := by
  conv_lhs => rw [← ZMod.natCast_zmod_val y]
  exact residueReduction_natCast d q y.val

/-- Exact division of an integer congruence, with no sign restriction. -/
theorem mul_dvd_add_mul_iff (d q m t : ℤ) (hd : d ≠ 0) :
    d * q ∣ m + d * t ↔ d ∣ m ∧ q ∣ m / d + t := by
  constructor
  · rintro ⟨k, hk⟩
    have hm : d ∣ m := by
      use q * k - t
      nlinarith [hk]
    refine ⟨hm, ?_⟩
    obtain ⟨l, rfl⟩ := hm
    rw [Int.mul_ediv_cancel_left _ hd]
    use k
    apply mul_left_cancel₀ hd
    nlinarith [hk]
  · rintro ⟨⟨k, rfl⟩, h⟩
    rw [Int.mul_ediv_cancel_left _ hd] at h
    obtain ⟨l, hl⟩ := h
    use l
    calc
      d * k + d * t = d * (k + t) := by ring
      _ = d * q * l := by rw [hl]; ring

/-- A linear congruence modulo `d*q` reduces to an exact divisibility check and
a linear congruence modulo `q`. -/
theorem divisor_linear_congruence_iff (d q : ℕ) [NeZero d] [NeZero q]
    (m : ℤ) (b : ZMod q) (y : ZMod (d * q)) :
    (m : ZMod (d * q)) + ((d * b.val : ℕ) : ZMod (d * q)) * y = 0 ↔
      (d : ℤ) ∣ m ∧ ((m / d : ℤ) : ZMod q) + b * residueReduction d q y = 0 := by
  have hleft : (m : ZMod (d * q)) + ((d * b.val : ℕ) : ZMod (d * q)) * y =
      ((m + (d : ℤ) * (b.val * y.val) : ℤ) : ZMod (d * q)) := by
    push_cast
    rw [ZMod.natCast_zmod_val]
    ring
  have hright : ((m / d + (b.val * y.val : ℕ) : ℤ) : ZMod q) =
      ((m / d : ℤ) : ZMod q) + b * residueReduction d q y := by
    rw [residueReduction_eq_val]
    push_cast
    rw [ZMod.natCast_zmod_val]
  rw [hleft, ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_mul,
    mul_dvd_add_mul_iff _ _ _ _ (Nat.cast_ne_zero.mpr (NeZero.ne d))]
  rw [← hright, ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rfl

/-- Solving a linear equation whose coefficient is a unit. -/
theorem unit_linear_eq_zero_iff {R : Type*} [CommRing R] (a : Rˣ) (k y : R) :
    k + (a : R) * y = 0 ↔ y = -((a⁻¹ : Rˣ) : R) * k := by
  constructor
  · intro h
    have h' := congrArg (fun z => ((a⁻¹ : Rˣ) : R) * z) h
    have ha : ((a⁻¹ : Rˣ) : R) * ((a : R) * y) = y := by
      rw [← mul_assoc, Units.inv_mul, one_mul]
    simp only [mul_add, ha, mul_zero] at h'
    rw [add_comm, add_eq_zero_iff_eq_neg] at h'
    simpa only [neg_mul] using h'
  · intro h
    rw [h]
    calc
      k + (a : R) * (-((a⁻¹ : Rˣ) : R) * k) =
          k - ((a : R) * ((a⁻¹ : Rˣ) : R)) * k := by ring
      _ = 0 := by rw [Units.mul_inv]; ring

/-- The exact residue fibre solving a divisor-stratum congruence. -/
theorem selberg_linear_congruence_iff (d q : ℕ) [NeZero d] [NeZero q]
    (m : ℤ) (a : (ZMod q)ˣ) (y : ZMod (d * q)) :
    (m : ZMod (d * q)) +
        ((d * (a : ZMod q).val : ℕ) : ZMod (d * q)) * y = 0 ↔
      (d : ℤ) ∣ m ∧ residueReduction d q y =
        -((a⁻¹ : (ZMod q)ˣ) : ZMod q) * ((m / d : ℤ) : ZMod q) := by
  rw [divisor_linear_congruence_iff, unit_linear_eq_zero_iff]

end GapFamily.Analytic
