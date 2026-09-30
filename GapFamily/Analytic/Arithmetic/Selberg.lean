import GapFamily.Analytic.Arithmetic.Kloosterman
import GapFamily.Analytic.Arithmetic.SelbergGcd
import GapFamily.Analytic.Arithmetic.SelbergCongruence

/-!
# Additive-character decomposition for the Selberg identity

The finite character calculation follows the orthogonality proof in Ping Xi,
`An elementary proof of the Selberg identity for Kloosterman sums` (2023).
All sums below are actual finite sums over residue rings and their units.
-/

noncomputable section

namespace GapFamily.Analytic

open scoped BigOperators

/-- The same Kloosterman sum with residue arguments and an arbitrary positive modulus. -/
def residueKloostermanSum (c : ℕ) [NeZero c] (m n : ZMod c) : ℂ :=
  ∑ u : (ZMod c)ˣ, ZMod.stdAddChar (m * (u : ZMod c) + n * ((u⁻¹ : (ZMod c)ˣ) : ZMod c))

@[simp] theorem residueKloostermanSum_int (m n : ℤ) (c : ℕ) :
    residueKloostermanSum (c + 1) m n = kloostermanSum m n c := rfl

theorem residueKloostermanSum_eq_index (c : ℕ) [NeZero c] (m n : ℤ) :
    residueKloostermanSum c m n = kloostermanSum m n (c - 1) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne c)
  subst c
  simp [residueKloostermanSum_int]

/-- Primitive additive-character orthogonality, including modulus one. -/
theorem selberg_character_orthogonality (c : ℕ) [NeZero c] (b : ZMod c) :
    (∑ x : ZMod c, ZMod.stdAddChar (x * b)) = if b = 0 then (c : ℂ) else 0 := by
  simpa only [ZMod.card, Nat.cast_ite, Nat.cast_zero] using
    AddChar.sum_mulShift b (ZMod.isPrimitive_stdAddChar c)

/-- A congruence delta expressed by its actual finite character sum. -/
theorem selberg_character_delta (c : ℕ) [NeZero c] (a b : ZMod c) :
    (if a = 0 then ZMod.stdAddChar b else 0) =
      (∑ x : ZMod c, ZMod.stdAddChar (x * a + b)) / (c : ℂ) := by
  simp_rw [AddChar.map_add_eq_mul, ← Finset.sum_mul]
  rw [selberg_character_orthogonality]
  have hc : (c : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne c
  by_cases ha : a = 0 <;> simp [ha, hc]

/-- The inverse pair of a unit is exactly a pair with product one. -/
def selbergUnitPairEquiv (c : ℕ) :
    (ZMod c)ˣ ≃ {p : ZMod c × ZMod c // p.1 * p.2 = 1} where
  toFun u := ⟨((u : ZMod c), ((u⁻¹ : (ZMod c)ˣ) : ZMod c)), Units.mul_inv u⟩
  invFun p := Units.mkOfMulEqOne p.val.1 p.val.2 p.property
  left_inv u := Units.ext rfl
  right_inv p := by
    apply Subtype.ext
    rfl

/-- Product-one residue pairs enumerate exactly the original unit sum. -/
theorem residueKloostermanSum_eq_product_pairs (c : ℕ) [NeZero c] (m n : ZMod c) :
    residueKloostermanSum c m n =
      ∑ p : {p : ZMod c × ZMod c // p.1 * p.2 = 1},
        ZMod.stdAddChar (m * p.val.1 + n * p.val.2) := by
  exact (selbergUnitPairEquiv c).sum_comp
    (fun p => ZMod.stdAddChar (m * p.val.1 + n * p.val.2))

theorem residueKloostermanSum_eq_product_constraint (c : ℕ) [NeZero c]
    (m n : ZMod c) :
    residueKloostermanSum c m n =
      ∑ x : ZMod c, ∑ y : ZMod c,
        if x * y = 1 then ZMod.stdAddChar (m * x + n * y) else 0 := by
  classical
  rw [residueKloostermanSum_eq_product_pairs]
  rw [← Finset.sum_subtype (Finset.univ.filter (fun p : ZMod c × ZMod c => p.1 * p.2 = 1))
    (by intro p; simp) (fun p => ZMod.stdAddChar (m * p.1 + n * p.2))]
  rw [Finset.sum_filter, Fintype.sum_prod_type]

/-- Xi's first step is an exact finite triple sum for the original Kloosterman sum. -/
theorem residueKloostermanSum_eq_triple_sum (c : ℕ) [NeZero c] (m n : ZMod c) :
    residueKloostermanSum c m n =
      (∑ a : ZMod c, ∑ x : ZMod c, ∑ y : ZMod c,
        ZMod.stdAddChar (x * (m + a * y) + n * y - a)) / (c : ℂ) := by
  classical
  rw [residueKloostermanSum_eq_product_constraint]
  have hd (x y : ZMod c) :
      (if x * y = 1 then ZMod.stdAddChar (m * x + n * y) else 0) =
        (∑ a : ZMod c,
          ZMod.stdAddChar (x * (m + a * y) + n * y - a)) / (c : ℂ) := by
    have h := selberg_character_delta c (x * y - 1) (m * x + n * y)
    simp only [sub_eq_zero] at h
    rw [h]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    congr 1
    ring
  simp_rw [hd]
  simp_rw [← Finset.sum_div]
  congr 1
  calc
    (∑ x : ZMod c, ∑ y : ZMod c, ∑ a : ZMod c,
      ZMod.stdAddChar (x * (m + a * y) + n * y - a)) =
      ∑ x : ZMod c, ∑ a : ZMod c, ∑ y : ZMod c,
        ZMod.stdAddChar (x * (m + a * y) + n * y - a) := by
      apply Finset.sum_congr rfl
      intro x _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- Summing one residue variable leaves a genuine linear-congruence fibre. -/
theorem residueKloostermanSum_eq_linear_constraint (c : ℕ) [NeZero c] (m n : ZMod c) :
    residueKloostermanSum c m n =
      ∑ a : ZMod c, ∑ y : ZMod c,
        if m + a * y = 0 then ZMod.stdAddChar (n * y - a) else 0 := by
  classical
  rw [residueKloostermanSum_eq_triple_sum]
  have hc : (c : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne c
  have hd (a y : ZMod c) :
      (∑ x : ZMod c, ZMod.stdAddChar (x * (m + a * y) + n * y - a)) =
        (c : ℂ) * (if m + a * y = 0 then ZMod.stdAddChar (n * y - a) else 0) := by
    have h := selberg_character_delta c (m + a * y) (n * y - a)
    simp_rw [add_sub_assoc] at *
    exact (eq_div_iff hc).mp h |>.symm.trans (mul_comm _ _)
  have hsum : (∑ a : ZMod c, ∑ x : ZMod c, ∑ y : ZMod c,
      ZMod.stdAddChar (x * (m + a * y) + n * y - a)) =
      (c : ℂ) * ∑ a : ZMod c, ∑ y : ZMod c,
        if m + a * y = 0 then ZMod.stdAddChar (n * y - a) else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_comm, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun y _ => hd a y)
  rw [hsum, mul_div_cancel_left₀ _ hc]

/-- Evaluation of the actual congruence fibre in one divisor–unit stratum. -/
theorem selberg_divisor_unit_inner (d q : ℕ) [NeZero d] [NeZero q]
    (m n : ℤ) (a : (ZMod q)ˣ) :
    (∑ y : ZMod (d * q),
      if (m : ZMod (d * q)) + ((d * (a : ZMod q).val : ℕ) : ZMod (d * q)) * y = 0
      then ZMod.stdAddChar ((n : ZMod (d * q)) * y -
        ((d * (a : ZMod q).val : ℕ) : ZMod (d * q))) else 0) =
      if (d : ℤ) ∣ m ∧ (d : ℤ) ∣ n then
        (d : ℂ) * ZMod.stdAddChar (((n / d : ℤ) : ZMod q) *
          (-((a⁻¹ : (ZMod q)ˣ) : ZMod q) * ((m / d : ℤ) : ZMod q)) - (a : ZMod q))
      else 0 := by
  classical
  simp_rw [selberg_linear_congruence_iff]
  by_cases hm : (d : ℤ) ∣ m
  · simp only [hm, true_and]
    rw [← Finset.sum_filter]
    have hp (y : ZMod (d * q)) :
        (n : ZMod (d * q)) * y - ((d * (a : ZMod q).val : ℕ) : ZMod (d * q)) =
        (n : ZMod (d * q)) * y +
          (((d : ℤ) * (-(a : ZMod q).val : ℤ) : ℤ) : ZMod (d * q)) := by
      push_cast
      ring
    simp_rw [hp]
    rw [sum_stdAddChar_residue_filter_affine]
    simp only [Int.cast_neg, Int.cast_natCast, ZMod.natCast_zmod_val, ← sub_eq_add_neg]
  · simp [hm]

/-- A complete divisor stratum is one smaller-modulus Kloosterman sum with
its exact multiplicity, and vanishes unless the divisor divides both inputs. -/
theorem selberg_divisor_block (d q : ℕ) [NeZero d] [NeZero q] (m n : ℤ) :
    (∑ a : (ZMod q)ˣ, ∑ y : ZMod (d * q),
      if (m : ZMod (d * q)) + ((d * (a : ZMod q).val : ℕ) : ZMod (d * q)) * y = 0
      then ZMod.stdAddChar ((n : ZMod (d * q)) * y -
        ((d * (a : ZMod q).val : ℕ) : ZMod (d * q))) else 0) =
      if (d : ℤ) ∣ m ∧ (d : ℤ) ∣ n then
        (d : ℂ) * residueKloostermanSum q ((m / d : ℤ) * (n / d : ℤ)) 1 else 0 := by
  classical
  simp_rw [selberg_divisor_unit_inner]
  split_ifs with h
  · rw [← Finset.mul_sum, sum_stdAddChar_selberg_phase]
    simp only [residueKloostermanSum, one_mul]
  · simp

/-- The same stratum evaluation with a separately named ambient modulus. -/
theorem selberg_divisor_block_of_mul (c d q : ℕ) [NeZero c] [NeZero d] [NeZero q]
    (hc : c = d * q) (m n : ℤ) :
    (∑ a : (ZMod q)ˣ, ∑ y : ZMod c,
      if (m : ZMod c) + ((d * (a : ZMod q).val : ℕ) : ZMod c) * y = 0
      then ZMod.stdAddChar ((n : ZMod c) * y -
        ((d * (a : ZMod q).val : ℕ) : ZMod c)) else 0) =
      if (d : ℤ) ∣ m ∧ (d : ℤ) ∣ n then
        (d : ℂ) * residueKloostermanSum q ((m / d : ℤ) * (n / d : ℤ)) 1 else 0 := by
  subst c
  exact selberg_divisor_block d q m n

/-- The finite Selberg identity for every positive modulus and both signed inputs.
The divisor sum includes modulus one and zero frequencies without exceptions. -/
theorem residueKloostermanSum_selberg (c : ℕ) [NeZero c] (m n : ℤ) :
    residueKloostermanSum c m n =
      ∑ d : {d : ℕ // d ∣ c},
        if (d.val : ℤ) ∣ m ∧ (d.val : ℤ) ∣ n then
          (d.val : ℂ) * residueKloostermanSum (c / d.val)
            ((m / d.val : ℤ) * (n / d.val : ℤ)) 1 else 0 := by
  classical
  rw [residueKloostermanSum_eq_linear_constraint, sum_zmod_eq_sum_divisorUnit]
  apply Finset.sum_congr rfl
  intro d _
  exact selberg_divisor_block_of_mul c d.val (c / d.val)
    (Nat.mul_div_cancel' d.property).symm m n

/-- Exact integer quotients recover the customary `m*n/d²` argument. -/
theorem selberg_quotient_product {m n d : ℤ} (hd : d ≠ 0) (hm : d ∣ m) (hn : d ∣ n) :
    (m / d) * (n / d) = (m * n) / d ^ 2 := by
  obtain ⟨a, rfl⟩ := hm
  obtain ⟨b, rfl⟩ := hn
  rw [Int.mul_ediv_cancel_left _ hd, Int.mul_ediv_cancel_left _ hd]
  rw [show (d * a) * (d * b) = d ^ 2 * (a * b) by ring,
    Int.mul_ediv_cancel_left _ (pow_ne_zero 2 hd)]

/-- Selberg's identity for the original project Kloosterman sum. The index
`c` denotes denominator `c+1`, and the smaller denominator is `(c+1)/d`. -/
theorem kloostermanSum_selberg (m n : ℤ) (c : ℕ) :
    kloostermanSum m n c =
      ∑ d : {d : ℕ // d ∣ c + 1},
        if (d.val : ℤ) ∣ m ∧ (d.val : ℤ) ∣ n then
          (d.val : ℂ) * kloostermanSum (m * n / (d.val : ℤ) ^ 2) 1
            ((c + 1) / d.val - 1) else 0 := by
  classical
  rw [← residueKloostermanSum_int, residueKloostermanSum_selberg]
  apply Finset.sum_congr rfl
  intro d _
  split_ifs with h
  · rw [← Int.cast_mul,
      selberg_quotient_product (Nat.cast_ne_zero.mpr (NeZero.ne d.val)) h.1 h.2]
    exact congrArg (fun z : ℂ => (d.val : ℂ) * z)
      (by simpa only [Int.cast_one] using (residueKloostermanSum_eq_index
          ((c + 1) / d.val) (m * n / (d.val : ℤ) ^ 2) 1))
  · rfl

end GapFamily.Analytic
