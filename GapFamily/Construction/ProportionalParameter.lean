import GapFamily.Construction.InitialParameter
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Continuous charge parameter for a proportional gap

The auxiliary integers are fixed before the charge or gap ratio is chosen.
Rounding the degree down allows every sufficiently large real charge.
-/

open Real

namespace GapFamily.Construction

/-- The integer initial degree for an arbitrary real charge parameter. -/
noncomputable def proportionalDegree (a : ℝ) (s : ℕ) : ℕ := ⌊a / s⌋₊

/-- The initial cutoff at an arbitrary real charge parameter. -/
noncomputable def proportionalCutoff (a : ℝ) (s : ℕ) : ℝ := a / (s : ℝ) ^ 2

theorem proportionalParameter_degree_le {a : ℝ} (ha : 0 ≤ a) (s : ℕ) :
    (proportionalDegree a s : ℝ) ≤ a / s :=
  Nat.floor_le (by positivity)

theorem proportionalParameter_half_le_degree {a : ℝ} {s : ℕ}
    (hlarge : 2 ≤ a / s) :
    a / (2 * s) ≤ (proportionalDegree a s : ℝ) := by
  have hf := Nat.lt_floor_add_one (a / s)
  change a / (2 * s) ≤ (⌊a / s⌋₊ : ℝ)
  have heq : a / (2 * s) = (a / s) / 2 := by ring
  rw [heq]
  linarith

theorem proportionalParameter_sqrt_aU {a : ℝ} (ha : 0 ≤ a) (s : ℕ) :
    sqrt (a * proportionalCutoff a s) = a / s := by
  have heq : a * proportionalCutoff a s = (a / s) ^ 2 := by
    unfold proportionalCutoff
    ring
  rw [heq, sqrt_sq (by positivity)]

theorem proportionalParameter_degree_le_sqrt_aU {a : ℝ} (ha : 0 ≤ a) (s : ℕ) :
    (proportionalDegree a s : ℝ) ≤ sqrt (a * proportionalCutoff a s) := by
  rw [proportionalParameter_sqrt_aU ha]
  exact proportionalParameter_degree_le ha s

/-- A fixed sufficiently small positive gap ratio makes the negative
exponential scale no greater than the rounded initial degree. -/
theorem proportionalParameter_negative_exponent_le {a κ C_N : ℝ} {R s : ℕ}
    (ha : 0 ≤ a) (hR : 1 ≤ R) (hs : 1 ≤ s)
    (hC : C_N ≤ sqrt (R : ℝ))
    (hκ : κ ≤ 1 / (4 * R * (s : ℝ) ^ 2)) (hlarge : 2 ≤ a / s) :
    C_N * sqrt (a * (κ * a)) ≤ (proportionalDegree a s : ℝ) := by
  have hspos : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hRpos : (0 : ℝ) < R := by exact_mod_cast (show 0 < R by omega)
  have hκ' : κ * (4 * R * (s : ℝ) ^ 2) ≤ 1 :=
    (le_div_iff₀ (by positivity)).mp hκ
  have hsq : (R : ℝ) * (a * (κ * a)) ≤ (a / (2 * s)) ^ 2 := by
    have hm := mul_le_mul_of_nonneg_right hκ' (sq_nonneg a)
    rw [div_pow]
    apply (le_div_iff₀ (show 0 < (2 * (s : ℝ)) ^ 2 by positivity)).mpr
    nlinarith [hm]
  calc
    _ ≤ sqrt (R : ℝ) * sqrt (a * (κ * a)) :=
      mul_le_mul_of_nonneg_right hC (sqrt_nonneg _)
    _ = sqrt ((R : ℝ) * (a * (κ * a))) := (sqrt_mul (Nat.cast_nonneg R) _).symm
    _ ≤ a / (2 * s) := (sqrt_le_iff).mpr ⟨by positivity, hsq⟩
    _ ≤ _ := proportionalParameter_half_le_degree hlarge

/-- The marker lies well below the initial processing cutoff. -/
theorem proportionalParameter_gap_le_cutoff {a κ : ℝ} {R s : ℕ}
    (ha : 0 ≤ a) (_hR : 1 ≤ R) (_hs : 1 ≤ s)
    (hκ : κ ≤ 1 / (4 * R * (s : ℝ) ^ 2)) :
    κ * a ≤ proportionalCutoff a s / (4 * R) := by
  have hm := mul_le_mul_of_nonneg_right hκ ha
  have heq : (1 / (4 * R * (s : ℝ) ^ 2)) * a =
      proportionalCutoff a s / (4 * R) := by
    unfold proportionalCutoff
    ring
  exact heq ▸ hm

theorem proportionalParameter_polynomial_base_le {a : ℝ} {s : ℕ}
    (hs : 1 ≤ s) :
    1 + a ≤ (2 * (s : ℝ) + 1) * ((proportionalDegree a s : ℝ) + 1) := by
  have hspos : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hf := (div_lt_iff₀ hspos).mp (Nat.lt_floor_add_one (a / s))
  change 1 + a ≤ (2 * (s : ℝ) + 1) * ((⌊a / s⌋₊ : ℝ) + 1)
  nlinarith [show (0 : ℝ) ≤ (⌊a / s⌋₊ : ℕ) from Nat.cast_nonneg _]

/-- An explicit real threshold gives arbitrarily large degree. -/
theorem proportionalParameter_degree_threshold {s : ℕ} (hs : 1 ≤ s)
    (n : ℕ) (a : ℝ) (ha : (s : ℝ) * ((n : ℝ) + 2) ≤ a) :
    n ≤ proportionalDegree a s ∧ 2 ≤ a / s := by
  have hspos : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have han : (n : ℝ) + 2 ≤ a / s := by
    apply (le_div_iff₀ hspos).mpr
    nlinarith
  constructor
  · exact (Nat.le_floor_iff (by linarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg _])).mpr
      (by linarith)
  · linarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg _]

theorem exists_proportionalParameter_degree_threshold {s : ℕ} (hs : 1 ≤ s)
    (n : ℕ) : ∃ a₀ : ℝ, 1 ≤ a₀ ∧ ∀ a : ℝ, a₀ ≤ a →
      n ≤ proportionalDegree a s ∧ 2 ≤ a / s := by
  have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
  refine ⟨(s : ℝ) * ((n : ℝ) + 2),
    by nlinarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg _], ?_⟩
  intro a ha
  exact proportionalParameter_degree_threshold hs n a ha

/-- Every real charge bound holds above a positive threshold. -/
theorem exists_proportionalParameter_charge_threshold (A : ℝ) :
    ∃ a₀ : ℝ, 1 ≤ a₀ ∧ ∀ a : ℝ, a₀ ≤ a → A ≤ a := by
  refine ⟨max 1 A, le_max_left _ _, ?_⟩
  intro a ha
  exact (le_max_right _ _).trans ha

/-- A fixed positive gap ratio allows every real marker threshold. -/
theorem exists_proportionalParameter_gap_threshold {κ : ℝ} (hκ : 0 < κ) (B : ℝ) :
    ∃ a₀ : ℝ, 1 ≤ a₀ ∧ ∀ a : ℝ, a₀ ≤ a → B ≤ κ * a := by
  obtain ⟨a₀, ha₀1, ha₀⟩ := exists_proportionalParameter_charge_threshold (B / κ)
  refine ⟨a₀, ha₀1, ?_⟩
  intro a ha
  have h := (div_le_iff₀ hκ).mp (ha₀ a ha)
  simpa only [mul_comm κ] using h

theorem proportionalParameter_cutoff_le_charge {a : ℝ} (ha : 0 ≤ a)
    {s : ℕ} (hs : 1 ≤ s) : proportionalCutoff a s ≤ a := by
  have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
  unfold proportionalCutoff
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith [mul_nonneg ha (show 0 ≤ (s : ℝ) ^ 2 - 1 by nlinarith)]

theorem proportionalParameter_charge_le_degree {a : ℝ} {s : ℕ} (hs : 1 ≤ s)
    (hlarge : 2 ≤ a / s) : a ≤ 2 * s * (proportionalDegree a s : ℝ) := by
  have hspos : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have h := (div_le_iff₀ (show 0 < 2 * (s : ℝ) by positivity)).mp
    (proportionalParameter_half_le_degree hlarge)
  nlinarith

theorem proportionalParameter_scaled_cutoff_le_degree {a : ℝ} {s : ℕ}
    (hs : 1 ≤ s) (hlarge : 2 ≤ a / s) :
    (s : ℝ) * proportionalCutoff a s ≤ 2 * (proportionalDegree a s : ℝ) := by
  have hspos : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have h := proportionalParameter_charge_le_degree hs hlarge
  have heq : (s : ℝ) * proportionalCutoff a s = a / s := by
    unfold proportionalCutoff
    field_simp
  rw [heq]
  apply (div_le_iff₀ hspos).mpr
  nlinarith

theorem proportionalParameter_scaled_repairBand_le {a : ℝ} {s : ℕ}
    (hs : 1 ≤ s) (hlarge : 2 ≤ a / s) (hU : 1 ≤ proportionalCutoff a s) :
    (s : ℝ) * (2 * proportionalCutoff a s + 4) ≤
      12 * (proportionalDegree a s : ℝ) := by
  have h := proportionalParameter_scaled_cutoff_le_degree hs hlarge
  have hband : 2 * proportionalCutoff a s + 4 ≤ 6 * proportionalCutoff a s := by
    linarith
  have hm := mul_le_mul_of_nonneg_left hband (Nat.cast_nonneg s : (0 : ℝ) ≤ s)
  nlinarith

end GapFamily.Construction
