import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A weighted mass bound from a polynomial supremum estimate

The analytic helper below applies to any continuous nonnegative density whose
supremum is bounded by its average. The polynomial application supplies the
supremum estimate separately.
-/

open Set MeasureTheory

namespace GapFamily.Quadrature

/-- A nonnegative density with the indicated supremum bound cannot concentrate
all its mass next to zero. The parameter `r` is later the degree plus one. -/
theorem sq_mul_integral_lower_of_sup_bound {f : ℝ → ℝ} {a b r : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hr : 1 ≤ r)
    (hf : ContinuousOn f (Icc a b)) (hfnn : ∀ x ∈ Icc a b, 0 ≤ f x)
    (hsup : ∀ x ∈ Icc a b,
      f x ≤ 16 * r ^ 3 / (b - a) * (∫ y in a..b, f y)) :
    (b - a) ^ 2 / (8192 * r ^ 6) * (∫ x in a..b, f x) ≤
      ∫ x in a..b, x ^ 2 * f x := by
  let d := b - a
  let M := ∫ x in a..b, f x
  let δ := d / (64 * r ^ 3)
  let c := a + δ
  have hd : 0 < d := sub_pos.mpr hab
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hr3 : 1 ≤ r ^ 3 := one_le_pow₀ hr
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hδd : δ ≤ d := by
    dsimp [δ]
    apply (div_le_iff₀ (by positivity : 0 < 64 * r ^ 3)).2
    nlinarith
  have hac : a ≤ c := by dsimp [c]; linarith
  have hcb : c ≤ b := by dsimp [c] at *; dsimp [d] at hδd; linarith
  have hleft : Icc a c ⊆ Icc a b := Icc_subset_Icc le_rfl hcb
  have hright : Icc c b ⊆ Icc a b := Icc_subset_Icc hac le_rfl
  have hfl : IntervalIntegrable f volume a c :=
    (hf.mono hleft).intervalIntegrable_of_Icc hac
  have hfr : IntervalIntegrable f volume c b :=
    (hf.mono hright).intervalIntegrable_of_Icc hcb
  have hM : 0 ≤ M := intervalIntegral.integral_nonneg hab.le hfnn
  have hleft_le : (∫ x in a..c, f x) ≤ M / 4 := by
    calc
      (∫ x in a..c, f x) ≤ ∫ _ in a..c, 16 * r ^ 3 / d * M := by
        apply intervalIntegral.integral_mono_on hac hfl (intervalIntegrable_const)
        intro x hx
        exact hsup x (hleft hx)
      _ = M / 4 := by
        rw [intervalIntegral.integral_const]
        dsimp [c, δ]
        field_simp
        ring
  have hsplit : (∫ x in a..c, f x) + (∫ x in c..b, f x) = M :=
    intervalIntegral.integral_add_adjacent_intervals hfl hfr
  have hhalf : M / 2 ≤ ∫ x in c..b, f x := by linarith
  have hwcont : ContinuousOn (fun x => x ^ 2 * f x) (Icc a b) :=
    (continuousOn_id.pow 2).mul hf
  have hwleft : IntervalIntegrable (fun x => x ^ 2 * f x) volume a c :=
    (hwcont.mono hleft).intervalIntegrable_of_Icc hac
  have hwright : IntervalIntegrable (fun x => x ^ 2 * f x) volume c b :=
    (hwcont.mono hright).intervalIntegrable_of_Icc hcb
  have hwleft_nn : 0 ≤ ∫ x in a..c, x ^ 2 * f x := by
    apply intervalIntegral.integral_nonneg hac
    intro x hx
    exact mul_nonneg (sq_nonneg x) (hfnn x (hleft hx))
  have htail : δ ^ 2 * (∫ x in c..b, f x) ≤ ∫ x in c..b, x ^ 2 * f x := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hcb (hfr.const_mul _) hwright
    intro x hx
    have hδx : δ ≤ x := by have := hx.1; dsimp [c] at this; linarith
    apply mul_le_mul_of_nonneg_right _ (hfnn x (hright hx))
    exact pow_le_pow_left₀ hδ hδx 2
  have hwhole : (∫ x in c..b, x ^ 2 * f x) ≤ ∫ x in a..b, x ^ 2 * f x := by
    have hsum := intervalIntegral.integral_add_adjacent_intervals hwleft hwright
    linarith
  calc
    (b - a) ^ 2 / (8192 * r ^ 6) * (∫ x in a..b, f x) = δ ^ 2 * (M / 2) := by
      dsimp [δ, d, M]
      field_simp
      ring
    _ ≤ δ ^ 2 * (∫ x in c..b, f x) := mul_le_mul_of_nonneg_left hhalf (sq_nonneg δ)
    _ ≤ ∫ x in c..b, x ^ 2 * f x := htail
    _ ≤ ∫ x in a..b, x ^ 2 * f x := hwhole

end GapFamily.Quadrature
