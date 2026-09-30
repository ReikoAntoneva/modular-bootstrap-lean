import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Midpoint quadrature and total variation

The estimate in this file is the scalar error bound used by the quantile route to
prescribed-count quadrature. Variation means mathlib's supremum over ordered
partitions, not a derivative integral or an assumed error bound.
-/

open Set MeasureTheory

namespace GapFamily.Quadrature

/-- A constant sample on an interval differs from its integral by at most length
times the variation, provided the sample belongs to that interval. -/
theorem sample_integral_error_le_variation {f : ℝ → ℝ} {a b c : ℝ}
    (hab : a ≤ b) (hc : c ∈ Icc a b)
    (hf : IntervalIntegrable f volume a b)
    (hv : BoundedVariationOn f (Icc a b)) :
    |(b - a) * f c - ∫ x in a..b, f x| ≤
      (b - a) * (eVariationOn f (Icc a b)).toReal := by
  have hbound : ∀ x ∈ uIoc a b,
      ‖f c - f x‖ ≤ (eVariationOn f (Icc a b)).toReal := by
    intro x hx
    rw [uIoc_of_le hab] at hx
    simpa only [Real.dist_eq, Real.norm_eq_abs] using
      hv.dist_le hc ⟨hx.1.le, hx.2⟩
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [intervalIntegral.integral_sub intervalIntegrable_const hf,
    intervalIntegral.integral_const, smul_eq_mul, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr hab)] at h
  simpa only [mul_comm] using h

/-- Splitting at the midpoint improves the general sample error constant to
one half. No differentiability hypothesis is required. -/
theorem midpoint_integral_error_le_half_variation {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hv : BoundedVariationOn f (Icc a b)) :
    |(b - a) * f ((a + b) / 2) - ∫ x in a..b, f x| ≤
      ((b - a) / 2) * (eVariationOn f (Icc a b)).toReal := by
  let m := (a + b) / 2
  have ham : a ≤ m := by dsimp [m]; linarith
  have hmb : m ≤ b := by dsimp [m]; linarith
  have hsub₁ : Icc a m ⊆ Icc a b := Icc_subset_Icc_right hmb
  have hsub₂ : Icc m b ⊆ Icc a b := Icc_subset_Icc_left ham
  have hv₁ := hv.mono hsub₁
  have hv₂ := hv.mono hsub₂
  have hf₁ : IntervalIntegrable f volume a m :=
    (hf.mono hsub₁).intervalIntegrable_of_Icc ham
  have hf₂ : IntervalIntegrable f volume m b :=
    (hf.mono hsub₂).intervalIntegrable_of_Icc hmb
  have h₁ := sample_integral_error_le_variation ham ⟨ham, le_rfl⟩ hf₁ hv₁
  have h₂ := sample_integral_error_le_variation hmb ⟨le_rfl, hmb⟩ hf₂ hv₂
  have hvadd : (eVariationOn f (Icc a m)).toReal +
      (eVariationOn f (Icc m b)).toReal = (eVariationOn f (Icc a b)).toReal := by
    rw [← ENNReal.toReal_add hv₁ hv₂]
    congr 1
    simpa only [univ_inter] using
      eVariationOn.Icc_add_Icc f (s := univ) ham hmb (mem_univ m)
  have herr : (b - a) * f m - ∫ x in a..b, f x =
      ((m - a) * f m - ∫ x in a..m, f x) +
        ((b - m) * f m - ∫ x in m..b, f x) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hf₁ hf₂]
    ring
  change |(b - a) * f m - ∫ x in a..b, f x| ≤ _
  rw [herr]
  calc
    _ ≤ |(m - a) * f m - ∫ x in a..m, f x| +
        |(b - m) * f m - ∫ x in m..b, f x| := abs_add_le _ _
    _ ≤ (m - a) * (eVariationOn f (Icc a m)).toReal +
        (b - m) * (eVariationOn f (Icc m b)).toReal := add_le_add h₁ h₂
    _ = ((b - a) / 2) * (eVariationOn f (Icc a b)).toReal := by
      rw [show m - a = (b - a) / 2 by dsimp [m]; ring,
        show b - m = (b - a) / 2 by dsimp [m]; ring,
        ← mul_add, hvadd]

/-- The composite midpoint error is bounded by half the mesh size times
variation on the entire interval. -/
theorem composite_midpoint_error_le_variation {f : ℝ → ℝ} {a : ℕ → ℝ}
    {n : ℕ} {δ : ℝ} (ha : Monotone a)
    (hf : ContinuousOn f (Icc (a 0) (a n)))
    (hv : BoundedVariationOn f (Icc (a 0) (a n)))
    (hδ : ∀ i < n, a (i + 1) - a i ≤ δ) :
    |(∑ i ∈ Finset.range n, (a (i + 1) - a i) * f ((a i + a (i + 1)) / 2)) -
        ∫ x in a 0..a n, f x| ≤
      (δ / 2) * (eVariationOn f (Icc (a 0) (a n))).toReal := by
  have hsub (i : ℕ) (hi : i < n) : Icc (a i) (a (i + 1)) ⊆ Icc (a 0) (a n) :=
    Icc_subset_Icc (ha (Nat.zero_le i)) (ha (Nat.add_one_le_iff.mpr hi))
  have hint (i : ℕ) (hi : i < n) : IntervalIntegrable f volume (a i) (a (i + 1)) :=
    (hf.mono (hsub i hi)).intervalIntegrable_of_Icc (ha (Nat.le_succ i))
  have hvar (i : ℕ) (hi : i ∈ Finset.range n) :
      eVariationOn f (Icc (a i) (a (i + 1))) ≠ ⊤ :=
    hv.mono (hsub i (Finset.mem_range.mp hi))
  have hvsum : (∑ i ∈ Finset.range n,
      (eVariationOn f (Icc (a i) (a (i + 1)))).toReal) =
        (eVariationOn f (Icc (a 0) (a n))).toReal := by
    rw [← ENNReal.toReal_sum hvar, eVariationOn.sum' f ha]
  rw [← intervalIntegral.sum_integral_adjacent_intervals hint, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ Finset.range n,
        |(a (i + 1) - a i) * f ((a i + a (i + 1)) / 2) -
          ∫ x in a i..a (i + 1), f x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range n,
        (δ / 2) * (eVariationOn f (Icc (a i) (a (i + 1)))).toReal := by
      apply Finset.sum_le_sum
      intro i hi
      have hin := Finset.mem_range.mp hi
      exact (midpoint_integral_error_le_half_variation (ha (Nat.le_succ i))
        (hf.mono (hsub i hin)) (hv.mono (hsub i hin))).trans
          (mul_le_mul_of_nonneg_right (by linarith [hδ i hin]) ENNReal.toReal_nonneg)
    _ = _ := by rw [← Finset.mul_sum, hvsum]

/-- Exactly `n` equally spaced midpoint samples on the probability interval
have error at most `1 / (2*n)` times total variation. -/
theorem unit_midpoint_error_le_variation {f : ℝ → ℝ} {n : ℕ} (hn : 0 < n)
    (hf : ContinuousOn f (Icc 0 1)) (hv : BoundedVariationOn f (Icc 0 1)) :
    |(1 / (n : ℝ)) * (∑ i ∈ Finset.range n, f (((i : ℝ) + 1 / 2) / n)) -
        ∫ x in (0 : ℝ)..1, f x| ≤
      (1 / (2 * (n : ℝ))) * (eVariationOn f (Icc 0 1)).toReal := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  let a : ℕ → ℝ := fun i => i / n
  have ha : Monotone a := by
    intro i j hij
    exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hij) (Nat.cast_nonneg n)
  have ha₀ : a 0 = 0 := by simp [a]
  have han : a n = 1 := by simp [a, hn']
  have hf' : ContinuousOn f (Icc (a 0) (a n)) := by simpa [ha₀, han] using hf
  have hv' : BoundedVariationOn f (Icc (a 0) (a n)) := by simpa [ha₀, han] using hv
  have hδ (i : ℕ) (_hi : i < n) : a (i + 1) - a i ≤ 1 / (n : ℝ) := by
    dsimp [a]
    simp only [Nat.cast_add, Nat.cast_one]
    exact le_of_eq (by ring)
  have h := composite_midpoint_error_le_variation ha hf' hv' hδ
  have hsum : (∑ i ∈ Finset.range n,
      (a (i + 1) - a i) * f ((a i + a (i + 1)) / 2)) =
        (1 / (n : ℝ)) * (∑ i ∈ Finset.range n, f (((i : ℝ) + 1 / 2) / n)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    dsimp [a]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [show ((i : ℝ) + 1) / n - i / n = 1 / n by ring,
      show ((i : ℝ) / n + ((i : ℝ) + 1) / n) / 2 = ((i : ℝ) + 1 / 2) / n by ring]
  simpa only [hsum, ha₀, han, show (1 / (n : ℝ)) / 2 = 1 / (2 * (n : ℝ)) by ring]
    using h

/-- A monotone transport (in particular, an inverse cumulative distribution)
cannot increase the variation appearing in the midpoint error. This theorem
isolates the numerical part from the still-required continuous choice of a
positive density with prescribed moments. -/
theorem monotone_transport_midpoint_error {f q : ℝ → ℝ} {a b : ℝ} {n : ℕ}
    (hn : 0 < n) (hf : ContinuousOn f (Icc a b))
    (hv : BoundedVariationOn f (Icc a b))
    (hq : ContinuousOn q (Icc 0 1)) (hm : MonotoneOn q (Icc 0 1))
    (hmap : MapsTo q (Icc 0 1) (Icc a b)) :
    |(1 / (n : ℝ)) * (∑ i ∈ Finset.range n, f (q (((i : ℝ) + 1 / 2) / n))) -
        ∫ x in (0 : ℝ)..1, f (q x)| ≤
      (1 / (2 * (n : ℝ))) * (eVariationOn f (Icc a b)).toReal := by
  have hcomp : eVariationOn (f ∘ q) (Icc 0 1) ≤ eVariationOn f (Icc a b) :=
    eVariationOn.comp_le_of_monotoneOn f q hm hmap
  have hvcomp : BoundedVariationOn (f ∘ q) (Icc 0 1) :=
    ne_top_of_le_ne_top hv hcomp
  exact (unit_midpoint_error_le_variation hn (hf.comp hq hmap) hvcomp).trans
    (mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hv hcomp)
      (by positivity))

end GapFamily.Quadrature
