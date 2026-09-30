import GapFamily.Quadrature.PolynomialBound

/-!
# Signed initial-cell density estimate

The density may be negative on the lower portion of the interval. Its total
negative mass controls that contribution, while a positive lower bound on
the upper portion supplies the positive polynomial moment.
-/

noncomputable section

open MeasureTheory Set

namespace GapFamily.Construction

/-- Ordinary negative mass of a signed coordinate density on an interval. -/
def initialCellNegativeMass (a b : ℝ) (q : ℝ → ℝ) : ℝ :=
  ∫ x in a..b, max (-q x) 0

theorem initialCell_negativePart_intervalIntegrable {a b : ℝ} {q : ℝ → ℝ}
    (hq : IntervalIntegrable q volume a b) :
    IntervalIntegrable (fun x => max (-q x) 0) volume a b :=
  ⟨hq.1.neg.pos_part, hq.2.neg.pos_part⟩

theorem initialCellNegativeMass_nonneg {a b : ℝ} (hab : a ≤ b) (q : ℝ → ℝ) :
    0 ≤ initialCellNegativeMass a b q :=
  intervalIntegral.integral_nonneg hab (fun _ _ => le_max_right _ _)

/-- A positive upper interval outweighs all possible signed loss below it.
Every term is an ordinary integrable density moment. -/
theorem initialCell_signed_integral_lower {a m b A M N : ℝ}
    (ham : a ≤ m) (hmb : m ≤ b) (hM : 0 ≤ M)
    (q : ℝ → ℝ) (hq : IntervalIntegrable q volume a b)
    (hnegative : initialCellNegativeMass a b q ≤ N)
    (hupper : ∀ x ∈ Icc m b, A ≤ q x)
    (p : ℝ → ℝ) (hp : ContinuousOn p (Icc a b))
    (hpos : ∀ x ∈ Icc a b, 0 ≤ p x)
    (hbound : ∀ x ∈ Icc a b, p x ≤ M) :
    A * (∫ x in m..b, p x) - M * N ≤ ∫ x in a..b, p x * q x := by
  have hab := ham.trans hmb
  have hleft : Icc a m ⊆ Icc a b := Icc_subset_Icc_right hmb
  have hright : Icc m b ⊆ Icc a b := Icc_subset_Icc_left ham
  have hqleft : IntervalIntegrable q volume a m := hq.mono_set (by
    rw [uIcc_of_le ham, uIcc_of_le hab]
    exact hleft)
  have hqright : IntervalIntegrable q volume m b := hq.mono_set (by
    rw [uIcc_of_le hmb, uIcc_of_le hab]
    exact hright)
  have hpqleft := hqleft.continuousOn_mul (by
    simpa only [uIcc_of_le ham] using hp.mono hleft)
  have hpqright := hqright.continuousOn_mul (by
    simpa only [uIcc_of_le hmb] using hp.mono hright)
  have hn := initialCell_negativePart_intervalIntegrable hq
  have hnleft := initialCell_negativePart_intervalIntegrable hqleft
  have hnegativeLeft : (∫ x in a..m, max (-q x) 0) ≤ N := by
    exact (intervalIntegral.integral_mono_interval le_rfl ham hmb
      (Filter.Eventually.of_forall fun _ => le_max_right _ _) hn).trans hnegative
  have hlower : -M * N ≤ ∫ x in a..m, p x * q x := by
    calc
      _ ≤ -M * ∫ x in a..m, max (-q x) 0 :=
        mul_le_mul_of_nonpos_left hnegativeLeft (neg_nonpos.mpr hM)
      _ = ∫ x in a..m, -M * max (-q x) 0 :=
        (intervalIntegral.integral_const_mul _ _).symm
      _ ≤ _ := by
        apply intervalIntegral.integral_mono_on ham (hnleft.const_mul _) hpqleft
        intro x hx
        have hx' := hleft hx
        have hqneg : -(max (-q x) 0) ≤ q x := by linarith [le_max_left (-q x) 0]
        have h₁ := mul_le_mul_of_nonneg_left hqneg (hpos x hx')
        have h₂ := mul_le_mul_of_nonneg_right (hbound x hx') (le_max_right (-q x) 0)
        nlinarith
  have hupperIntegral : A * (∫ x in m..b, p x) ≤ ∫ x in m..b, p x * q x := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hmb
      (((hp.mono hright).intervalIntegrable_of_Icc hmb).const_mul _) hpqright
    intro x hx
    simpa only [mul_comm A] using mul_le_mul_of_nonneg_left (hupper x hx) (hpos x (hright hx))
  have hsum := intervalIntegral.integral_add_adjacent_intervals hpqleft hpqright
  linarith

end GapFamily.Construction
