import Mathlib.Analysis.InnerProductSpace.StarOrder

namespace GapFamily.Analytic.PositiveContractionProduct

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Commuting positive bounded operators have a positive product. Keeping
the Hilbert space abstract here also fixes the scalar restriction instances. -/
theorem isPositive_mul_of_commute [CompleteSpace H] {A B : H →L[ℂ] H}
    (hA : A.IsPositive) (hB : B.IsPositive) (hcomm : Commute A B) :
    (A * B).IsPositive :=
  ContinuousLinearMap.nonneg_iff_isPositive.mp <|
    Commute.mul_nonneg (ContinuousLinearMap.nonneg_iff_isPositive.mpr hA)
      (ContinuousLinearMap.nonneg_iff_isPositive.mpr hB) hcomm

/-- The ordered prefix product, with each new factor appended on the right. -/
noncomputable def orderedProduct (R : ℕ → H →L[ℂ] H) : ℕ → H →L[ℂ] H
  | 0 => 1
  | n + 1 => orderedProduct R n * R n

@[simp] theorem orderedProduct_zero (R : ℕ → H →L[ℂ] H) :
    orderedProduct R 0 = 1 := rfl

@[simp] theorem orderedProduct_succ (R : ℕ → H →L[ℂ] H) (n : ℕ) :
    orderedProduct R (n + 1) = orderedProduct R n * R n := rfl

/-- Every ordered prefix commutes with every member of a pairwise commuting family. -/
theorem orderedProduct_commute (R : ℕ → H →L[ℂ] H)
    (hcomm : Pairwise (fun i j => Commute (R i) (R j))) (n m : ℕ) :
    Commute (orderedProduct R n) (R m) := by
  induction n with
  | zero => exact Commute.one_left _
  | succ n ih =>
      apply ih.mul_left
      by_cases h : n = m
      · subst m
        exact Commute.refl _
      · exact hcomm h

/-- Products of pairwise commuting positive operators are positive. -/
theorem orderedProduct_isPositive [CompleteSpace H] (R : ℕ → H →L[ℂ] H)
    (hpos : ∀ n, (R n).IsPositive)
    (hcomm : Pairwise (fun i j => Commute (R i) (R j))) (n : ℕ) :
    (orderedProduct R n).IsPositive := by
  induction n with
  | zero => exact ContinuousLinearMap.isPositive_one
  | succ n ih =>
      exact ContinuousLinearMap.nonneg_iff_isPositive.mp <|
        Commute.mul_nonneg (ContinuousLinearMap.nonneg_iff_isPositive.mpr ih)
          (ContinuousLinearMap.nonneg_iff_isPositive.mpr (hpos n))
          (orderedProduct_commute R hcomm n n)

/-- Ordered products of contractions are contractions, independently of positivity
or commutation. This also includes the zero-dimensional Hilbert space. -/
theorem orderedProduct_norm_le_one (R : ℕ → H →L[ℂ] H)
    (hnorm : ∀ n, ‖R n‖ ≤ 1) (n : ℕ) :
    ‖orderedProduct R n‖ ≤ 1 := by
  induction n with
  | zero => exact ContinuousLinearMap.norm_id_le
  | succ n ih =>
      calc
        ‖orderedProduct R (n + 1)‖ ≤ ‖orderedProduct R n‖ * ‖R n‖ := norm_mul_le _ _
        _ ≤ 1 * 1 := mul_le_mul ih (hnorm n) (norm_nonneg _) zero_le_one
        _ = 1 := one_mul _

end GapFamily.Analytic.PositiveContractionProduct
