import GapFamily.Analytic.Foundation.PositiveContractionProduct
import GapFamily.Analytic.Foundation.PositiveStrongLimit

/-! A positive commuting contraction recurrence and a genuine strong tail limit
force positivity of the initial bounded operator. -/

noncomputable section
namespace GapFamily.Analytic.PositiveRecurrenceLimit
open Filter
open scoped Topology
open PositiveContractionProduct PositiveStrongLimit

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The recurrence is iterated as an actual ordered operator product. -/
theorem eq_orderedProduct_mul_of_recurrence (T R : ℕ → H →L[ℂ] H)
    (hrec : ∀ n, T n = R n * T (n + 1)) (n : ℕ) :
    T 0 = orderedProduct R n * T n := by
  induction n with
  | zero => simp
  | succ n hn =>
    calc
      T 0 = orderedProduct R n * T n := hn
      _ = orderedProduct R n * (R n * T (n + 1)) := by rw [hrec n]
      _ = orderedProduct R (n + 1) * T (n + 1) := by
        rw [orderedProduct_succ, mul_assoc]

/-- Contraction of the iterated product transfers the strong tail limit to
the finite products, without requiring convergence in operator norm. -/
theorem orderedProduct_tendsto_of_recurrence (T R : ℕ → H →L[ℂ] H)
    (hnorm : ∀ n, ‖R n‖ ≤ 1)
    (hrec : ∀ n, T n = R n * T (n + 1))
    (htail : ∀ x, Tendsto (fun n => T n x) atTop (𝓝 x)) (x : H) :
    Tendsto (fun n => orderedProduct R n x) atTop (𝓝 (T 0 x)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hzero : Tendsto (fun n => ‖x - T n x‖) atTop (𝓝 0) := by
    simpa using ((tendsto_const_nhds (x := x)).sub (htail x)).norm
  apply squeeze_zero (fun n => norm_nonneg _) _ hzero
  intro n
  have hfactor := eq_orderedProduct_mul_of_recurrence T R hrec n
  have hdiff : orderedProduct R n x - T 0 x = orderedProduct R n (x - T n x) := by
    rw [hfactor]
    simp only [mul_apply_eq_comp, map_sub]
  rw [hdiff]
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_of_le_one_left (norm_nonneg _) (orderedProduct_norm_le_one R hnorm n))

/-- Positivity follows from explicit positive commuting contraction factors,
the stated recurrence, and a strong tail limit to the identity.  No positivity
or self-adjointness hypothesis on any `T n` is needed. -/
theorem isPositive_of_positive_contraction_recurrence [CompleteSpace H]
    (T R : ℕ → H →L[ℂ] H)
    (hpos : ∀ n, (R n).IsPositive)
    (hcomm : Pairwise (fun i j => Commute (R i) (R j)))
    (hnorm : ∀ n, ‖R n‖ ≤ 1)
    (hrec : ∀ n, T n = R n * T (n + 1))
    (htail : ∀ x, Tendsto (fun n => T n x) atTop (𝓝 x)) :
    (T 0).IsPositive :=
  isPositive_of_strong_tendsto (orderedProduct R) (T 0)
    (orderedProduct_isPositive R hpos hcomm)
    (orderedProduct_tendsto_of_recurrence T R hnorm hrec htail)

end GapFamily.Analytic.PositiveRecurrenceLimit
