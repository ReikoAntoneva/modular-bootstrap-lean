import GapFamily.Analytic.Foundation.PositiveRecurrenceLimit

/-! A bounded operator that commutes with every contraction factor also commutes
with the operator determined by the recurrence and its strong tail limit. -/

noncomputable section
namespace GapFamily.Analytic.CommutingRecurrenceLimit
open Filter
open scoped Topology
open PositiveContractionProduct PositiveRecurrenceLimit

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A fixed operator commuting with every factor commutes with each ordered prefix. -/
theorem commute_orderedProduct (R : ℕ → H →L[ℂ] H) (B : H →L[ℂ] H)
    (hcomm : ∀ n, Commute B (R n)) (n : ℕ) :
    Commute B (orderedProduct R n) := by
  induction n with
  | zero => exact Commute.one_right B
  | succ n ih => exact ih.mul_right (hcomm n)

/-- Commutation with a fixed bounded operator is preserved by strong convergence. -/
theorem commute_of_strong_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    (A : ι → H →L[ℂ] H) (T B : H →L[ℂ] H)
    (hcomm : ∀ i, Commute B (A i))
    (hlim : ∀ x, Tendsto (fun i => A i x) l (𝓝 (T x))) :
    Commute B T := by
  change B * T = T * B
  ext x
  change B (T x) = T (B x)
  have hleft : Tendsto (fun i => B (A i x)) l (𝓝 (B (T x))) :=
    (B.continuous.tendsto _).comp (hlim x)
  have heq : (fun i => B (A i x)) = (fun i => A i (B x)) := by
    funext i
    exact congrArg (fun S : H →L[ℂ] H => S x) (hcomm i).eq
  rw [heq] at hleft
  exact tendsto_nhds_unique hleft (hlim (B x))

/-- No commutation hypothesis on `T n` is required: contraction, the recurrence,
and the strong tail limit transfer the factors' commutation to `T 0`. -/
theorem commute_of_contraction_recurrence
    (T R : ℕ → H →L[ℂ] H) (B : H →L[ℂ] H)
    (hcomm : ∀ n, Commute B (R n))
    (hnorm : ∀ n, ‖R n‖ ≤ 1)
    (hrec : ∀ n, T n = R n * T (n + 1))
    (htail : ∀ x, Tendsto (fun n => T n x) atTop (𝓝 x)) :
    Commute B (T 0) :=
  commute_of_strong_tendsto (orderedProduct R) (T 0) B
    (commute_orderedProduct R B hcomm)
    (orderedProduct_tendsto_of_recurrence T R hnorm hrec htail)

end GapFamily.Analytic.CommutingRecurrenceLimit
