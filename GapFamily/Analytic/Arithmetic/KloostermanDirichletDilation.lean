import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.Tactic

/-!
# Dilation of a Dirichlet series

Inserting zero coefficients away from multiples of a positive integer rescales
the actual Dirichlet series. The summability equivalence is proved separately
from the identity between the totalized sums.
-/

noncomputable section

namespace GapFamily.Analytic

/-- Extend a sequence from the multiples of d, with zero elsewhere. -/
def dirichletDilation (d : ℕ) (f : ℕ → ℂ) (c : ℕ) : ℂ :=
  if d ∣ c then f (c / d) else 0

@[simp] theorem dirichletDilation_mul (d : ℕ) (hd : 0 < d)
    (f : ℕ → ℂ) (n : ℕ) : dirichletDilation d f (d * n) = f n := by
  simp [dirichletDilation, Nat.mul_div_cancel_left n hd]

/-- On the multiples of d, the Dirichlet term has exactly the expected scale. -/
theorem term_dirichletDilation_mul (d : ℕ) (hd : 0 < d)
    (f : ℕ → ℂ) (s : ℂ) (n : ℕ) :
    LSeries.term (dirichletDilation d f) s (d * n) =
      (d : ℂ) ^ (-s) * LSeries.term f s n := by
  by_cases hn : n = 0
  · simp [hn]
  · rw [LSeries.term_of_ne_zero (mul_ne_zero (Nat.ne_of_gt hd) hn),
      LSeries.term_of_ne_zero hn, dirichletDilation_mul d hd,
      Nat.cast_mul, Complex.natCast_mul_natCast_cpow, Complex.cpow_neg]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

/-- Every term outside the multiples of d is genuinely zero. -/
theorem term_dirichletDilation_eq_zero (d : ℕ) (f : ℕ → ℂ)
    (s : ℂ) (n : ℕ) (hn : ¬d ∣ n) :
    LSeries.term (dirichletDilation d f) s n = 0 := by
  simp [LSeries.term, dirichletDilation, hn]

private theorem dilation_injective (d : ℕ) (hd : 0 < d) :
    Function.Injective (fun n : ℕ => d * n) := by
  intro a b hab
  exact Nat.eq_of_mul_eq_mul_left hd hab

private theorem dilation_term_off_range (d : ℕ) (f : ℕ → ℂ) (s : ℂ)
    (n : ℕ) (hn : n ∉ Set.range (fun k : ℕ => d * k)) :
    LSeries.term (dirichletDilation d f) s n = 0 := by
  apply term_dirichletDilation_eq_zero
  rintro ⟨k, rfl⟩
  exact hn ⟨k, rfl⟩

/-- Dilation preserves and reflects genuine absolute convergence. -/
theorem lSeriesSummable_dirichletDilation_iff (d : ℕ) (hd : 0 < d)
    (f : ℕ → ℂ) (s : ℂ) :
    LSeriesSummable (dirichletDilation d f) s ↔ LSeriesSummable f s := by
  unfold LSeriesSummable
  rw [← (dilation_injective d hd).summable_iff (dilation_term_off_range d f s)]
  change Summable (fun n => LSeries.term (dirichletDilation d f) s (d * n)) ↔ _
  simp_rw [term_dirichletDilation_mul d hd]
  apply summable_mul_left_iff
  exact Complex.cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)))

/-- The dilated series converges whenever the original series converges. -/
theorem lSeriesSummable_dirichletDilation (d : ℕ) (hd : 0 < d)
    (f : ℕ → ℂ) (s : ℂ) (hf : LSeriesSummable f s) :
    LSeriesSummable (dirichletDilation d f) s :=
  (lSeriesSummable_dirichletDilation_iff d hd f s).mpr hf

/-- The exact dilation identity, valid also for the totalized values. -/
theorem lSeries_dirichletDilation (d : ℕ) (hd : 0 < d)
    (f : ℕ → ℂ) (s : ℂ) :
    LSeries (dirichletDilation d f) s = (d : ℂ) ^ (-s) * LSeries f s := by
  unfold LSeries
  rw [← (dilation_injective d hd).tsum_eq]
  · simp_rw [term_dirichletDilation_mul d hd]
    exact tsum_mul_left
  · intro n hn
    by_contra hnot
    exact hn (dilation_term_off_range d f s n hnot)

/-- A convergent original series supplies the actual sum of its dilation. -/
theorem lSeriesHasSum_dirichletDilation (d : ℕ) (hd : 0 < d)
    (f : ℕ → ℂ) (s : ℂ) (hf : LSeriesSummable f s) :
    LSeriesHasSum (dirichletDilation d f) s ((d : ℂ) ^ (-s) * LSeries f s) := by
  rw [LSeriesHasSum_iff]
  exact ⟨lSeriesSummable_dirichletDilation d hd f s hf,
    lSeries_dirichletDilation d hd f s⟩

end GapFamily.Analytic
