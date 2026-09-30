import Mathlib.NumberTheory.ZetaValues

noncomputable section
namespace GapFamily.Analytic.SelbergFiniteBound

/-- Every finite sub-sum of the ordinary reciprocal-square series has the
actual Basel bound; the totalized zero term is zero. -/
theorem sum_reciprocal_sq_le_zeta_two (s : Finset ℕ) :
    (∑ d ∈ s, (1 : ℝ) / (d : ℝ) ^ 2) ≤ Real.pi ^ 2 / 6 := by
  exact sum_le_hasSum s (fun n _ => by positivity) hasSum_zeta_two

end GapFamily.Analytic.SelbergFiniteBound
