import GapFamily.Analytic.Modular.ModularPositiveResolventOrder
import GapFamily.Analytic.Modular.ModularPositiveResolventCommute
import GapFamily.Analytic.Foundation.PositiveRecurrenceLimit

/-! The actual modular resolvent factors instantiate the abstract positivity
argument. The operator recurrence and strong tail limit remain explicit. -/

noncomputable section
namespace GapFamily.Analytic.ModularPositiveResolvent
open Filter
open scoped Topology

/-- Only recurrence and strong convergence remain to be supplied: positivity,
contraction, and commutation of the actual modular factors are proved. -/
theorem isPositive_of_recurrence (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (T : ℕ → ModularHilbert →L[ℂ] ModularHilbert)
    (hrec : ∀ n, T n = resolventFactor (r n) * T (n + 1))
    (htail : ∀ x, Tendsto (fun n => T n x) atTop (𝓝 x)) :
    (T 0).IsPositive := by
  apply PositiveRecurrenceLimit.isPositive_of_positive_contraction_recurrence
    T (fun n => resolventFactor (r n))
  · exact fun n => resolventFactor_isPositive (r n) (hr n)
  · intro i j _
    exact resolventFactor_commute (r i) (hr i) (r j) (hr j)
  · exact fun n => resolventFactor_norm_le_one (r n) (hr n)
  · exact hrec
  · exact htail

/-- The exact quadratic coefficient for the normalized spatial recurrence,
using the actual unbounded modular Laplacian resolvent factors. -/
theorem isPositive_of_quadratic_recurrence (s : ℝ) (hs : 1 < s)
    (T : ℕ → ModularHilbert →L[ℂ] ModularHilbert)
    (hrec : ∀ n, T n = resolventFactor
      ((s + (n : ℝ)) * (s + (n : ℝ) - 1)) * T (n + 1))
    (htail : ∀ x, Tendsto (fun n => T n x) atTop (𝓝 x)) :
    (T 0).IsPositive := by
  apply isPositive_of_recurrence (fun n => (s + (n : ℝ)) * (s + (n : ℝ) - 1))
    _ T hrec htail
  intro n
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  exact mul_pos (by linarith) (by linarith)

end GapFamily.Analytic.ModularPositiveResolvent
