import GapFamily.Analytic.Spatial.SpatialOrbitResolventRecurrence
import GapFamily.Analytic.Spatial.SpatialOrbitStrongApproximation
import GapFamily.Analytic.Modular.ModularPositiveResolventRecurrence

/-! Positivity of the actual spatial orbit integral operator, from its genuine
resolvent recurrence and proved strong approximate identity. -/

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open Filter ModularPositiveResolvent
open scoped Topology ComplexOrder

/-- Actual normalized spatial operators are positive for every real s>1. -/
theorem normalizedOrbitOperator_isPositive (s : ℝ) (hs : 1 < s) :
    (normalizedOrbitOperator s hs).IsPositive := by
  let q : ℕ → ℝ := fun n => s + (n : ℝ)
  have hq (n : ℕ) : 1 < q n := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    dsimp [q]
    linarith
  have hqLim : Tendsto q atTop atTop := by
    simpa only [q, add_comm] using
      (tendsto_atTop_add_const_right atTop s tendsto_natCast_atTop_atTop)
  have hrec (n : ℕ) : normalizedOrbitOperator (q n) (hq n) =
      resolventFactor ((s + (n : ℝ)) * (s + (n : ℝ) - 1)) *
        normalizedOrbitOperator (q (n + 1)) (hq (n + 1)) := by
    simpa only [q, Nat.cast_add, Nat.cast_one, add_assoc] using
      normalizedOrbitOperator_resolvent_recurrence (q n) (hq n)
  have hp := isPositive_of_quadratic_recurrence s hs
    (fun n => normalizedOrbitOperator (q n) (hq n)) hrec
    (normalizedOrbitOperator_tendsto q hq hqLim)
  simpa only [q, Nat.cast_zero, add_zero] using hp

/-- Positivity of the literal unnormalized L² integral operator. -/
theorem spatialOrbitIntegralOperator_isPositive (s : ℝ) (hs : 1 < s) :
    (spatialOrbitIntegralOperator s hs).IsPositive := by
  have ha : 0 ≤ (((Real.pi / (s - 1) : ℝ)) : ℂ) :=
    (RCLike.ofReal_nonneg (K := ℂ)).mpr (div_nonneg Real.pi_pos.le (by linarith))
  have hp := (normalizedOrbitOperator_isPositive s hs).smul_of_nonneg ha
  have he : (((Real.pi / (s - 1) : ℝ)) : ℂ) • normalizedOrbitOperator s hs =
      spatialOrbitIntegralOperator s hs := by
    rw [normalizedOrbitOperator, smul_smul]
    have hc : (((Real.pi / (s - 1) : ℝ)) : ℂ) * ((((s - 1) / Real.pi : ℝ)) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul]
      have hreal : Real.pi / (s - 1) * ((s - 1) / Real.pi) = 1 := by
        field_simp [Real.pi_ne_zero, sub_ne_zero.mpr hs.ne']
      rw [hreal, Complex.ofReal_one]
    rw [hc, one_smul]
  rwa [he] at hp

end GapFamily.Analytic.SpatialPoint
