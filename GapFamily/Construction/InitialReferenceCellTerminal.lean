import GapFamily.Construction.CellCoordinateIntegral
import GapFamily.Construction.InitialReferenceTerminalDensity

/-!
# Terminal mass of an initial reference cell

The physical edge factor cancels the singular reference density. Its lower
bound on a unit terminal interval yields an ordinary mass bound, and an
explicit threshold makes that mass greater than one.
-/

noncomputable section

open Set MeasureTheory Real
open GapFamily.Analytic

namespace GapFamily.Construction

/-- A constant lower bound for the weighted numerator gives the same lower
bound for the physical mass of a unit interval. -/
theorem initialReferenceCell_terminal_mass_of_weighted_lower
    (j : ℤ) {U A : ℝ} (hjU : |(j : ℝ)| ≤ U)
    (q : ℝ → ℝ)
    (hq : IntegrableOn q (Ioo U (U + 1)) (referenceMeasure j))
    (hbound : ∀ E ∈ Icc U (U + 1), A ≤ referenceDensity j E * q E) :
    A ≤ ∫ E in Ioo U (U + 1), q E ∂referenceMeasure j := by
  have hUU : U ≤ U + 1 := by linarith
  have hint : IntervalIntegrable (fun E => referenceDensity j E * q E)
      volume U (U + 1) := by
    apply (intervalIntegrable_iff_integrableOn_Ioo_of_le hUU).2
    exact (integrableOn_referenceMeasure_Ioo_iff j hjU q).1 hq
  calc
    A = ∫ E in U..(U + 1), A := by simp
    _ ≤ ∫ E in U..(U + 1), referenceDensity j E * q E :=
      intervalIntegral.integral_mono_on hUU intervalIntegrable_const hint hbound
    _ = ∫ E in Ioo U (U + 1), referenceDensity j E * q E := by
      rw [intervalIntegral.integral_of_le hUU, integral_Ioc_eq_integral_Ioo]
    _ = ∫ E in Ioo U (U + 1), q E ∂referenceMeasure j :=
      (integral_referenceMeasure_Ioo j hjU q).symm

/-- The physical edge-times-exponential lower bound supplies at least
`c * U / 2` ordinary mass on the terminal unit interval. -/
theorem initialReferenceCell_terminal_mass_lower
    (j : ℤ) {a U c : ℝ} (ha : 0 ≤ a) (hU : 1 ≤ U)
    (hjU : |(j : ℝ)| ≤ U / 16) (hc : 0 ≤ c)
    (q : ℝ → ℝ)
    (hq : IntegrableOn q (Ioo U (U + 1)) (referenceMeasure j))
    (hbound : ∀ E ∈ Icc U (U + 1),
      c * (E ^ 2 - (j : ℝ) ^ 2) * exp (8 * sqrt (a * E)) ≤ q E) :
    c * U / 2 ≤ ∫ E in Ioo U (U + 1), q E ∂referenceMeasure j := by
  apply initialReferenceCell_terminal_mass_of_weighted_lower j
    (by linarith) q hq
  intro E hE
  exact initialReference_terminal_weighted_density_lower j hc ha hU hjU hE.1
    (hbound E hE)

/-- An explicit endpoint threshold makes the ordinary terminal mass exceed
one, as required for choosing an integer-mass initial endpoint. -/
theorem initialReferenceCell_terminal_mass_gt_one
    (j : ℤ) {a U c : ℝ} (ha : 0 ≤ a) (hU : 1 ≤ U)
    (hjU : |(j : ℝ)| ≤ U / 16) (hc : 0 < c) (hlarge : 2 / c < U)
    (q : ℝ → ℝ)
    (hq : IntegrableOn q (Ioo U (U + 1)) (referenceMeasure j))
    (hbound : ∀ E ∈ Icc U (U + 1),
      c * (E ^ 2 - (j : ℝ) ^ 2) * exp (8 * sqrt (a * E)) ≤ q E) :
    1 < ∫ E in Ioo U (U + 1), q E ∂referenceMeasure j := by
  have hlarge' := (div_lt_iff₀ hc).mp hlarge
  exact lt_of_lt_of_le (by nlinarith : 1 < c * U / 2)
    (initialReferenceCell_terminal_mass_lower j ha hU hjU hc.le q hq hbound)

end GapFamily.Construction
