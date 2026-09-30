import GapFamily.Construction.RealInitialState
import GapFamily.Construction.MarkerReferenceDensityBound

/-! The real initial state inherits the actual reference half-budget and
the finite initial-repair eighth-budget on its unprocessed region. -/

noncomputable section

open Real
open scoped BigOperators

namespace GapFamily.Construction

open Analytic

variable (S : Finset ℤ) (b U : ℝ) (k : ℕ) (q : ℤ → ℝ → ℝ)
  (cells : ∀ J : S, InitialReferenceCell J (max b |(J : ℝ)|) U k (q J))
  (B0 : ℝ) (hB0 : 1 ≤ B0) (hcut : ∀ J, (cells J).right < B0)

/-- The numerical estimates concern the same density and finite sum stored
in the initial state. The marker is free to lie below the density cutoff. -/
theorem realInitialRepairState_error_le_five_eighths (a T : ℝ)
    (hTU : T ≤ U) (hcover : ∀ j : ℤ, |(j : ℝ)| ≤ T → j ∈ S)
    (href : ∀ (j : ℤ) (e : ℝ), max T |(j : ℝ)| ≤ e →
      |q j e - vacuumLeading a e j| ≤ exp (7 * sqrt (a * e)) / 2)
    (hrepair : ∀ (j : ℤ) (e : ℝ), |(j : ℝ)| ≤ e →
      (∑ J : S, |if B0 < e then (cells J).exteriorNumerator B0 hB0 j e else 0|) ≤
        exp (7 * sqrt (a * e)) / 8)
    (j : ℤ) (e : ℝ)
    (he : (realInitialRepairState S b U k q cells B0 hB0 hcut).front j ≤ e) :
    |(realInitialRepairState S b U k q cells B0 hB0 hcut).numerator j e -
        vacuumLeading a e j| ≤ 5 * exp (7 * sqrt (a * e)) / 8 := by
  have hfront := (max_le_realInitialRepairFront_of_cover S b U k q cells
    T hTU hcover j).trans he
  exact realInitialRepairNumerator_error_le_five_eighths S b U k q cells B0 hB0
    (fun j e => vacuumLeading a e j) (fun _ e => exp (7 * sqrt (a * e))) j e he
    (href j e hfront) (hrepair j e ((le_max_right _ _).trans hfront))

/-- The same error reserve gives the positive physical-edge factor used by
the tail construction. -/
theorem realInitialRepairState_density_lower {a : ℝ} (ha : 100 ≤ a)
    (herror : ∀ j e, (realInitialRepairState S b U k q cells B0 hB0 hcut).front j ≤ e →
      |(realInitialRepairState S b U k q cells B0 hB0 hcut).numerator j e -
        vacuumLeading a e j| ≤ 5 * exp (7 * sqrt (a * e)) / 8)
    (j : ℤ) (e : ℝ)
    (he : (realInitialRepairState S b U k q cells B0 hB0 hcut).front j ≤ e)
    (hedge : |(j : ℝ)| + 1 ≤ e) :
    (π ^ 4 / 625) * (e ^ 2 - (j : ℝ) ^ 2) * exp (8 * sqrt (a * e)) ≤
      (realInitialRepairState S b U k q cells B0 hB0 hcut).numerator j e := by
  apply referenceDensity_lower_of_vacuum_error j ha hedge
    ((realInitialRepairState S b U k q cells B0 hB0 hcut).numerator j)
  have h := herror j e he
  have hp := exp_pos (7 * sqrt (a * e))
  linarith

end GapFamily.Construction
