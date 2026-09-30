import GapFamily.Analytic.Foundation.Vacuum
import GapFamily.Analytic.Foundation.VacuumFactor
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Continuous-spin primary reference

The density is the literal real-spin extension of the denominator-one vacuum
reference in Section 5. The transform is an ordinary Bochner integral of that
density over the physical energy-spin cone, with the paper's inverse-square-root
reference measure written explicitly.
-/

noncomputable section

open MeasureTheory Set
open GapFamily.Analytic

namespace BTZEntropy

/-- The real-spin extension of the same leading density used in the construction. -/
def continuousSpinLeading (a E J : ℝ) : ℝ :=
  2 * vacuumDifference a (E + J) * vacuumDifference a (E - J)

/-- This real-spin extension agrees exactly with the existing integer-spin density. -/
theorem continuousSpinLeading_int {a E : ℝ} (J : ℤ)
    (ha : 2 ≤ a) (hE : |(J : ℝ)| ≤ E) :
    continuousSpinLeading a E J = vacuumLeading a E J := by
  rw [vacuumLeading_eq_cosh a E J ha hE]
  rfl

/-- The open physical cone; its boundary has zero two-dimensional volume. -/
def referenceCone : Set (ℝ × ℝ) := {p | |p.2| < p.1}

/-- The primary reference density relative to ordinary `dE dJ`. -/
def referencePrimaryDensity (a E J : ℝ) : ℝ :=
  continuousSpinLeading a E J / Real.sqrt (E ^ 2 - J ^ 2)

theorem referencePrimaryDensity_nonneg {a : ℝ} (ha : 2 ≤ a) (E J : ℝ) :
    0 ≤ referencePrimaryDensity a E J := by
  exact div_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) (vacuumDifference_nonneg ha))
      (vacuumDifference_nonneg ha)) (Real.sqrt_nonneg _)

/-- The primary reference thermal transform in shifted energy. -/
def referencePrimaryTransform (a β : ℝ) : ℝ :=
  ∫ p : ℝ × ℝ in referenceCone,
    Real.exp (-β * p.1) * referencePrimaryDensity a p.1 p.2

@[fun_prop] theorem measurable_continuousSpinLeading (a : ℝ) :
    Measurable (fun p : ℝ × ℝ => continuousSpinLeading a p.1 p.2) := by
  unfold continuousSpinLeading vacuumDifference
  fun_prop

@[fun_prop] theorem measurable_referencePrimaryDensity (a : ℝ) :
    Measurable (fun p : ℝ × ℝ => referencePrimaryDensity a p.1 p.2) := by
  unfold referencePrimaryDensity
  exact (measurable_continuousSpinLeading a).div (by fun_prop)

@[measurability] theorem measurableSet_referenceCone : MeasurableSet referenceCone := by
  exact measurableSet_lt (by fun_prop) (by fun_prop)

/-- The literal factor of two in the density compensates the lightcone Jacobian. -/
theorem referencePrimaryDensity_lightcone (a u v : ℝ) (hu : 0 ≤ u) :
    referencePrimaryDensity a ((u + v) / 2) ((u - v) / 2) =
      2 * (vacuumDifference a u / Real.sqrt u) *
        (vacuumDifference a v / Real.sqrt v) := by
  have hplus : (u + v) / 2 + (u - v) / 2 = u := by ring
  have hminus : (u + v) / 2 - (u - v) / 2 = v := by ring
  have hsquare : ((u + v) / 2) ^ 2 - ((u - v) / 2) ^ 2 = u * v := by ring
  simp only [referencePrimaryDensity, continuousSpinLeading, hplus, hminus, hsquare,
    Real.sqrt_mul hu]
  ring

/-- Thermal weighting also separates in the two positive chiral coordinates. -/
theorem referencePrimaryThermal_lightcone (a β u v : ℝ) (hu : 0 ≤ u) :
    Real.exp (-β * ((u + v) / 2)) *
        referencePrimaryDensity a ((u + v) / 2) ((u - v) / 2) =
      2 * (Real.exp (-β * u / 2) * (vacuumDifference a u / Real.sqrt u)) *
        (Real.exp (-β * v / 2) * (vacuumDifference a v / Real.sqrt v)) := by
  rw [referencePrimaryDensity_lightcone a u v hu,
    show -β * ((u + v) / 2) = -β * u / 2 + -β * v / 2 by ring, Real.exp_add]
  ring

/-- Fubini identifies the cone integral with the paper's literal energy-then-spin integral. -/
theorem integral_referenceCone_eq_iterated (f : ℝ × ℝ → ℝ)
    (hf : IntegrableOn f referenceCone) :
    (∫ p in referenceCone, f p) =
      ∫ E in Ioi (0 : ℝ), ∫ J in Ioo (-E) E, f (E, J) := by
  have hfi : Integrable (referenceCone.indicator f) :=
    (integrable_indicator_iff measurableSet_referenceCone).2 hf
  rw [← integral_indicator measurableSet_referenceCone,
    Measure.volume_eq_prod, integral_prod _ (by simpa [Measure.volume_eq_prod] using hfi),
    ← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards [] with E
  by_cases hE : 0 < E
  · rw [Set.indicator_of_mem (show E ∈ Ioi (0 : ℝ) from hE), ← integral_indicator measurableSet_Ioo]
    apply integral_congr_ae
    filter_upwards [] with J
    have hcone : (E, J) ∈ referenceCone ↔ J ∈ Ioo (-E) E := by
      simp only [referenceCone, Set.mem_ofPred_eq, Set.mem_Ioo, abs_lt]
    by_cases hJ : J ∈ Ioo (-E) E
    · rw [Set.indicator_of_mem (hcone.mpr hJ), Set.indicator_of_mem hJ]
    · rw [Set.indicator_of_notMem (mt hcone.mp hJ), Set.indicator_of_notMem hJ]
  · rw [Set.indicator_of_notMem (show E ∉ Ioi (0 : ℝ) from hE)]
    have hzero : (fun J => referenceCone.indicator f (E, J)) = 0 := by
      funext J
      apply Set.indicator_of_notMem
      intro h
      exact hE (lt_of_le_of_lt (abs_nonneg J) h)
    simp [hzero]

end BTZEntropy
