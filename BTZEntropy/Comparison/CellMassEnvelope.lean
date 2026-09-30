import BTZEntropy.Comparison.DensityErrorBand
import GapFamily.Construction.ThermalEnvelope

/-!
# Bounded-energy mass of the signed-cell envelope

Every actual current cell is controlled by the sum of the leading vacuum
density and the `exp (7 sqrt (a E))` construction error. Integrating this
positive envelope costs only a quadratic energy prefactor at the unchanged
exponential rate `exp (4 pi sqrt (a X))`, including all spin openings.
-/

noncomputable section

open Set MeasureTheory Real
open GapFamily.Analytic GapFamily.Construction
open scoped BigOperators

namespace BTZEntropy.Comparison

/-- Ordinary envelope mass on one physical reference row. -/
def cellEnvelopeRowMass (a T X : ℝ) (j : ℤ) : ℝ :=
  ∫ e in Ioo (max T |(j : ℝ)|) X, tailEnvelopeNumerator a e j ∂referenceMeasure j

/-- The complete finite-energy envelope includes every integer spin. -/
def cellEnvelopeMass (a T X : ℝ) : ℝ := ∑' j : ℤ, cellEnvelopeRowMass a T X j

/-- The old thermal envelope has the exact leading exponential rate on a
finite band; the lower error exponent does not change it. -/
theorem tailEnvelopeNumerator_le_band {a X e : ℝ} (j : ℤ)
    (ha : 100 ≤ a) (hj : |(j : ℝ)| ≤ e) (heX : e ≤ X) :
    tailEnvelopeNumerator a e j ≤ 3 * exp (4 * π * sqrt (a * X)) := by
  apply (tailEnvelopeNumerator_le_exp a e j ha hj).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply exp_le_exp.mpr
  have hs : sqrt (a * e) ≤ sqrt (a * X) :=
    sqrt_le_sqrt (mul_le_mul_of_nonneg_left heX (by linarith))
  have hm := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 4 * π)
  simpa only [sqrt_mul (by linarith : 0 ≤ a), mul_assoc] using hm

/-- The physical band is finite even when its endpoint is a spin opening,
so every continuous envelope is an ordinary integrable density there. -/
theorem integrable_cellEnvelopeRow {a T X : ℝ} (j : ℤ) (hT : 1 ≤ T) :
    IntegrableOn (fun e => tailEnvelopeNumerator a e j)
      (Ioo (max T |(j : ℝ)|) X) (referenceMeasure j) := by
  by_cases hTX : max T |(j : ℝ)| ≤ X
  · exact integrableOn_tailEnvelopeNumerator a j
      (hT.trans (le_max_left _ _)) (le_max_right _ _) hTX
  · simp [Ioo_eq_empty_of_le (le_of_not_ge hTX)]

theorem cellEnvelopeRowMass_nonneg {a T X : ℝ} (j : ℤ) (ha : 100 ≤ a) :
    0 ≤ cellEnvelopeRowMass a T X j := by
  apply setIntegral_nonneg measurableSet_Ioo
  intro e he
  exact tailEnvelopeNumerator_nonneg a e j (by linarith)
    ((le_max_right _ _).trans he.1.le)

/-- One row costs one power of the upper energy, uniformly in spin. -/
theorem cellEnvelopeRowMass_le {a T X : ℝ} (j : ℤ)
    (ha : 100 ≤ a) (hT : 1 ≤ T) (hX : 0 ≤ X) :
    cellEnvelopeRowMass a T X j ≤ 3 * X * exp (4 * π * sqrt (a * X)) := by
  let _ := densityErrorBand_isFiniteMeasure j hT (V := X)
  calc
    _ ≤ ∫ _e in Ioo (max T |(j : ℝ)|) X,
        3 * exp (4 * π * sqrt (a * X)) ∂referenceMeasure j := by
      exact setIntegral_mono_on (integrable_cellEnvelopeRow j hT) (integrable_const _)
        measurableSet_Ioo (fun e he => tailEnvelopeNumerator_le_band j ha
          ((le_max_right _ _).trans he.1.le) he.2.le)
    _ = (referenceMeasure j).real (Ioo (max T |(j : ℝ)|) X) *
        (3 * exp (4 * π * sqrt (a * X))) := by simp
    _ ≤ X * (3 * exp (4 * π * sqrt (a * X))) :=
      mul_le_mul_of_nonneg_right (densityErrorBand_mass_le j hT hX) (by positivity)
    _ = _ := by ring

theorem cellEnvelopeRowMass_eq_zero {a T X : ℝ} (j : ℤ)
    (hj : X ≤ |(j : ℝ)|) : cellEnvelopeRowMass a T X j = 0 := by
  simp [cellEnvelopeRowMass, Ioo_eq_empty_of_le (hj.trans (le_max_right _ _))]

theorem cellEnvelopeRowMass_eq_zero_of_not_mem {a T X : ℝ} (j : ℤ)
    (hj : j ∉ Finset.Icc (-⌈X⌉) ⌈X⌉) : cellEnvelopeRowMass a T X j = 0 := by
  apply cellEnvelopeRowMass_eq_zero
  by_contra h
  have habs : |(j : ℝ)| < X := lt_of_not_ge h
  have hceil : X ≤ (⌈X⌉ : ℝ) := Int.le_ceil X
  apply hj
  simp only [Finset.mem_Icc]
  constructor
  · have hl : -(⌈X⌉ : ℝ) ≤ (j : ℝ) := by
      have := (abs_lt.mp habs).1
      linarith
    exact_mod_cast hl
  · have hu : (j : ℝ) ≤ (⌈X⌉ : ℝ) := by
      have := (abs_lt.mp habs).2
      linarith
    exact_mod_cast hu

theorem cellEnvelopeMass_eq_sum (a T X : ℝ) :
    cellEnvelopeMass a T X =
      ∑ j ∈ Finset.Icc (-⌈X⌉) ⌈X⌉, cellEnvelopeRowMass a T X j :=
  tsum_eq_sum (fun j hj => cellEnvelopeRowMass_eq_zero_of_not_mem j hj)

theorem cellEnvelopeRowMass_summable (a T X : ℝ) :
    Summable (fun j : ℤ => cellEnvelopeRowMass a T X j) := by
  apply summable_of_hasFiniteSupport
  apply (Finset.finite_toSet (Finset.Icc (-⌈X⌉) ⌈X⌉)).subset
  intro j hj
  by_contra h
  exact hj (cellEnvelopeRowMass_eq_zero_of_not_mem j h)

theorem cellEnvelopeMass_nonneg {a T X : ℝ} (ha : 100 ≤ a) :
    0 ≤ cellEnvelopeMass a T X :=
  tsum_nonneg fun j => cellEnvelopeRowMass_nonneg j ha

theorem cellEnvelopeMass_eq_zero_of_nonpos {a T X : ℝ} (hX : X ≤ 0) :
    cellEnvelopeMass a T X = 0 := by
  have hz (j : ℤ) : cellEnvelopeRowMass a T X j = 0 :=
    cellEnvelopeRowMass_eq_zero j (hX.trans (abs_nonneg (j : ℝ)))
  simp only [cellEnvelopeMass, hz, tsum_zero]

/-- Summing the finite spin band produces only a quadratic prefactor,
with no extra exponential loss from the construction error. -/
theorem cellEnvelopeMass_le {a T X : ℝ}
    (ha : 100 ≤ a) (hT : 1 ≤ T) (hX : 0 ≤ X) :
    cellEnvelopeMass a T X ≤ 9 * (1 + X) ^ 2 * exp (4 * π * sqrt (a * X)) := by
  have hceil : 0 ≤ ⌈X⌉ := Int.ceil_nonneg hX
  have hcard : ((Finset.Icc (-⌈X⌉) ⌈X⌉).card : ℝ) = 2 * (⌈X⌉ : ℝ) + 1 := by
    have hh := Int.card_Icc_of_le (a := -⌈X⌉) (b := ⌈X⌉) (by omega)
    have hz : ((Finset.Icc (-⌈X⌉) ⌈X⌉).card : ℤ) = 2 * ⌈X⌉ + 1 := by omega
    exact_mod_cast hz
  have hceil_le : (⌈X⌉ : ℝ) ≤ X + 1 := (Int.ceil_lt_add_one X).le
  rw [cellEnvelopeMass_eq_sum]
  calc
    _ ≤ ∑ _j ∈ Finset.Icc (-⌈X⌉) ⌈X⌉,
        3 * X * exp (4 * π * sqrt (a * X)) :=
      Finset.sum_le_sum fun j _ => cellEnvelopeRowMass_le j ha hT hX
    _ = (2 * (⌈X⌉ : ℝ) + 1) * (3 * X * exp (4 * π * sqrt (a * X))) := by
      rw [Finset.sum_const, nsmul_eq_mul, hcard]
    _ ≤ (2 * (X + 1) + 1) * (3 * X * exp (4 * π * sqrt (a * X))) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      linarith
    _ ≤ _ := by
      have hp : (2 * (X + 1) + 1) * (3 * X) ≤ 9 * (1 + X) ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hp (exp_pos (4 * π * sqrt (a * X))).le]

end BTZEntropy.Comparison
