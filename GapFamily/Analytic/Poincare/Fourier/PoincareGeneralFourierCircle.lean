import GapFamily.Analytic.Poincare.Fourier.PoincareGeneralFourier
import Mathlib.Analysis.Fourier.AddCircle

/-! Circle Fourier reconstruction of the actual general-energy threshold seed.
The circle function is the periodic quotient of the continuous canonical seed.
Its ordinary Fourier coefficients are exactly the already constructed coefficients.
-/
noncomputable section
namespace GapFamily.Analytic.PoincareEnergyFourier

open Set MeasureTheory PoincareFourier PoincareEnergyContinuation
open scoped Topology

/-- Modular translation acts on the literal horizontal row by adding one. -/
theorem rowPoint_add_one (y : ℝ) (hy : 0 < y) (x : ℝ) :
    rowPoint y hy (x + 1) = ModularGroup.T • rowPoint y hy x := by
  rw [UpperHalfPlane.modular_T_smul]
  apply UpperHalfPlane.ext
  apply Complex.ext <;> simp [rowPoint, UpperHalfPlane.coe_vadd, add_comm]

/-- The actual canonical threshold seed is periodic along every horizontal row. -/
theorem periodic_generalThresholdSeed_row (y : ℝ) (hy : 0 < y) (E : ℂ) (J : ℤ) :
    Function.Periodic (fun x => generalThresholdSeed E J (rowPoint y hy x)) 1 := by
  intro x
  change generalThresholdSeed E J (rowPoint y hy (x + 1)) =
    generalThresholdSeed E J (rowPoint y hy x)
  rw [rowPoint_add_one, generalThresholdSeed_smul]

/-- The actual threshold row as a continuous function on the unit circle. -/
def generalThresholdCircle (y : ℝ) (hy : 0 < y) (E : ℂ) (J : ℤ) :
    C(AddCircle (1 : ℝ), ℂ) where
  toFun := (periodic_generalThresholdSeed_row y hy E J).lift
  continuous_toFun := continuous_coinduced_dom.mpr
    ((continuous_generalThresholdSeed E J).comp (continuous_rowPoint y hy))

/-- The circle lift agrees with the canonical seed at every real coordinate. -/
@[simp] theorem generalThresholdCircle_coe (y : ℝ) (hy : 0 < y) (E : ℂ) (J : ℤ) (x : ℝ) :
    generalThresholdCircle y hy E J (x : AddCircle (1 : ℝ)) =
      generalThresholdSeed E J (rowPoint y hy x) :=
  (periodic_generalThresholdSeed_row y hy E J).lift_coe x

/-- The standard circle character has the project's positive Fourier convention. -/
theorem fourier_coe_eq_cuspFourierMode (j : ℤ) (x : ℝ) :
    fourier j (x : AddCircle (1 : ℝ)) = cuspFourierMode j x := by
  rw [fourier_coe_apply]
  simp [cuspFourierMode]

/-- Circle Fourier extraction is exactly the ordinary threshold Fourier integral. -/
theorem fourierCoeff_generalThresholdCircle (y : ℝ) (hy : 0 < y) (E : ℂ) (j J : ℤ) :
    fourierCoeff (generalThresholdCircle y hy E J) j =
      generalThresholdFourierCoefficient y hy E j J := by
  rw [fourierCoeff_eq_intervalIntegral _ _ 0]
  simp only [one_div, inv_one, one_smul, zero_add, smul_eq_mul]
  apply intervalIntegral.integral_congr
  intro x hx
  simp only [fourier_coe_eq_cuspFourierMode, generalThresholdCircle_coe]

/-- Absolute summability of the actual coefficients gives uniform circle reconstruction. -/
theorem hasSum_generalThresholdCircle_of_summable
    (y : ℝ) (hy : 0 < y) (E : ℂ) (J : ℤ)
    (hs : Summable (fun j : ℤ => generalThresholdFourierCoefficient y hy E j J)) :
    HasSum (fun j : ℤ => generalThresholdFourierCoefficient y hy E j J •
      (fourier j : C(AddCircle (1 : ℝ), ℂ))) (generalThresholdCircle y hy E J) := by
  have hc : Summable (fourierCoeff (generalThresholdCircle y hy E J)) := by
    exact hs.congr (fun j => (fourierCoeff_generalThresholdCircle y hy E j J).symm)
  simpa only [fourierCoeff_generalThresholdCircle] using
    hasSum_fourier_series_of_summable hc

/-- Summable actual coefficients reconstruct the seed at every real coordinate. -/
theorem hasSum_generalThresholdSeed_row_of_summable
    (y : ℝ) (hy : 0 < y) (E : ℂ) (J : ℤ)
    (hs : Summable (fun j : ℤ => generalThresholdFourierCoefficient y hy E j J)) (x : ℝ) :
    HasSum (fun j : ℤ => generalThresholdFourierCoefficient y hy E j J * cuspFourierMode j x)
      (generalThresholdSeed E J (rowPoint y hy x)) := by
  have hc : Summable (fourierCoeff (generalThresholdCircle y hy E J)) := by
    exact hs.congr (fun j => (fourierCoeff_generalThresholdCircle y hy E j J).symm)
  simpa only [fourierCoeff_generalThresholdCircle, smul_eq_mul,
    fourier_coe_eq_cuspFourierMode, generalThresholdCircle_coe] using
    has_pointwise_sum_fourier_series_of_summable hc (x : AddCircle (1 : ℝ))

end GapFamily.Analytic.PoincareEnergyFourier
