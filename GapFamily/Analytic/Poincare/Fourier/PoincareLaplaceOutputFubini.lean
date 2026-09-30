import GapFamily.Analytic.Poincare.Continuation.PoincareLaplaceContinuation
import GapFamily.Analytic.Poincare.Fourier.PoincareLaplaceDifference

/-!
# The input energy integral commutes with the actual output test

The physical input test gives an ordinary integral in compact spatial norm.
The bounded horizontal Fourier functional therefore commutes with that
integral. Both output heights and their difference have explicit ordinary
integrability, including the scalar input endpoint.
-/

noncomputable section
namespace GapFamily.Analytic.PoincareEnergyFourier
open Set Filter MeasureTheory UpperHalfPlane CuspFourierCutoff PoincareCanonical
open PoincareFourier PoincareFourierContinuation PoincareEnergyContinuation

/-- Ordinary compact-row integrability before applying the Fourier functional. -/
theorem integrable_laplaceTest_compactRow (y : ℝ) (hy : 0 < y) (J : ℤ) (l : ℕ) :
    Integrable (fun E : ℝ => (laplaceTest l E : ℂ) •
      continuedSeedOn (horizontalRow y) (horizontalRow_subset_upperHalfPlaneSet y hy) E J 0)
      (referenceMeasure J) := by
  simpa only [thermalHeightDifference_eq_laplaceTest] using
    integrable_seedLaplaceDifference_reference (horizontalRow y)
      (horizontalRow_subset_upperHalfPlaneSet y hy) J
      (show 0 < (l : ℝ) + 1 by positivity) (show (0 : ℝ) ≤ 1 by norm_num)

private theorem horizontalFourierFunctional_laplaceTest_seed
    (y : ℝ) (hy : 0 < y) (j J : ℤ) (l : ℕ) (E : ℝ) :
    horizontalFourierFunctional y j ((laplaceTest l E : ℂ) •
      continuedSeedOn (horizontalRow y) (horizontalRow_subset_upperHalfPlaneSet y hy) E J 0) =
        (laplaceTest l E : ℂ) * generalThresholdFourierCoefficient y hy E j J := by
  rw [map_smul, smul_eq_mul, ← continuedEnergyFourierCoefficient_zero y hy E j J]
  rfl

/-- The input integral of each actual output Fourier coefficient is ordinary. -/
theorem integrable_laplaceTest_generalThresholdFourierCoefficient
    (y : ℝ) (hy : 0 < y) (j J : ℤ) (l : ℕ) :
    Integrable (fun E : ℝ => (laplaceTest l E : ℂ) *
      generalThresholdFourierCoefficient y hy E j J) (referenceMeasure J) := by
  apply ((horizontalFourierFunctional y j).integrable_comp
    (integrable_laplaceTest_compactRow y hy J l)).congr
  exact Eventually.of_forall (horizontalFourierFunctional_laplaceTest_seed y hy j J l)

private theorem laplaceSeedOn_horizontalRow_reference
    (y : ℝ) (hy : 0 < y) (J : ℤ) (l : ℕ) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    laplaceSeedOn (horizontalRow y) (horizontalRow_subset_upperHalfPlaneSet y hy) J l (1 / 2)
      ⟨Complex.mk x y, ⟨x, hx, rfl⟩⟩ =
      ∫ E : ℝ, (laplaceTest l E : ℂ) * generalThresholdSeed E J (rowPoint y hy x)
        ∂referenceMeasure J :=
  laplaceSeedOn_one_half_apply_reference (horizontalRow y)
    (horizontalRow_subset_upperHalfPlaneSet y hy) J l (rowPoint y hy x) ⟨x, hx, rfl⟩

/-- The ordinary output Fourier integral remains interval integrable after
integrating over the full physical input energy half-line. -/
theorem intervalIntegrable_laplaceTest_integral_fourier
    (y : ℝ) (hy : 0 < y) (j J : ℤ) (l : ℕ) :
    IntervalIntegrable (fun x : ℝ => horizontalPhase (-j) x *
      (∫ E : ℝ, (laplaceTest l E : ℂ) * generalThresholdSeed E J (rowPoint y hy x)
        ∂referenceMeasure J)) volume 0 1 := by
  simpa only [horizontalPhase_eq_cuspFourierMode] using
    intervalIntegrable_horizontalFourierRepresentative y j
      (laplaceSeedOn (horizontalRow y) (horizontalRow_subset_upperHalfPlaneSet y hy) J l (1 / 2))
      _ (laplaceSeedOn_horizontalRow_reference y hy J l)

/-- The actual bounded Fourier functional commutes with the ordinary input
energy integral. This includes the zero-spin reference singularity. -/
theorem laplaceTest_fourier_integral_comm
    (y : ℝ) (hy : 0 < y) (j J : ℤ) (l : ℕ) :
    (∫ x : ℝ in 0..1, horizontalPhase (-j) x *
      (∫ E : ℝ, (laplaceTest l E : ℂ) * generalThresholdSeed E J (rowPoint y hy x)
        ∂referenceMeasure J)) =
      ∫ E : ℝ, (laplaceTest l E : ℂ) *
        generalThresholdFourierCoefficient y hy E j J ∂referenceMeasure J := by
  have hf := horizontalFourierFunctional_eq_intervalIntegral y j
    (laplaceSeedOn (horizontalRow y) (horizontalRow_subset_upperHalfPlaneSet y hy) J l (1 / 2))
    _ (laplaceSeedOn_horizontalRow_reference y hy J l)
  rw [← show (∫ x : ℝ in 0..1, horizontalPhase (-j) x *
      (∫ E : ℝ, (laplaceTest l E : ℂ) * generalThresholdSeed E J (rowPoint y hy x)
        ∂referenceMeasure J)) =
      ∫ x : ℝ in 0..1, cuspFourierMode (-j) x *
        (∫ E : ℝ, (laplaceTest l E : ℂ) * generalThresholdSeed E J (rowPoint y hy x)
          ∂referenceMeasure J) by simp only [horizontalPhase_eq_cuspFourierMode]] at hf
  rw [← hf, laplaceSeedOn_one_half_eq_reference,
    ← (horizontalFourierFunctional y j).integral_comp_comm
      (integrable_laplaceTest_compactRow y hy J l)]
  apply integral_congr_ae
  exact Eventually.of_forall (horizontalFourierFunctional_laplaceTest_seed y hy j J l)

/-- The actual output height test equals the difference of the two ordinary
Fourier coefficients, before any energy integration. -/
theorem generalThresholdSeed_fourier_height_eq_coefficient (k : ℕ)
    (E : ℝ) (j J : ℤ) :
    (∫ x : ℝ in 0..1, horizontalPhase (-j) x *
      (generalThresholdSeed E J (laplacePoint k x) / (Real.sqrt (laplaceHeight k) : ℂ) -
        generalThresholdSeed E J (laplacePoint (k + 1) x) /
          (Real.sqrt (laplaceHeight (k + 1)) : ℂ))) =
      generalThresholdFourierCoefficient (laplaceHeight k) (laplaceHeight_pos k) E j J /
        (Real.sqrt (laplaceHeight k) : ℂ) -
      generalThresholdFourierCoefficient (laplaceHeight (k + 1))
        (laplaceHeight_pos (k + 1)) E j J / (Real.sqrt (laplaceHeight (k + 1)) : ℂ) := by
  have hp (n : ℕ) (x : ℝ) :
      laplacePoint n x = rowPoint (laplaceHeight n) (laplaceHeight_pos n) x := rfl
  simp_rw [horizontalPhase_eq_cuspFourierMode, hp, mul_sub, ← mul_div_assoc]
  rw [intervalIntegral.integral_sub
    ((intervalIntegrable_generalThresholdFourierIntegrand _ (laplaceHeight_pos k) E j J).div_const _)
    ((intervalIntegrable_generalThresholdFourierIntegrand _ (laplaceHeight_pos (k + 1)) E j J).div_const _),
    intervalIntegral.integral_div, intervalIntegral.integral_div]
  rfl

/-- The ordinary output height test is interval integrable at every input energy. -/
theorem intervalIntegrable_generalThresholdSeed_fourier_height
    (k : ℕ) (E : ℝ) (j J : ℤ) :
    IntervalIntegrable (fun x : ℝ => horizontalPhase (-j) x *
      (generalThresholdSeed E J (laplacePoint k x) / (Real.sqrt (laplaceHeight k) : ℂ) -
        generalThresholdSeed E J (laplacePoint (k + 1) x) /
          (Real.sqrt (laplaceHeight (k + 1)) : ℂ))) volume 0 1 := by
  have hp (n : ℕ) (x : ℝ) :
      laplacePoint n x = rowPoint (laplaceHeight n) (laplaceHeight_pos n) x := rfl
  simpa only [horizontalPhase_eq_cuspFourierMode, hp, mul_sub, ← mul_div_assoc] using
    ((intervalIntegrable_generalThresholdFourierIntegrand _ (laplaceHeight_pos k) E j J).div_const
      (Real.sqrt (laplaceHeight k) : ℂ)).sub
        ((intervalIntegrable_generalThresholdFourierIntegrand _ (laplaceHeight_pos (k + 1)) E j J).div_const
          (Real.sqrt (laplaceHeight (k + 1)) : ℂ))

/-- Integrating the input energy first still gives an ordinary Fourier/height test. -/
theorem intervalIntegrable_laplaceTest_integral_fourier_height
    (j J : ℤ) (k l : ℕ) :
    IntervalIntegrable (fun x : ℝ => horizontalPhase (-j) x *
      ((∫ E : ℝ, (laplaceTest l E : ℂ) * generalThresholdSeed E J (laplacePoint k x)
          ∂referenceMeasure J) / (Real.sqrt (laplaceHeight k) : ℂ) -
        (∫ E : ℝ, (laplaceTest l E : ℂ) * generalThresholdSeed E J (laplacePoint (k + 1) x)
          ∂referenceMeasure J) / (Real.sqrt (laplaceHeight (k + 1)) : ℂ))) volume 0 1 := by
  have hp (n : ℕ) (x : ℝ) :
      laplacePoint n x = rowPoint (laplaceHeight n) (laplaceHeight_pos n) x := rfl
  simpa only [hp, mul_sub, ← mul_div_assoc] using
    ((intervalIntegrable_laplaceTest_integral_fourier _ (laplaceHeight_pos k) j J l).div_const
      (Real.sqrt (laplaceHeight k) : ℂ)).sub
        ((intervalIntegrable_laplaceTest_integral_fourier _ (laplaceHeight_pos (k + 1)) j J l).div_const
          (Real.sqrt (laplaceHeight (k + 1)) : ℂ))

/-- Integrating the Fourier/height test first gives an ordinary input reference integral. -/
theorem integrable_laplaceTest_fourier_height (j J : ℤ) (k l : ℕ) :
    Integrable (fun E : ℝ => (laplaceTest l E : ℂ) *
      (∫ x : ℝ in 0..1, horizontalPhase (-j) x *
        (generalThresholdSeed E J (laplacePoint k x) /
            (Real.sqrt (laplaceHeight k) : ℂ) -
          generalThresholdSeed E J (laplacePoint (k + 1) x) /
            (Real.sqrt (laplaceHeight (k + 1)) : ℂ)))) (referenceMeasure J) := by
  simp_rw [generalThresholdSeed_fourier_height_eq_coefficient, mul_sub, ← mul_div_assoc]
  exact ((integrable_laplaceTest_generalThresholdFourierCoefficient _ (laplaceHeight_pos k)
    j J l).div_const _).sub
      ((integrable_laplaceTest_generalThresholdFourierCoefficient _ (laplaceHeight_pos (k + 1))
        j J l).div_const _)

/-- The actual input energy integral commutes with the full normalized
output Fourier/height test. Both iterated integrals are ordinarily convergent. -/
theorem laplaceTest_fourier_height_integral_comm (j J : ℤ) (k l : ℕ) :
    (∫ x : ℝ in 0..1, horizontalPhase (-j) x *
      ((∫ E : ℝ, (laplaceTest l E : ℂ) * generalThresholdSeed E J (laplacePoint k x)
          ∂referenceMeasure J) / (Real.sqrt (laplaceHeight k) : ℂ) -
        (∫ E : ℝ, (laplaceTest l E : ℂ) * generalThresholdSeed E J (laplacePoint (k + 1) x)
          ∂referenceMeasure J) / (Real.sqrt (laplaceHeight (k + 1)) : ℂ))) =
      ∫ E : ℝ, (laplaceTest l E : ℂ) *
        (∫ x : ℝ in 0..1, horizontalPhase (-j) x *
          (generalThresholdSeed E J (laplacePoint k x) /
              (Real.sqrt (laplaceHeight k) : ℂ) -
            generalThresholdSeed E J (laplacePoint (k + 1) x) /
              (Real.sqrt (laplaceHeight (k + 1)) : ℂ))) ∂referenceMeasure J := by
  simp_rw [generalThresholdSeed_fourier_height_eq_coefficient, mul_sub, ← mul_div_assoc]
  have hp (n : ℕ) (x : ℝ) :
      laplacePoint n x = rowPoint (laplaceHeight n) (laplaceHeight_pos n) x := rfl
  simp_rw [hp]
  rw [intervalIntegral.integral_sub
    ((intervalIntegrable_laplaceTest_integral_fourier _ (laplaceHeight_pos k) j J l).div_const _)
    ((intervalIntegrable_laplaceTest_integral_fourier _ (laplaceHeight_pos (k + 1)) j J l).div_const _),
    intervalIntegral.integral_div, intervalIntegral.integral_div,
    laplaceTest_fourier_integral_comm _ (laplaceHeight_pos k) j J l,
    laplaceTest_fourier_integral_comm _ (laplaceHeight_pos (k + 1)) j J l,
    integral_sub ((integrable_laplaceTest_generalThresholdFourierCoefficient _
      (laplaceHeight_pos k) j J l).div_const _)
      ((integrable_laplaceTest_generalThresholdFourierCoefficient _
        (laplaceHeight_pos (k + 1)) j J l).div_const _),
    integral_div, integral_div]

end GapFamily.Analytic.PoincareEnergyFourier
