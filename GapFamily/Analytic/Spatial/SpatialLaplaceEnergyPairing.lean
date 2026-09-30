import GapFamily.Analytic.Spatial.SpatialOrbitLaplacePositivity
import GapFamily.Analytic.Spatial.SpatialOrbitLaplaceContinuation
import GapFamily.Analytic.Poincare.Fourier.PoincareLaplacePairing
import GapFamily.Analytic.Poincare.Fourier.PoincareLaplaceOutputFubini

/-!
# Identification of the actual finite spatial and energy pairings

The source Fourier/height identity is combined with ordinary energy/output
Fubini and the exact scalar rank correction. Positivity remains in the
separate spatial module.
-/

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open MeasureTheory Set UpperHalfPlane PoincareEnergyContinuation
open scoped Topology

private theorem continuous_horizontalPhase (j : ℤ) : Continuous (horizontalPhase j) := by
  unfold horizontalPhase
  fun_prop

private def sourceHeightValue (J : ℤ) (l : ℕ) (z : UpperHalfPlane) : ℂ :=
  UpperWeightedCoherence.weightedThresholdValue (1 / 4) (by norm_num)
    (spatialSourceFourierHeightInput (1 / 2) J l) z

private theorem continuous_sourceHeightValue (J : ℤ) (l : ℕ) :
    Continuous (sourceHeightValue J l) :=
  UpperWeightedCoherence.continuous_weightedThresholdValue _ _ _

private theorem intervalIntegrable_source_output (j J : ℤ) (k l : ℕ) :
    IntervalIntegrable (fun x : ℝ => horizontalPhase (-j) x *
      (laplaceHeightWeight k * sourceHeightValue J l (laplacePoint k x) -
        laplaceHeightWeight (k + 1) * sourceHeightValue J l (laplacePoint (k + 1) x)))
      volume 0 1 := by
  exact ((continuous_horizontalPhase (-j)).mul
    ((continuous_const.mul ((continuous_sourceHeightValue J l).comp (continuous_laplacePoint k))).sub
      (continuous_const.mul ((continuous_sourceHeightValue J l).comp
        (continuous_laplacePoint (k + 1)))))).intervalIntegrable 0 1

private theorem inner_spatial_test_eq_source_output (j J : ℤ) (k l : ℕ) (x : ℝ) :
    (∫ y : ℝ in 0..1, horizontalPhase (-j) x *
      normalizedHeightDifference spatialThresholdKernel k l x y * horizontalPhase J y) =
      horizontalPhase (-j) x *
        (laplaceHeightWeight k * sourceHeightValue J l (laplacePoint k x) -
          laplaceHeightWeight (k + 1) * sourceHeightValue J l (laplacePoint (k + 1) x)) := by
  let f (a b : ℕ) (y : ℝ) : ℂ :=
    horizontalPhase J y * spatialThresholdKernel (laplacePoint a x) (laplacePoint b y)
  have hi (a b : ℕ) : IntervalIntegrable (f a b) volume 0 1 :=
    ((continuous_horizontalPhase J).mul
      ((continuous_spatialThresholdKernel_right (laplacePoint a x)).comp
        (continuous_laplacePoint b))).intervalIntegrable 0 1
  have he (y : ℝ) : horizontalPhase (-j) x *
      normalizedHeightDifference spatialThresholdKernel k l x y * horizontalPhase J y =
      horizontalPhase (-j) x *
        (laplaceHeightWeight k * (laplaceHeightWeight l * f k l y -
          laplaceHeightWeight (l + 1) * f k (l + 1) y) -
        laplaceHeightWeight (k + 1) * (laplaceHeightWeight l * f (k + 1) l y -
          laplaceHeightWeight (l + 1) * f (k + 1) (l + 1) y)) := by
    dsimp [normalizedHeightDifference, f]
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul]
  have hk := (((hi k l).const_mul (laplaceHeightWeight l)).sub
    ((hi k (l + 1)).const_mul (laplaceHeightWeight (l + 1)))).const_mul (laplaceHeightWeight k)
  have hk' := (((hi (k + 1) l).const_mul (laplaceHeightWeight l)).sub
    ((hi (k + 1) (l + 1)).const_mul (laplaceHeightWeight (l + 1)))).const_mul
      (laplaceHeightWeight (k + 1))
  rw [intervalIntegral.integral_sub hk hk']
  simp_rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_sub ((hi k l).const_mul _) ((hi k (l + 1)).const_mul _),
    intervalIntegral.integral_sub ((hi (k + 1) l).const_mul _)
      ((hi (k + 1) (l + 1)).const_mul _)]
  simp_rw [intervalIntegral.integral_const_mul]
  simp only [sourceHeightValue, weightedThresholdValue_spatialSourceFourierHeightInput, f]

private theorem normalizedHeightDifference_corrected (k l : ℕ) (x y : ℝ) :
    normalizedHeightDifference spatialThresholdCorrectedKernel k l x y =
      normalizedHeightDifference spatialThresholdKernel k l x y +
        normalizedHeightDifference (fun _ _ => 6) k l x y := by
  simp only [normalizedHeightDifference, spatialThresholdCorrectedKernel]
  ring

private theorem intervalIntegrable_inner_rank_test (j J : ℤ) (k l : ℕ) :
    IntervalIntegrable (fun x : ℝ => ∫ y : ℝ in 0..1,
      horizontalPhase (-j) x * normalizedHeightDifference (fun _ _ => 6) k l x y *
        horizontalPhase J y) volume 0 1 := by
  simp only [normalizedHeightDifference]
  simp_rw [intervalIntegral.integral_const_mul]
  apply Continuous.intervalIntegrable
  unfold horizontalPhase
  fun_prop

/-- The canonical spatial pairing is its actual source output test plus the
ordinary reference-measure scalar rank correction. -/
private theorem spatialLaplacePairing_eq_source_output_add_rank (j J : ℤ) (k l : ℕ) :
    spatialLaplacePairing j J k l =
      (∫ x : ℝ in 0..1, horizontalPhase (-j) x *
        (laplaceHeightWeight k * sourceHeightValue J l (laplacePoint k x) -
          laplaceHeightWeight (k + 1) * sourceHeightValue J l (laplacePoint (k + 1) x))) +
      ((∫ p : ℝ × ℝ, laplaceTest k p.1 * scalarRankKernel j J p.1 p.2 * laplaceTest l p.2
        ∂((referenceMeasure j).prod (referenceMeasure J)) : ℝ) : ℂ) := by
  unfold spatialLaplacePairing
  have hi (a b : ℕ) (x : ℝ) :
      IntervalIntegrable (fun y : ℝ =>
        horizontalPhase (-j) x * (laplaceHeightWeight a * laplaceHeightWeight b *
          spatialThresholdKernel (laplacePoint a x) (laplacePoint b y)) * horizontalPhase J y)
        volume 0 1 := by
    exact ((continuous_const.mul (continuous_const.mul
      ((continuous_spatialThresholdKernel_right (laplacePoint a x)).comp
        (continuous_laplacePoint b)))).mul (continuous_horizontalPhase J)).intervalIntegrable 0 1
  have hcore (x : ℝ) : IntervalIntegrable (fun y : ℝ => horizontalPhase (-j) x *
      normalizedHeightDifference spatialThresholdKernel k l x y * horizontalPhase J y) volume 0 1 := by
    have he (y : ℝ) : horizontalPhase (-j) x *
        normalizedHeightDifference spatialThresholdKernel k l x y * horizontalPhase J y =
        (horizontalPhase (-j) x * (laplaceHeightWeight k * laplaceHeightWeight l *
          spatialThresholdKernel (laplacePoint k x) (laplacePoint l y)) * horizontalPhase J y) -
        (horizontalPhase (-j) x * (laplaceHeightWeight k * laplaceHeightWeight (l + 1) *
          spatialThresholdKernel (laplacePoint k x) (laplacePoint (l + 1) y)) * horizontalPhase J y) -
        (horizontalPhase (-j) x * (laplaceHeightWeight (k + 1) * laplaceHeightWeight l *
          spatialThresholdKernel (laplacePoint (k + 1) x) (laplacePoint l y)) * horizontalPhase J y) +
        (horizontalPhase (-j) x * (laplaceHeightWeight (k + 1) * laplaceHeightWeight (l + 1) *
          spatialThresholdKernel (laplacePoint (k + 1) x) (laplacePoint (l + 1) y)) * horizontalPhase J y) := by
      simp only [normalizedHeightDifference]
      ring
    simp_rw [he]
    exact (((hi k l x).sub (hi k (l + 1) x)).sub (hi (k + 1) l x)).add
      (hi (k + 1) (l + 1) x)
  have hrank (x : ℝ) : IntervalIntegrable (fun y : ℝ => horizontalPhase (-j) x *
      normalizedHeightDifference (fun _ _ => 6) k l x y * horizontalPhase J y) volume 0 1 := by
    simp only [normalizedHeightDifference]
    exact (continuous_const.mul (continuous_horizontalPhase J)).intervalIntegrable 0 1
  simp_rw [normalizedHeightDifference_corrected, mul_add, add_mul,
    intervalIntegral.integral_add (hcore _) (hrank _), inner_spatial_test_eq_source_output]
  rw [intervalIntegral.integral_add (intervalIntegrable_source_output j J k l)
    (intervalIntegrable_inner_rank_test j J k l), fourierHeight_six_eq_scalarRankKernel_pairing]

/-- The final finite pairing identification once the literal source Fourier/height
identity is supplied. The premise is instantiated by the actual operator continuation;
all finite integration, energy/output Fubini, and rank normalization are proved here. -/
private theorem spatialLaplacePairing_eq_laplaceEnergyPairing_of_source_identity
    (j J : ℤ) (k l : ℕ)
    (hsource : ∀ z : UpperHalfPlane,
      UpperWeightedCoherence.weightedThresholdValue (1 / 4) (by norm_num)
        (spatialSourceFourierHeightInput (1 / 2) J l) z =
          ∫ E : ℝ, (laplaceTest l E : ℂ) * generalThresholdSeed E J z ∂referenceMeasure J) :
    spatialLaplacePairing j J k l = laplaceEnergyPairing j J k l := by
  rw [spatialLaplacePairing_eq_source_output_add_rank,
    PoincareEnergyFourier.laplaceEnergyPairing_eq_generalThresholdSeed_pairing]
  congr 1
  calc
    _ = ∫ x : ℝ in 0..1, horizontalPhase (-j) x *
        ((∫ E : ℝ, (laplaceTest l E : ℂ) * generalThresholdSeed E J (laplacePoint k x)
            ∂referenceMeasure J) / (Real.sqrt (laplaceHeight k) : ℂ) -
          (∫ E : ℝ, (laplaceTest l E : ℂ) * generalThresholdSeed E J (laplacePoint (k + 1) x)
            ∂referenceMeasure J) / (Real.sqrt (laplaceHeight (k + 1)) : ℂ)) := by
      apply intervalIntegral.integral_congr
      intro x hx
      simp only [sourceHeightValue]
      rw [hsource (laplacePoint k x), hsource (laplacePoint (k + 1) x)]
      simp only [laplaceHeightWeight, div_eq_mul_inv]
      ring
    _ = _ := PoincareEnergyFourier.laplaceTest_fourier_height_integral_comm j J k l

/-- The actual canonical spatial finite Fourier/height pairing is exactly the
identity-plus-corrected-kernel energy pairing. The source identity is discharged by
the proved same-parameter operator continuation, with ordinary Fubini on both sides. -/
theorem spatialLaplacePairing_eq_laplaceEnergyPairing (j J : ℤ) (k l : ℕ) :
    spatialLaplacePairing j J k l = laplaceEnergyPairing j J k l :=
  spatialLaplacePairing_eq_laplaceEnergyPairing_of_source_identity j J k l
    (weightedThresholdValue_sourceHeight_eq_reference_point J l)

end GapFamily.Analytic.SpatialPoint
