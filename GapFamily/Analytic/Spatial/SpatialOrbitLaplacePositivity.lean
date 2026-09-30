import GapFamily.Analytic.Spatial.SpatialOrbitPointGram
import GapFamily.Analytic.Kernel.PositiveKernelIntegral

/-! Actual Fourier projections and adjacent normalized height differences of
the canonical corrected spatial kernel have nonnegative finite pairings. -/
noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open MeasureTheory
open scoped ComplexOrder ComplexConjugate BigOperators

/-- The ordinary double Fourier integral of the four normalized heights of
the actual continued spatial kernel, including its exact constant correction. -/
def spatialLaplacePairing (j J : ℤ) (k l : ℕ) : ℂ :=
  ∫ x : ℝ in 0..1, ∫ y : ℝ in 0..1,
    horizontalPhase (-j) x *
      normalizedHeightDifference spatialThresholdCorrectedKernel k l x y *
      horizontalPhase J y

/-- Positivity survives the actual horizontal integrals and both adjacent
height differences. The source kernel positivity is discharged internally. -/
theorem spatialLaplacePairing_posSemidef
    {ι : Type*} [Finite ι] (j : ι → ℤ) (k : ι → ℕ) :
    Matrix.PosSemidef (fun i l => spatialLaplacePairing (j i) (j l) (k i) (k l)) :=
  posSemidef_fourierHeight_interval spatialThresholdCorrectedKernel
    spatialThresholdCorrectedKernel_matrix_posSemidef
    continuous_spatialThresholdCorrectedKernel j k

/-- The spin/height index set may itself be infinite; the matrix predicate
uses precisely the finitely supported combinations. -/
theorem spatialLaplacePairing_matrix_posSemidef :
    Matrix.PosSemidef (fun a b : ℤ × ℕ =>
      spatialLaplacePairing a.1 b.1 a.2 b.2) := by
  apply FiniteKernelPosSemidef.posSemidef_of_finite_gram
  intro ι _ p
  exact spatialLaplacePairing_posSemidef (fun i => (p i).1) (fun i => (p i).2)

/-- Every actual finite Fourier/height linear combination has a nonnegative
complex quadratic form (so its imaginary part also vanishes). -/
theorem spatialLaplacePairing_quadratic_nonneg
    {ι : Type*} [Fintype ι] (j : ι → ℤ) (k : ι → ℕ) (c : ι → ℂ) :
    0 ≤ ∑ i, ∑ l, star (c i) *
      spatialLaplacePairing (j i) (j l) (k i) (k l) * c l := by
  have h := (spatialLaplacePairing_posSemidef j k).dotProduct_mulVec_nonneg c
  simpa only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, mul_assoc] using h

theorem spatialLaplacePairing_quadratic_re_nonneg
    {ι : Type*} [Fintype ι] (j : ι → ℤ) (k : ι → ℕ) (c : ι → ℂ) :
    0 ≤ (∑ i, ∑ l, star (c i) *
      spatialLaplacePairing (j i) (j l) (k i) (k l) * c l).re :=
  (Complex.nonneg_iff.mp (spatialLaplacePairing_quadratic_nonneg j k c)).1

theorem spatialLaplacePairing_quadratic_im_eq_zero
    {ι : Type*} [Fintype ι] (j : ι → ℤ) (k : ι → ℕ) (c : ι → ℂ) :
    (∑ i, ∑ l, star (c i) *
      spatialLaplacePairing (j i) (j l) (k i) (k l) * c l).im = 0 :=
  (Complex.nonneg_iff.mp (spatialLaplacePairing_quadratic_nonneg j k c)).2.symm

private theorem continuous_laplaceIntegrand_of_continuous
    (K : Matrix UpperHalfPlane UpperHalfPlane ℂ)
    (hcont : Continuous (Function.uncurry K)) (j J : ℤ) (k l : ℕ) :
    Continuous (fun p : ℝ × ℝ => horizontalPhase (-j) p.1 *
      normalizedHeightDifference K k l p.1 p.2 * horizontalPhase J p.2) := by
  have hc (a b : ℕ) : Continuous (fun p : ℝ × ℝ =>
      K (laplacePoint a p.1) (laplacePoint b p.2)) := by
    have hpair : Continuous (fun p : ℝ × ℝ =>
        (laplacePoint a p.1, laplacePoint b p.2)) :=
      ((continuous_laplacePoint a).comp continuous_fst).prodMk
        ((continuous_laplacePoint b).comp continuous_snd)
    exact hcont.comp hpair
  have hd : Continuous (fun p : ℝ × ℝ => normalizedHeightDifference K k l p.1 p.2) := by
    unfold normalizedHeightDifference
    exact (((continuous_const.mul (hc k l)).sub
      (continuous_const.mul (hc k (l + 1)))).sub
      (continuous_const.mul (hc (k + 1) l))).add
      (continuous_const.mul (hc (k + 1) (l + 1)))
  have hp (n : ℤ) : Continuous (horizontalPhase n) := by
    unfold horizontalPhase
    fun_prop
  exact ((hp (-j)).comp continuous_fst).mul hd |>.mul ((hp J).comp continuous_snd)

/-- Joint continuity certifies the compact Fourier integrations as ordinary
integrals of the canonical spatial response. -/
theorem continuous_spatialLaplaceIntegrand (j J : ℤ) (k l : ℕ) :
    Continuous (fun p : ℝ × ℝ => horizontalPhase (-j) p.1 *
      normalizedHeightDifference spatialThresholdCorrectedKernel k l p.1 p.2 *
      horizontalPhase J p.2) :=
  continuous_laplaceIntegrand_of_continuous spatialThresholdCorrectedKernel
    continuous_spatialThresholdCorrectedKernel j J k l

theorem intervalIntegrable_spatialLaplaceIntegrand
    (j J : ℤ) (k l : ℕ) (x : ℝ) :
    IntervalIntegrable (fun y : ℝ => horizontalPhase (-j) x *
      normalizedHeightDifference spatialThresholdCorrectedKernel k l x y *
      horizontalPhase J y) volume 0 1 := by
  have hc : Continuous (fun y : ℝ => (x, y)) := continuous_const.prodMk continuous_id
  exact ((continuous_spatialLaplaceIntegrand j J k l).comp hc).intervalIntegrable 0 1

end GapFamily.Analytic.SpatialPoint
