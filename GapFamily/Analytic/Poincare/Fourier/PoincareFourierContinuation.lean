import GapFamily.Analytic.Poincare.PoincareHorizontalFunctional
import GapFamily.Analytic.Poincare.Seed.PoincareEnergyIdentification
import GapFamily.Analytic.Poincare.Fourier.PoincareFourierRegroup

/-! The actual continued ordinary horizontal Fourier coefficient of the zero-energy seed. -/
noncomputable section
namespace GapFamily.Analytic.PoincareFourierContinuation
open Set MeasureTheory UpperHalfPlane CuspFourierCutoff PoincareCanonical
open PoincareEnergyContinuation PoincareFourier PoincareFourierRegroup
open PoincareFourierUnfold
open scoped Topology

/-- The proved canonical compact continuation on the actual thin horizontal row. -/
def horizontalContinuation (y : ℝ) (hy : 0 < y) : Continuation (horizontalRow y) :=
  chosenContinuation (horizontalRow y) (horizontalRow_subset_upperHalfPlaneSet y hy)

/-- The full continuation domain: the actual threshold disk and punctured right half-plane. -/
def horizontalFourierDomain (y : ℝ) (hy : 0 < y) : Set ℂ :=
  continuationRegion (horizontalContinuation y hy).radius

/-- The bounded ordinary Fourier functional applied to the actual constructed family. -/
def continuedFourierCoefficient (y : ℝ) (hy : 0 < y) (j J : ℤ) (κ : ℂ) : ℂ :=
  horizontalFourierFunctional y j ((horizontalContinuation y hy).family J κ)

theorem isOpen_horizontalFourierDomain (y : ℝ) (hy : 0 < y) :
    IsOpen (horizontalFourierDomain y hy) := isOpen_continuationRegion _

theorem zero_mem_horizontalFourierDomain (y : ℝ) (hy : 0 < y) :
    (0 : ℂ) ∈ horizontalFourierDomain y hy := by
  left
  simpa only [Metric.mem_ball, dist_self] using (horizontalContinuation y hy).radius_pos

/-- Analyticity holds on the whole actual parameter domain, in the complex norm. -/
theorem analyticOnNhd_continuedFourierCoefficient (y : ℝ) (hy : 0 < y) (j J : ℤ) :
    AnalyticOnNhd ℂ (continuedFourierCoefficient y hy j J) (horizontalFourierDomain y hy) := by
  intro κ hκ
  exact ((horizontalFourierFunctional y j).analyticAt _).comp
    ((horizontalContinuation y hy).analytic_family J κ hκ)

theorem analyticAt_continuedFourierCoefficient_zero (y : ℝ) (hy : 0 < y) (j J : ℤ) :
    AnalyticAt ℂ (continuedFourierCoefficient y hy j J) 0 :=
  analyticOnNhd_continuedFourierCoefficient y hy j J 0 (zero_mem_horizontalFourierDomain y hy)

/-- Contraction of the ordinary Fourier integral keeps the compact seed's spin bound. -/
theorem norm_continuedFourierCoefficient_le (y : ℝ) (hy : 0 < y) (j J : ℤ) (κ : ℂ)
    (hκ : ‖κ‖ ≤ (horizontalContinuation y hy).radius) :
    ‖continuedFourierCoefficient y hy j J κ‖ ≤
      (horizontalContinuation y hy).bound * (1 + (J : ℝ) ^ 2) := by
  exact (norm_horizontalFourierFunctional_apply_le y j _).trans
    ((horizontalContinuation y hy).uniform_bound J κ hκ)

/-- One disk and one constant work simultaneously for every input and output spin. -/
theorem exists_uniform_continuedFourierCoefficient_bound (y : ℝ) (hy : 0 < y) :
    ∃ r C : ℝ, 0 < r ∧ r ≤ 1 / 8 ∧ 0 < C ∧
      ∀ (j J : ℤ) (κ : ℂ), ‖κ‖ ≤ r →
        ‖continuedFourierCoefficient y hy j J κ‖ ≤ C * (1 + (J : ℝ) ^ 2) := by
  refine ⟨(horizontalContinuation y hy).radius, (horizontalContinuation y hy).bound,
    (horizontalContinuation y hy).radius_pos, (horizontalContinuation y hy).radius_le_eighth,
    (horizontalContinuation y hy).bound_pos, ?_⟩
  exact norm_continuedFourierCoefficient_le y hy

/-- The canonical threshold coefficient is an ordinary interval integral of the actual global seed. -/
def thresholdFourierCoefficient (y : ℝ) (hy : 0 < y) (j J : ℤ) : ℂ :=
  ∫ x in (0 : ℝ)..1, cuspFourierMode (-j) x * thresholdSeed J (rowPoint y hy x)

/-- This ordinary threshold integral is genuinely integrable, even though the observation row is thin. -/
theorem intervalIntegrable_thresholdFourierIntegrand (y : ℝ) (hy : 0 < y) (j J : ℤ) :
    IntervalIntegrable (fun x => cuspFourierMode (-j) x * thresholdSeed J (rowPoint y hy x))
      volume 0 1 :=
  ((contDiff_cuspFourierMode (-j)).continuous.mul
    ((continuous_thresholdSeed J).comp (continuous_rowPoint y hy))).intervalIntegrable 0 1

/-- At zero the analytic coefficient is exactly the canonical global threshold coefficient. -/
theorem continuedFourierCoefficient_zero (y : ℝ) (hy : 0 < y) (j J : ℤ) :
    continuedFourierCoefficient y hy j J 0 = thresholdFourierCoefficient y hy j J := by
  unfold continuedFourierCoefficient thresholdFourierCoefficient
  apply horizontalFourierFunctional_eq_intervalIntegral
  intro x hx
  exact (thresholdSeed_eq_continuation (horizontalContinuation y hy) J
    (rowPoint y hy x) ⟨x, hx, rfl⟩).symm

/-- On the complete original convergence half-plane, the new family is the literal
ordinary Fourier coefficient of the original zero-energy Poincaré series. -/
theorem continuedFourierCoefficient_eq_series (y : ℝ) (hy : 0 < y) (j J : ℤ)
    {κ : ℂ} (hκ : (1 / 2 : ℝ) < κ.re) :
    continuedFourierCoefficient y hy j J κ =
      ∫ x in (0 : ℝ)..1, cuspFourierMode (-j) x *
        complexPoincareSeries 0 J (exponent κ) (rowPoint y hy x) := by
  unfold continuedFourierCoefficient
  apply horizontalFourierFunctional_eq_intervalIntegral
  intro x hx
  have h := continuation_eq_series_full_convergence (horizontalRow y)
    (horizontalRow_subset_upperHalfPlaneSet y hy) (horizontalContinuation y hy) J hκ
      ⟨Complex.mk x y, ⟨x, hx, rfl⟩⟩
  have hp : ofComplex (Complex.mk x y) = rowPoint y hy x :=
    ofComplex_apply (rowPoint y hy x)
  simpa only [hp] using h

/-- The convergent arithmetic integral series identifies this analytic coefficient
only on Re κ>1/2; no termwise continuation of that denominator sum is asserted. -/
theorem hasSum_kloosterman_continuedFourierCoefficient_common
    (y : ℝ) (hy : 0 < y) (j J : ℤ) {κ : ℂ} (hκ : (1 / 2 : ℝ) < κ.re) :
    HasSum (fun n : ℕ => kloostermanSum j J n *
      ∫ t : ℝ, fourierKernel (n + 1 : ℕ) y j J (exponent κ) t)
      (continuedFourierCoefficient y hy j J κ -
        (if j = J then (y : ℂ) ^ (exponent κ) else 0)) := by
  rw [continuedFourierCoefficient_eq_series y hy j J hκ]
  have hs : 1 < (exponent κ).re := by
    norm_num [exponent, Complex.add_re]
    linarith
  exact hasSum_kloosterman_fourier j J hs y hy

/-- The canonical threshold coefficients inherit the same bound uniformly in output spin. -/
theorem thresholdFourierCoefficient_uniform_bound (y : ℝ) (hy : 0 < y) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j J : ℤ),
      ‖thresholdFourierCoefficient y hy j J‖ ≤ C * (1 + (J : ℝ) ^ 2) := by
  refine ⟨(horizontalContinuation y hy).bound, (horizontalContinuation y hy).bound_pos, ?_⟩
  intro j J
  rw [← continuedFourierCoefficient_zero y hy j J]
  exact norm_continuedFourierCoefficient_le y hy j J 0
    (by simpa using (horizontalContinuation y hy).radius_pos.le)

end GapFamily.Analytic.PoincareFourierContinuation
