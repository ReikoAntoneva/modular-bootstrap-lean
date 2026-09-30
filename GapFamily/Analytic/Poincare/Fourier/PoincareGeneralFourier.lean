import GapFamily.Analytic.Poincare.Fourier.PoincareFourierContinuation
import GapFamily.Analytic.Poincare.Fourier.PoincareEnergyFourierFunctional

/-! The actual continued ordinary horizontal Fourier coefficient at arbitrary complex energy. -/

noncomputable section
namespace GapFamily.Analytic.PoincareEnergyFourier

open Set MeasureTheory UpperHalfPlane CuspFourierCutoff PoincareCanonical
open PoincareFourier PoincareFourierContinuation
open PoincareEnergyContinuation PoincareEnergyConvergentAnalytic
open scoped Topology

/-- The bounded ordinary Fourier functional of the actual compact general-energy continuation. -/
def continuedEnergyFourierCoefficient (y : ℝ) (hy : 0 < y) (E : ℂ)
    (j J : ℤ) (κ : ℂ) : ℂ :=
  horizontalFourierFunctional y j
    (continuedSeedOn (horizontalRow y) (horizontalRow_subset_upperHalfPlaneSet y hy) E J κ)

/-- Linearity splits the literal continuation into its canonical base and actual energy correction. -/
theorem continuedEnergyFourierCoefficient_eq_base_add_correction (y : ℝ) (hy : 0 < y)
    (E : ℂ) (j J : ℤ) (κ : ℂ) :
    continuedEnergyFourierCoefficient y hy E j J κ =
      continuedFourierCoefficient y hy j J κ +
        energyFourierCorrection y hy E j J (exponent κ) := by
  exact map_add (horizontalFourierFunctional y j) _ _

/-- The general-energy ordinary Fourier coefficient is analytic on the full actual domain. -/
theorem analyticOnNhd_continuedEnergyFourierCoefficient (y : ℝ) (hy : 0 < y)
    (E : ℂ) (j J : ℤ) :
    AnalyticOnNhd ℂ (continuedEnergyFourierCoefficient y hy E j J)
      (horizontalFourierDomain y hy) := by
  intro κ hκ
  exact ((horizontalFourierFunctional y j).analyticAt _).comp
    (analyticOnNhd_continuedSeedOn (horizontalRow y)
      (horizontalRow_subset_upperHalfPlaneSet y hy) E J κ hκ)

/-- Analyticity includes the actual threshold parameter. -/
theorem analyticAt_continuedEnergyFourierCoefficient_zero (y : ℝ) (hy : 0 < y)
    (E : ℂ) (j J : ℤ) :
    AnalyticAt ℂ (continuedEnergyFourierCoefficient y hy E j J) 0 :=
  analyticOnNhd_continuedEnergyFourierCoefficient y hy E j J 0
    (zero_mem_horizontalFourierDomain y hy)

/-- At every parameter in the actual domain, all complex energy dependence is entire. -/
theorem analyticAt_continuedEnergyFourierCoefficient_energy (y : ℝ) (hy : 0 < y)
    (j J : ℤ) {κ : ℂ} (hκ : κ ∈ horizontalFourierDomain y hy) (E : ℂ) :
    AnalyticAt ℂ (fun F => continuedEnergyFourierCoefficient y hy F j J κ) E := by
  have hk := re_gt_neg_half_of_mem_continuation (horizontalContinuation y hy) hκ
  have hs : 0 < (exponent κ).re := by
    norm_num [exponent, Complex.add_re]
    linarith
  have he := (analyticAt_const (v := continuedFourierCoefficient y hy j J κ)).add
    (analyticAt_energyFourierCorrection_energy y hy j J hs E)
  simpa only [Pi.add_def, continuedEnergyFourierCoefficient_eq_base_add_correction] using he

/-- Entire analyticity in energy holds uniformly as a statement over the complete parameter domain. -/
theorem analyticOnNhd_continuedEnergyFourierCoefficient_energy (y : ℝ) (hy : 0 < y)
    (j J : ℤ) {κ : ℂ} (hκ : κ ∈ horizontalFourierDomain y hy) :
    AnalyticOnNhd ℂ (fun E => continuedEnergyFourierCoefficient y hy E j J κ) univ :=
  fun E _ => analyticAt_continuedEnergyFourierCoefficient_energy y hy j J hκ E

/-- Along the actual observation row the compact family is the original series throughout Re s>1. -/
theorem continuedSeedOn_horizontalRow_eq_series (y : ℝ) (hy : 0 < y) (E : ℂ)
    (J : ℤ) {κ : ℂ} (hκ : (1 / 2 : ℝ) < κ.re)
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    continuedSeedOn (horizontalRow y) (horizontalRow_subset_upperHalfPlaneSet y hy) E J κ
      ⟨Complex.mk x y, ⟨x, hx, rfl⟩⟩ =
        complexPoincareSeries E J (exponent κ) (rowPoint y hy x) := by
  rw [continuedSeedOn_eq_series_full_convergence _ _ E J hκ]
  rw [show ofComplex (Complex.mk x y) = rowPoint y hy x from ofComplex_apply (rowPoint y hy x)]

/-- On the full original convergence half-plane the new family is the literal ordinary coefficient. -/
theorem continuedEnergyFourierCoefficient_eq_series (y : ℝ) (hy : 0 < y) (E : ℂ)
    (j J : ℤ) {κ : ℂ} (hκ : (1 / 2 : ℝ) < κ.re) :
    continuedEnergyFourierCoefficient y hy E j J κ =
      ∫ x in (0 : ℝ)..1, cuspFourierMode (-j) x *
        complexPoincareSeries E J (exponent κ) (rowPoint y hy x) :=
  horizontalFourierFunctional_eq_intervalIntegral y j _ _
    (continuedSeedOn_horizontalRow_eq_series y hy E J hκ)

/-- The actual original-series Fourier integrand is genuinely interval integrable on Re s>1. -/
theorem intervalIntegrable_continuedEnergyFourierIntegrand (y : ℝ) (hy : 0 < y)
    (E : ℂ) (j J : ℤ) {κ : ℂ} (hκ : (1 / 2 : ℝ) < κ.re) :
    IntervalIntegrable (fun x => cuspFourierMode (-j) x *
      complexPoincareSeries E J (exponent κ) (rowPoint y hy x)) volume 0 1 :=
  intervalIntegrable_horizontalFourierRepresentative y j
    (continuedSeedOn (horizontalRow y) (horizontalRow_subset_upperHalfPlaneSet y hy) E J κ)
    _ (continuedSeedOn_horizontalRow_eq_series y hy E J hκ)

/-- The general-energy threshold coefficient is an ordinary integral of the actual global seed. -/
def generalThresholdFourierCoefficient (y : ℝ) (hy : 0 < y) (E : ℂ) (j J : ℤ) : ℂ :=
  ∫ x in (0 : ℝ)..1, cuspFourierMode (-j) x * generalThresholdSeed E J (rowPoint y hy x)

/-- The global threshold Fourier integrand is continuous, hence genuinely interval integrable. -/
theorem intervalIntegrable_generalThresholdFourierIntegrand (y : ℝ) (hy : 0 < y)
    (E : ℂ) (j J : ℤ) :
    IntervalIntegrable (fun x => cuspFourierMode (-j) x *
      generalThresholdSeed E J (rowPoint y hy x)) volume 0 1 :=
  ((contDiff_cuspFourierMode (-j)).continuous.mul
    ((continuous_generalThresholdSeed E J).comp (continuous_rowPoint y hy))).intervalIntegrable 0 1

/-- The analytic family at zero equals the actual global general-energy threshold integral. -/
theorem continuedEnergyFourierCoefficient_zero (y : ℝ) (hy : 0 < y) (E : ℂ) (j J : ℤ) :
    continuedEnergyFourierCoefficient y hy E j J 0 =
      generalThresholdFourierCoefficient y hy E j J := by
  unfold continuedEnergyFourierCoefficient generalThresholdFourierCoefficient
  apply horizontalFourierFunctional_eq_intervalIntegral
  intro x hx
  exact (generalThresholdSeed_eq_compact (horizontalRow y)
    (horizontalRow_subset_upperHalfPlaneSet y hy) E J (rowPoint y hy x) ⟨x, hx, rfl⟩).symm

/-- The literal threshold integral is entire in complex energy. -/
theorem analyticAt_generalThresholdFourierCoefficient_energy (y : ℝ) (hy : 0 < y)
    (j J : ℤ) (E : ℂ) :
    AnalyticAt ℂ (fun F => generalThresholdFourierCoefficient y hy F j J) E := by
  simpa only [continuedEnergyFourierCoefficient_zero] using
    analyticAt_continuedEnergyFourierCoefficient_energy y hy j J
      (zero_mem_horizontalFourierDomain y hy) E

/-- The ordinary Fourier functional preserves the actual compact supremum bound. -/
theorem norm_continuedEnergyFourierCoefficient_le (y : ℝ) (hy : 0 < y) (E : ℂ)
    (j J : ℤ) (κ : ℂ) :
    ‖continuedEnergyFourierCoefficient y hy E j J κ‖ ≤
      ‖continuedSeedOn (horizontalRow y) (horizontalRow_subset_upperHalfPlaneSet y hy) E J κ‖ :=
  norm_horizontalFourierFunctional_apply_le y j _

/-- At bounded complex energy, the original radius and one constant work for both integer spins. -/
theorem exists_continuedEnergyFourierCoefficient_bound (y : ℝ) (hy : 0 < y) (B : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (E : ℂ), ‖E‖ ≤ B → ∀ (j J : ℤ) (κ : ℂ),
      ‖κ‖ ≤ (horizontalContinuation y hy).radius →
      ‖continuedEnergyFourierCoefficient y hy E j J κ‖ ≤
        C * (1 + (J : ℝ) ^ 2 + ‖E‖) := by
  obtain ⟨C, hC, hb⟩ := exists_continuedSeedOn_norm_bound (horizontalRow y)
    (horizontalRow_subset_upperHalfPlaneSet y hy) B
  exact ⟨C, hC, fun E hE j J κ hκ =>
    (norm_continuedEnergyFourierCoefficient_le y hy E j J κ).trans (hb E hE J κ hκ)⟩

/-- One positive threshold disk works for every bounded energy and every input and output spin. -/
theorem exists_uniform_continuedEnergyFourierCoefficient_bound (y : ℝ) (hy : 0 < y)
    (B : ℝ) :
    ∃ r C : ℝ, 0 < r ∧ r ≤ 1 / 8 ∧ 0 < C ∧
      ∀ (E : ℂ), ‖E‖ ≤ B → ∀ (j J : ℤ) (κ : ℂ), ‖κ‖ ≤ r →
        ‖continuedEnergyFourierCoefficient y hy E j J κ‖ ≤
          C * (1 + (J : ℝ) ^ 2 + ‖E‖) := by
  obtain ⟨C, hC, hb⟩ := exists_continuedEnergyFourierCoefficient_bound y hy B
  exact ⟨(horizontalContinuation y hy).radius, C,
    (horizontalContinuation y hy).radius_pos, (horizontalContinuation y hy).radius_le_eighth,
    hC, hb⟩

/-- The literal general-energy threshold coefficients satisfy the same uniform bound. -/
theorem generalThresholdFourierCoefficient_uniform_bound (y : ℝ) (hy : 0 < y) (B : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (E : ℂ), ‖E‖ ≤ B → ∀ (j J : ℤ),
      ‖generalThresholdFourierCoefficient y hy E j J‖ ≤ C * (1 + (J : ℝ) ^ 2 + ‖E‖) := by
  obtain ⟨C, hC, hb⟩ := exists_continuedEnergyFourierCoefficient_bound y hy B
  refine ⟨C, hC, ?_⟩
  intro E hE j J
  rw [← continuedEnergyFourierCoefficient_zero y hy E j J]
  exact hb E hE j J 0 (by simpa using (horizontalContinuation y hy).radius_pos.le)

end GapFamily.Analytic.PoincareEnergyFourier
