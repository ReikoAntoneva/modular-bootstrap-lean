import GapFamily.Analytic.Poincare.Fourier.PoincareLaplaceDifference
import GapFamily.Analytic.Transform.LaplaceKernelPairing
import GapFamily.Analytic.Transform.LaplaceRankReference

/-!
# The actual seed under both energy tests

Absolute product integrability permits integration of the literal seed
Fourier/height identity in the input energy. The resulting expression is
the actual identity-plus-corrected-kernel pairing, with its scalar rank
correction kept explicit. This module makes no positivity assertion.
-/

noncomputable section

namespace GapFamily.Analytic.PoincareEnergyFourier

open MeasureTheory PoincareEnergyContinuation

/-- Removing the separately integrable rank correction preserves ordinary
absolute convergence of the two-energy holomorphic-kernel pairing. -/
theorem integrable_laplaceTest_fullKernelHol_pair (j J : ℤ) (k l : ℕ) :
    Integrable (fun p : ℝ × ℝ => (laplaceTest k p.1 : ℂ) *
      fullKernelHol j J p.1 p.2 * (laplaceTest l p.2 : ℂ))
      ((referenceMeasure j).prod (referenceMeasure J)) := by
  have hr := (scalarRankKernel_laplaceTest_integrable j J k l).ofReal (𝕜 := ℂ)
  simp only [RCLike.ofReal_eq_complex_ofReal] at hr
  convert (integrable_laplaceTest_correctedKernel_pair j J k l).sub hr using 1
  ext p
  simp only [Pi.sub_apply, correctedKernel]
  push_cast
  ring

/-- The input energy integral of the output transform is ordinary. -/
theorem integrable_laplaceTest_integral_fullKernelHol (j J : ℤ) (k l : ℕ) :
    Integrable (fun E : ℝ => (laplaceTest l E : ℂ) *
      ∫ e : ℝ, (laplaceTest k e : ℂ) * fullKernelHol j J e E ∂referenceMeasure j)
      (referenceMeasure J) := by
  convert (integrable_laplaceTest_fullKernelHol_pair j J k l).integral_prod_right using 1
  ext E
  dsimp only
  rw [integral_mul_const, mul_comm]

/-- Fubini identifies the full holomorphic-kernel pairing with the ordinary
input integral of its output Laplace transform. -/
theorem integral_laplaceTest_fullKernelHol_pair (j J : ℤ) (k l : ℕ) :
    (∫ p : ℝ × ℝ, (laplaceTest k p.1 : ℂ) *
      fullKernelHol j J p.1 p.2 * (laplaceTest l p.2 : ℂ)
        ∂((referenceMeasure j).prod (referenceMeasure J))) =
      ∫ E : ℝ, (laplaceTest l E : ℂ) *
        (∫ e : ℝ, (laplaceTest k e : ℂ) * fullKernelHol j J e E ∂referenceMeasure j)
          ∂referenceMeasure J := by
  rw [integral_prod_symm _ (integrable_laplaceTest_fullKernelHol_pair j J k l)]
  simp_rw [integral_mul_const, mul_comm]

private theorem integrable_laplaceTest_diagonal (j J : ℤ) (k l : ℕ) :
    Integrable (fun E : ℝ => (laplaceTest l E : ℂ) *
      (if j = J then (laplaceTest k E : ℂ) else 0)) (referenceMeasure J) := by
  by_cases h : j = J
  · subst j
    simpa only [ite_true, RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_mul, mul_comm] using
      (integrable_laplaceTest_product_referenceMeasure J k l).ofReal (𝕜 := ℂ)
  · simp [h]

private theorem integral_laplaceTest_diagonal (j J : ℤ) (k l : ℕ) :
    (∫ E : ℝ, (laplaceTest l E : ℂ) *
      (if j = J then (laplaceTest k E : ℂ) else 0) ∂referenceMeasure J) =
      if j = J then
        ((∫ E, laplaceTest k E * laplaceTest l E ∂referenceMeasure j) : ℂ) else 0 := by
  by_cases h : j = J
  · subst j
    simp only [ite_true, ← Complex.ofReal_mul, integral_complex_ofReal, mul_comm]
  · simp [h]

/-- The weighted literal Fourier/height test of the actual seed has ordinary
input reference integrability, including the scalar endpoint. -/
theorem integrable_generalThresholdSeed_fourier_height_pair
    (j J : ℤ) (k l : ℕ) :
    Integrable (fun E : ℝ => (laplaceTest l E : ℂ) *
      ∫ x : ℝ in 0..1, horizontalPhase (-j) x *
        (generalThresholdSeed E J (laplacePoint k x) /
            (Real.sqrt (laplaceHeight k) : ℂ) -
          generalThresholdSeed E J (laplacePoint (k + 1) x) /
            (Real.sqrt (laplaceHeight (k + 1)) : ℂ))) (referenceMeasure J) := by
  simp_rw [generalThresholdSeed_fourier_height_difference, mul_add]
  exact (integrable_laplaceTest_diagonal j J k l).add
    (integrable_laplaceTest_integral_fullKernelHol j J k l)

/-- The actual identity-plus-corrected-kernel energy pairing is precisely
the literal seed Fourier/height test integrated in input energy, plus the
actual scalar rank pairing. Every energy integral is ordinarily convergent. -/
theorem laplaceEnergyPairing_eq_generalThresholdSeed_pairing
    (j J : ℤ) (k l : ℕ) :
    laplaceEnergyPairing j J k l =
      (∫ E : ℝ, (laplaceTest l E : ℂ) *
        (∫ x : ℝ in 0..1, horizontalPhase (-j) x *
          (generalThresholdSeed E J (laplacePoint k x) /
              (Real.sqrt (laplaceHeight k) : ℂ) -
            generalThresholdSeed E J (laplacePoint (k + 1) x) /
              (Real.sqrt (laplaceHeight (k + 1)) : ℂ))) ∂referenceMeasure J) +
      ((∫ p : ℝ × ℝ,
        laplaceTest k p.1 * scalarRankKernel j J p.1 p.2 * laplaceTest l p.2
          ∂((referenceMeasure j).prod (referenceMeasure J)) : ℝ) : ℂ) := by
  have hr := (scalarRankKernel_laplaceTest_integrable j J k l).ofReal (𝕜 := ℂ)
  simp only [RCLike.ofReal_eq_complex_ofReal] at hr
  have heq (p : ℝ × ℝ) :
      (laplaceTest k p.1 : ℂ) * correctedKernel j J p.1 p.2 * (laplaceTest l p.2 : ℂ) =
        (laplaceTest k p.1 : ℂ) * fullKernelHol j J p.1 p.2 * (laplaceTest l p.2 : ℂ) +
          ((laplaceTest k p.1 * scalarRankKernel j J p.1 p.2 * laplaceTest l p.2 : ℝ) : ℂ) := by
    simp only [correctedKernel]
    push_cast
    ring
  unfold laplaceEnergyPairing
  simp_rw [heq, generalThresholdSeed_fourier_height_difference, mul_add]
  rw [integral_add (integrable_laplaceTest_fullKernelHol_pair j J k l) hr,
    integral_complex_ofReal, integral_laplaceTest_fullKernelHol_pair,
    integral_add (integrable_laplaceTest_diagonal j J k l)
      (integrable_laplaceTest_integral_fullKernelHol j J k l),
    integral_laplaceTest_diagonal]
  ring

end GapFamily.Analytic.PoincareEnergyFourier
