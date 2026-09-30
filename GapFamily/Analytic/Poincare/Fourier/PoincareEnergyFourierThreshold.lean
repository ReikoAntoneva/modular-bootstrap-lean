import GapFamily.Analytic.Poincare.Fourier.PoincareEnergyFourierRegroup
import GapFamily.Analytic.Poincare.Fourier.PoincareGeneralFourier
import GapFamily.Analytic.Poincare.Arithmetic.PoincareCentralQuotient

/-! Actual continued general-energy coefficients and their convergent threshold energy tail.
The zero-energy central contribution is kept separate from the convergent energy subtraction.
-/
noncomputable section
namespace GapFamily.Analytic.PoincareEnergyFourier
open Set MeasureTheory CuspFourierCutoff PoincareFourierContinuation
open PoincareEnergyContinuation PoincareCentralZeta
open PoincareCentralFactor PoincareFourierRemainder
open scoped Topology

/-- The actual general-energy family has an ordinarily integrated arithmetic correction
on its whole constructed continuation region, including the threshold neighborhood. -/
theorem continuedEnergyFourierCoefficient_eq_base_add_kloosterman
    (y : ℝ) (hy : 0 < y) (E : ℂ) (j J : ℤ) {κ : ℂ}
    (hκ : κ ∈ horizontalFourierDomain y hy) :
    continuedEnergyFourierCoefficient y hy E j J κ =
      continuedFourierCoefficient y hy j J κ + energyFourierDirect y E j J (exponent κ) +
        ∑' n : ℕ, kloostermanSum j J n *
          ∫ t : ℝ, energyFourierKernel (n + 1 : ℕ) y E j J (exponent κ) t := by
  have hs : 0 < (exponent κ).re := by
    have hh := re_gt_neg_half_of_mem_continuation (horizontalContinuation y hy) hκ
    norm_num [exponent, Complex.add_re]
    linarith
  rw [continuedEnergyFourierCoefficient_eq_base_add_correction,
    energyFourierCorrection_eq_direct_add_kloosterman y hy E j J hs]
  ring

/-- The complete denominator correction has a genuine HasSum at each continued parameter. -/
theorem hasSum_kloosterman_continuedEnergyFourierCoefficient
    (y : ℝ) (hy : 0 < y) (E : ℂ) (j J : ℤ) {κ : ℂ}
    (hκ : κ ∈ horizontalFourierDomain y hy) :
    HasSum (fun n : ℕ => kloostermanSum j J n *
      ∫ t : ℝ, energyFourierKernel (n + 1 : ℕ) y E j J (exponent κ) t)
      (continuedEnergyFourierCoefficient y hy E j J κ -
        continuedFourierCoefficient y hy j J κ - energyFourierDirect y E j J (exponent κ)) := by
  have hs : 0 < (exponent κ).re := by
    have hh := re_gt_neg_half_of_mem_continuation (horizontalContinuation y hy) hκ
    norm_num [exponent, Complex.add_re]
    linarith
  rw [continuedEnergyFourierCoefficient_eq_base_add_correction]
  convert hasSum_kloosterman_energyFourier y hy E j J hs using 1
  ring

/-- Threshold energy correction is norm summable for every complex energy and both spins. -/
theorem summable_norm_kloosterman_energyFourier_threshold
    (y : ℝ) (hy : 0 < y) (E : ℂ) (j J : ℤ) :
    Summable (fun n : ℕ => ‖kloostermanSum j J n *
      ∫ t : ℝ, energyFourierKernel (n + 1 : ℕ) y E j J (1 / 2 : ℂ) t‖) :=
  summable_norm_kloosterman_energyFourier y hy E j J (by norm_num)

/-- Literal ordinary Fourier coefficient of the actual global threshold seed at any energy. -/
theorem generalThresholdFourierCoefficient_eq_base_add_kloosterman
    (y : ℝ) (hy : 0 < y) (E : ℂ) (j J : ℤ) :
    generalThresholdFourierCoefficient y hy E j J =
      thresholdFourierCoefficient y hy j J + energyFourierDirect y E j J (1 / 2 : ℂ) +
        ∑' n : ℕ, kloostermanSum j J n *
          ∫ t : ℝ, energyFourierKernel (n + 1 : ℕ) y E j J (1 / 2 : ℂ) t := by
  have h := continuedEnergyFourierCoefficient_eq_base_add_kloosterman
    y hy E j J (zero_mem_horizontalFourierDomain y hy)
  simpa only [continuedEnergyFourierCoefficient_zero, continuedFourierCoefficient_zero,
    exponent, add_zero] using h

/-- At nonzero output spin the actual threshold coefficient has the proved local
central-zeta factor, zero-energy remainder, and normally convergent energy correction.
No divergent central integral is separated or summed at the threshold. -/
theorem generalThresholdFourierCoefficient_eq_central_add_energy
    (y : ℝ) (hy : 0 < y) (E : ℂ) (j J : ℤ) (hj : j ≠ 0) :
    generalThresholdFourierCoefficient y hy E j J =
      (if j = J then (y : ℂ) ^ (1 / 2 : ℂ) *
        Complex.exp (-2 * (Real.pi : ℂ) * E * (y : ℂ)) else 0) +
      centralFourierFactor y j 0 * centralZeta j J 0 +
      fourierRemainder y j J (1 / 2 : ℂ) +
        ∑' n : ℕ, kloostermanSum j J n *
          ∫ t : ℝ, energyFourierKernel (n + 1 : ℕ) y E j J (1 / 2 : ℂ) t := by
  rw [generalThresholdFourierCoefficient_eq_base_add_kloosterman,
    thresholdFourierCoefficient_eq_centralZeta y hy j J hj]
  classical
  by_cases h : j = J <;> simp only [energyFourierDirect, h, ite_true, ite_false] <;> ring

end GapFamily.Analytic.PoincareEnergyFourier
