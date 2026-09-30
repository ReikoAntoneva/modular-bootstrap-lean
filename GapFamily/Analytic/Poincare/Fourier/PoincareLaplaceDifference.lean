import GapFamily.Analytic.Poincare.Fourier.PoincareFullFourierOutput
import GapFamily.Analytic.Transform.LaplaceTest

/-! Adjacent normalized heights of the actual canonical seed.  The scalar
threshold atom cancels, and the remaining ordinary energy integral contains
the endpoint-regularized Laplace test used in the spatial pairing. -/

noncomputable section
namespace GapFamily.Analytic.PoincareEnergyFourier
open Set MeasureTheory PoincareEnergyContinuation PoincareFourier

private theorem exp_laplaceHeight (k : ℕ) (E : ℝ) :
    Complex.exp (-2 * (Real.pi : ℂ) * (laplaceHeight k : ℂ) * (E : ℂ)) =
      (Real.exp (-2 * Real.pi * laplaceHeight k * E) : ℂ) := by
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring

theorem laplaceTest_complex_eq_height_difference (k : ℕ) (E : ℝ) :
    (laplaceTest k E : ℂ) =
      Complex.exp (-2 * (Real.pi : ℂ) * (laplaceHeight k : ℂ) * (E : ℂ)) -
        Complex.exp (-2 * (Real.pi : ℂ) * (laplaceHeight (k + 1) : ℂ) * (E : ℂ)) := by
  rw [exp_laplaceHeight, exp_laplaceHeight, laplaceTest_eq_height_difference]
  push_cast
  rfl

/-- Ordinary integrability at both positive heights justifies their difference,
including the scalar reference measure at its open endpoint. -/
theorem integrable_laplaceTest_fullKernelHol (k : ℕ) (E : ℂ) (j J : ℤ) :
    Integrable (fun e : ℝ => (laplaceTest k e : ℂ) * fullKernelHol j J e E)
      (referenceMeasure j) := by
  convert (integrable_fullKernelHol_laplace (laplaceHeight k) (laplaceHeight_pos k)
    E j J).sub (integrable_fullKernelHol_laplace (laplaceHeight (k + 1))
      (laplaceHeight_pos (k + 1)) E j J) using 1
  ext e
  simp only [Pi.sub_apply, laplaceTest_complex_eq_height_difference, sub_mul]

theorem integral_laplaceTest_fullKernelHol (k : ℕ) (E : ℂ) (j J : ℤ) :
    (∫ e : ℝ, (laplaceTest k e : ℂ) * fullKernelHol j J e E ∂referenceMeasure j) =
      (∫ e : ℝ,
        Complex.exp (-2 * (Real.pi : ℂ) * (laplaceHeight k : ℂ) * (e : ℂ)) *
          fullKernelHol j J e E ∂referenceMeasure j) -
      (∫ e : ℝ,
        Complex.exp (-2 * (Real.pi : ℂ) * (laplaceHeight (k + 1) : ℂ) * (e : ℂ)) *
          fullKernelHol j J e E ∂referenceMeasure j) := by
  simp_rw [laplaceTest_complex_eq_height_difference, sub_mul]
  exact integral_sub
    (integrable_fullKernelHol_laplace _ (laplaceHeight_pos k) E j J)
    (integrable_fullKernelHol_laplace _ (laplaceHeight_pos (k + 1)) E j J)

/-- The Fourier coefficient of the actual seed, normalized by the height,
has an ordinary direct term, a height-independent threshold term, and `Q_hol`.
-/
theorem normalized_generalThresholdFourierCoefficient (y : ℝ) (hy : 0 < y)
    (E : ℝ) (j J : ℤ) :
    generalThresholdFourierCoefficient y hy E j J / (Real.sqrt y : ℂ) =
      (if j = J then Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (E : ℂ)) else 0) +
      (if j = 0 then PoincareScalarFourier.scalarThresholdCoefficient J else 0) +
      ∫ e : ℝ, Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ)) *
        fullKernelHol j J e E ∂referenceMeasure j := by
  rw [generalThresholdFourierCoefficient_eq_full_laplace y hy E j J]
  have hn : (Real.sqrt y : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr hy)
  have he : -2 * (Real.pi : ℂ) * (E : ℂ) * (y : ℂ) =
      -2 * (Real.pi : ℂ) * (y : ℂ) * (E : ℂ) := by ring
  rw [he]
  split_ifs <;> field_simp <;> ring

/-- The actual output-side height difference annihilates the threshold atom.
This equality allows every real input energy, including vacuum input. -/
theorem generalThresholdFourierCoefficient_height_difference (k : ℕ)
    (E : ℝ) (j J : ℤ) :
    generalThresholdFourierCoefficient (laplaceHeight k) (laplaceHeight_pos k) E j J /
        (Real.sqrt (laplaceHeight k) : ℂ) -
      generalThresholdFourierCoefficient (laplaceHeight (k + 1))
        (laplaceHeight_pos (k + 1)) E j J / (Real.sqrt (laplaceHeight (k + 1)) : ℂ) =
      (if j = J then (laplaceTest k E : ℂ) else 0) +
        ∫ e : ℝ, (laplaceTest k e : ℂ) * fullKernelHol j J e E ∂referenceMeasure j := by
  rw [normalized_generalThresholdFourierCoefficient,
    normalized_generalThresholdFourierCoefficient, integral_laplaceTest_fullKernelHol,
    laplaceTest_complex_eq_height_difference]
  by_cases hd : j = J <;> simp only [hd, ite_true, ite_false] <;> ring

theorem horizontalPhase_eq_cuspFourierMode (j : ℤ) (x : ℝ) :
    horizontalPhase j x = cuspFourierMode j x := by
  unfold horizontalPhase cuspFourierMode
  congr 1
  ring

/-- The finite output test is the literal ordinary horizontal integral of the
actual global seed. No reconstructed or hypothetical spatial kernel is used.
-/
theorem generalThresholdSeed_fourier_height_difference (k : ℕ)
    (E : ℝ) (j J : ℤ) :
    (∫ x : ℝ in 0..1, horizontalPhase (-j) x *
      (generalThresholdSeed E J (laplacePoint k x) / (Real.sqrt (laplaceHeight k) : ℂ) -
        generalThresholdSeed E J (laplacePoint (k + 1) x) /
          (Real.sqrt (laplaceHeight (k + 1)) : ℂ))) =
      (if j = J then (laplaceTest k E : ℂ) else 0) +
        ∫ e : ℝ, (laplaceTest k e : ℂ) * fullKernelHol j J e E ∂referenceMeasure j := by
  have hp (n : ℕ) (x : ℝ) :
      laplacePoint n x = rowPoint (laplaceHeight n) (laplaceHeight_pos n) x := rfl
  simp_rw [horizontalPhase_eq_cuspFourierMode, hp, mul_sub, ← mul_div_assoc]
  rw [intervalIntegral.integral_sub
    ((intervalIntegrable_generalThresholdFourierIntegrand _ (laplaceHeight_pos k) E j J).div_const _)
    ((intervalIntegrable_generalThresholdFourierIntegrand _ (laplaceHeight_pos (k + 1)) E j J).div_const _),
    intervalIntegral.integral_div, intervalIntegral.integral_div]
  exact generalThresholdFourierCoefficient_height_difference k E j J

/-- All output spins remain absolutely summable after the finite height
difference, with ordinary reference integrals before the spin sum. -/
theorem summable_integral_norm_laplaceTest_fullKernelHol (k : ℕ) (E : ℂ) (J : ℤ) :
    Summable (fun j : ℤ => ∫ e : ℝ,
      ‖(laplaceTest k e : ℂ) * fullKernelHol j J e E‖ ∂referenceMeasure j) := by
  apply ((summable_integral_norm_fullKernelHol_laplace _ (laplaceHeight_pos k) E J).add
    (summable_integral_norm_fullKernelHol_laplace _ (laplaceHeight_pos (k + 1)) E J)).of_nonneg_of_le
  · exact fun j => integral_nonneg fun _ => norm_nonneg _
  · intro j
    rw [← integral_add
      (integrable_fullKernelHol_laplace _ (laplaceHeight_pos k) E j J).norm
      (integrable_fullKernelHol_laplace _ (laplaceHeight_pos (k + 1)) E j J).norm]
    apply integral_mono_ae (integrable_laplaceTest_fullKernelHol k E j J).norm
      ((integrable_fullKernelHol_laplace _ (laplaceHeight_pos k) E j J).norm.add
        (integrable_fullKernelHol_laplace _ (laplaceHeight_pos (k + 1)) E j J).norm)
    exact Filter.Eventually.of_forall fun e => by
      dsimp only [Pi.add_apply]
      rw [laplaceTest_complex_eq_height_difference, sub_mul]
      exact norm_sub_le _ _

end GapFamily.Analytic.PoincareEnergyFourier
