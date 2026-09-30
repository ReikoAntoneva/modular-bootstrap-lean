import BTZEntropy.Analytic.SaddleWhole
import BTZEntropy.Analytic.SaddleTaylorCount
import BTZEntropy.Analytic.SaddleEntropy

/-!
# The all-order BTZ count expansion

This theorem concerns the actual convergent inverse Laplace contour and the
designated finite Taylor--Gaussian coefficient algorithm. Every local and
nonlocal estimate is proved before the final normalization.
-/

noncomputable section

namespace BTZEntropy

private theorem real_normalized_error_le {I : ℂ} {A T : ℝ} (hA : 0 < A) :
    |I.re / A - T| ≤ ‖I - ((A * T : ℝ) : ℂ)‖ / A := by
  have heq : I.re / A - T = (I.re - T * A) / A := by
    field_simp
  rw [heq, abs_div, abs_of_pos hA]
  apply div_le_div_of_nonneg_right _ hA.le
  convert Complex.abs_re_le_norm (I - ((A * T : ℝ) : ℂ)) using 1 <;>
    simp [mul_comm]

/-- Every finite inverse-charge order is the prescribed BTZ coefficient,
uniformly over every positive compact energy-ratio interval. -/
theorem uniformSaddleCountExpansion_btzCount (φ : SmoothKernel) :
    UniformSaddleCountExpansion φ (btzCount φ) := by
  intro P L U hL hLU
  obtain ⟨C, hC, hTaylor⟩ := actualRescaledSaddle_wholeTaylor_uniform φ hL hLU (2 * P + 1)
  obtain ⟨m, M, hm, hM, hpref⟩ := saddlePrefactor_uniform_bounds φ hL hLU
  let a₀ := 2 * Real.pi * m
  have ha₀ : 0 < a₀ := by dsimp [a₀]; positivity
  refine ⟨C / a₀, div_pos hC ha₀, 1, le_rfl, ?_⟩
  intro c hc x hx
  have hxp : 0 < x := hL.trans_le hx.1
  have hcp : 0 < c := zero_lt_one.trans_le hc
  let ε := (Real.sqrt c)⁻¹
  have hε : 0 < ε := inv_pos.mpr (Real.sqrt_pos.mpr hcp)
  have hε1 : ε ≤ 1 := inv_le_one_of_one_le₀ (Real.one_le_sqrt.mpr hc)
  have hεsq : ε ^ 2 = c⁻¹ := by
    dsimp [ε]
    rw [inv_pow, Real.sq_sqrt hcp.le]
  have hpow : ε ^ (2 * P + 1 + 1) = (c ^ (P + 1))⁻¹ := by
    rw [show 2 * P + 1 + 1 = 2 * (P + 1) by omega, pow_mul, hεsq, inv_pow]
  have hAnorm : a₀ ≤ gaussianCountNormalization φ x := by
    unfold gaussianCountNormalization
    exact mul_le_mul_of_nonneg_left (hpref x hx).1 (by positivity)
  have hA := gaussianCountNormalization_pos φ hxp
  have herror := hTaylor x hx ε hε hε1
  rw [integralTaylorPolynomial_rescaledSaddleIntegrand φ hxp P ε, hεsq, hpow] at herror
  rw [btzCount_div_scale φ hxp hcp]
  change |(rescaledBTZContour φ x ε).re / gaussianCountNormalization φ x - _| ≤ _
  calc
    _ ≤ ‖rescaledBTZContour φ x ε -
        ((gaussianCountNormalization φ x *
          (1 + (countCorrectionPolynomial φ x P).eval c⁻¹) : ℝ) : ℂ)‖ /
          gaussianCountNormalization φ x := real_normalized_error_le hA
    _ ≤ (C * (c ^ (P + 1))⁻¹) / gaussianCountNormalization φ x :=
      div_le_div_of_nonneg_right herror hA.le
    _ ≤ (C * (c ^ (P + 1))⁻¹) / a₀ :=
      div_le_div_of_nonneg_left (by positivity) ha₀ hAnorm
    _ = (C / a₀) / c ^ (P + 1) := by ring

end BTZEntropy
