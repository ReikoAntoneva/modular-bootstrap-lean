import BTZEntropy.Analytic.SaddleCount
import BTZEntropy.Analytic.ContourAmplitude

/-!
# Arbitrary-order tail bound in the Gaussian coordinate

The exact rescaled integrand retains the fixed phase loss outside a moving
cutoff. The amplitude's uniform integrable bound scales by the reciprocal
parameter, which is dominated by exponential suppression to every order.
-/

noncomputable section

open MeasureTheory

namespace BTZEntropy

/-- The integral of the absolute rescaled tail is exponentially suppressed,
with the exact dilation factor displayed. -/
theorem integral_norm_actualRescaledSaddleIntegrand_outside_le
    (φ : SmoothKernel) {L U x ε R : ℝ}
    (hL : 0 < L) (hx : x ∈ Set.Icc L U) (hε : 0 < ε) (hR : 0 ≤ R) :
    (∫ t in {t : ℝ | R ≤ |ε * t|},
      ‖rescaledSaddleIntegrand (complexAmplitude φ) (saddleBeta x) t (ε : ℂ)‖) ≤
      Real.exp (-(ε ^ 2)⁻¹ * contourLoss L R) * ε⁻¹ *
        (∫ t : ℝ, ‖complexAmplitude φ (saddleContour (saddleBeta x) t)‖) := by
  have hxp : 0 < x := hL.trans_le hx.1
  have hc : 0 ≤ (ε ^ 2)⁻¹ := by positivity
  have hid : (ε ^ 2)⁻¹ * ε ^ 2 = 1 := inv_mul_cancel₀ (by positivity)
  let a : ℝ → ℝ := fun t => ‖complexAmplitude φ (saddleContour (saddleBeta x) (ε * t))‖
  have ha : Integrable a :=
    (integrable_complexAmplitude_contour φ (saddleBeta_pos hxp)).norm.comp_mul_left'
      (ne_of_gt hε)
  have hf := (integrable_rescaledBTZContour φ hxp (ne_of_gt hε)).norm
  calc
    _ ≤ ∫ t in {t : ℝ | R ≤ |ε * t|},
        Real.exp (-(ε ^ 2)⁻¹ * contourLoss L R) * a t := by
      apply integral_mono_ae hf.integrableOn (ha.const_mul _).integrableOn
      filter_upwards [ae_restrict_mem (measurableSet_le measurable_const
        ((continuous_const.mul continuous_id).abs.measurable))] with t ht
      rw [rescaledSaddleIntegrand_eq_original φ hxp hid, norm_mul]
      exact (mul_le_mul_of_nonneg_left
        (norm_normalizedSaddleExponential_le_outside hL hx hc hR ht) (norm_nonneg _)).trans_eq
        (mul_comm _ _)
    _ = Real.exp (-(ε ^ 2)⁻¹ * contourLoss L R) *
        ∫ t in {t : ℝ | R ≤ |ε * t|}, a t := integral_const_mul _ _
    _ ≤ Real.exp (-(ε ^ 2)⁻¹ * contourLoss L R) * ∫ t : ℝ, a t := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact setIntegral_le_integral ha (Filter.Eventually.of_forall (fun t => norm_nonneg _))
    _ = _ := by
      dsimp only [a]
      rw [Measure.integral_comp_mul_left (fun t : ℝ =>
        ‖complexAmplitude φ (saddleContour (saddleBeta x) t)‖) ε,
        abs_of_pos (inv_pos.mpr hε), smul_eq_mul]
      ring

/-- Uniform absolute tail control to every prescribed small-parameter power. -/
theorem actualRescaledSaddle_tail_uniform (φ : SmoothKernel) {L U R : ℝ}
    (hL : 0 < L) (hLU : L ≤ U) (hR : 0 < R) (N : ℕ) :
    ∃ C > 0, ∀ x ∈ Set.Icc L U, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      (∫ t in {t : ℝ | R ≤ |ε * t|},
        ‖rescaledSaddleIntegrand (complexAmplitude φ) (saddleBeta x) t (ε : ℂ)‖) ≤
          C * ε ^ N := by
  obtain ⟨M, hM, hbM⟩ := complexAmplitude_contour_integral_bounded φ
    (βmax := saddleBeta L) (saddleBeta_pos (hL.trans_le hLU))
  have hη := contourLoss_pos hL hR
  let C : ℝ := ((N + 1).factorial : ℝ) / contourLoss L R ^ (N + 1) * M
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro x hx ε hε hε1
  have hc : 0 < (ε ^ 2)⁻¹ := by positivity
  have hpow : ε ^ (2 * N + 1) ≤ ε ^ N :=
    pow_le_pow_of_le_one hε.le hε1 (by omega)
  calc
    _ ≤ Real.exp (-(ε ^ 2)⁻¹ * contourLoss L R) * ε⁻¹ *
        (∫ t : ℝ, ‖complexAmplitude φ (saddleContour (saddleBeta x) t)‖) :=
      integral_norm_actualRescaledSaddleIntegrand_outside_le φ hL hx hε hR.le
    _ ≤ Real.exp (-(ε ^ 2)⁻¹ * contourLoss L R) * ε⁻¹ * M := by
      exact mul_le_mul_of_nonneg_left (hbM _ (saddleBeta_mem_Icc hL hx)) (by positivity)
    _ ≤ ((N + 1).factorial : ℝ) /
        (contourLoss L R ^ (N + 1) * ((ε ^ 2)⁻¹) ^ (N + 1)) * ε⁻¹ * M := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (exp_neg_mul_le_factorial hc hη (N + 1)) (by positivity)) hM.le
    _ = C * ε ^ (2 * N + 1) := by
      dsimp [C]
      rw [inv_pow, div_mul_eq_div_div, div_inv_eq_mul, ← pow_mul]
      rw [show 2 * (N + 1) = (2 * N + 1) + 1 by omega, pow_succ]
      field_simp
      simp [pow_succ, mul_comm]
    _ ≤ C * ε ^ N := mul_le_mul_of_nonneg_left hpow hC.le

/-- The same uniform bound for the complex tail integral itself. -/
theorem norm_actualRescaledSaddle_tail_uniform (φ : SmoothKernel) {L U R : ℝ}
    (hL : 0 < L) (hLU : L ≤ U) (hR : 0 < R) (N : ℕ) :
    ∃ C > 0, ∀ x ∈ Set.Icc L U, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ‖∫ t in {t : ℝ | R ≤ |ε * t|},
        rescaledSaddleIntegrand (complexAmplitude φ) (saddleBeta x) t (ε : ℂ)‖ ≤
          C * ε ^ N := by
  obtain ⟨C, hC, hb⟩ := actualRescaledSaddle_tail_uniform φ hL hLU hR N
  exact ⟨C, hC, fun x hx ε hε hε1 =>
    (norm_integral_le_integral_norm _).trans (hb x hx ε hε hε1)⟩

end BTZEntropy
