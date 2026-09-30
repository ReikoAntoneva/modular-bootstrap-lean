import BTZEntropy.Analytic.SaddleJet
import BTZEntropy.Analytic.AmplitudeJet
import BTZEntropy.Analytic.SaddleGaussian
import BTZEntropy.Analytic.SaddleTailMoment

/-!
# Integration of the actual saddle jet

Real scale derivatives of the actual integrand agree with its holomorphic
jet. Its coefficient polynomials have every weighted Gaussian norm moment,
and their whole-line integrals are the designated Gaussian functional.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace BTZEntropy

/-- Along every real contour coordinate, the amplitude argument remains in the
positive half-plane and the rational saddle denominator never vanishes. -/
theorem continuous_rescaledSaddleIntegrand_real_coordinate (φ : SmoothKernel)
    {β : ℝ} (hβ : 0 < β) (ε : ℝ) :
    Continuous (fun t : ℝ => rescaledSaddleIntegrand (complexAmplitude φ) β t (ε : ℂ)) := by
  have hre (t : ℝ) : ((β : ℂ) + Complex.I * (ε : ℂ) * (t : ℂ)).re = β := by
    simp
  have hn (t : ℝ) : (β : ℂ) + Complex.I * (ε : ℂ) * (t : ℂ) ≠ 0 := by
    intro hz
    have he := congrArg Complex.re hz
    rw [hre] at he
    exact (ne_of_gt hβ) he
  have ha : Continuous (fun t : ℝ =>
      complexAmplitude φ ((β : ℂ) + Complex.I * (ε : ℂ) * (t : ℂ))) := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (analyticAt_complexAmplitude φ (by simpa only [hre] using hβ)).continuousAt.comp
      (by fun_prop)
  unfold rescaledSaddleIntegrand
  apply ha.mul
  apply Complex.continuous_exp.comp
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro t
  exact mul_ne_zero (pow_ne_zero 2 (by exact_mod_cast ne_of_gt hβ)) (hn t)

theorem rescaledSaddleIntegrand_eq_actual (A : ℂ → ℂ) (x t : ℝ) (ε : ℂ) :
    rescaledSaddleIntegrand A (saddleBeta x) t ε =
      actualSaddleIntegrand A x ((t : ℂ) * Complex.I) ε := by
  unfold rescaledSaddleIntegrand actualSaddleIntegrand rationalSaddlePhase
  have hmul : Complex.I * ε * (t : ℂ) = ε * ((t : ℂ) * Complex.I) := by ring
  rw [hmul, mul_pow, Complex.I_sq]
  congr 2
  ring

/-- The actual real jet is exactly the polynomial prescribed by the coefficient algorithm. -/
theorem iteratedDeriv_rescaledSaddleIntegrand_real_zero (φ : SmoothKernel)
    {x : ℝ} (hx : 0 < x) (N : ℕ) (t : ℝ) {n : ℕ} (hn : n ≤ N) :
    iteratedDeriv n
      (fun ε : ℝ => rescaledSaddleIntegrand (complexAmplitude φ) (saddleBeta x) t (ε : ℂ)) 0 =
      (Real.exp (-saddleHessian x * t ^ 2 / 2) : ℂ) * (n.factorial : ℂ) *
        ((amplitudeTaylor φ x N * phaseExponential x N).coeff n).eval₂
          Complex.ofRealHom ((t : ℂ) * Complex.I) := by
  simp_rw [rescaledSaddleIntegrand_eq_actual]
  have hA : AnalyticAt ℂ (complexAmplitude φ) (saddleBeta x) :=
    analyticAt_complexAmplitude φ (by simpa using saddleBeta_pos hx)
  have ha := analyticAt_actualSaddleIntegrand hx hA ((t : ℂ) * Complex.I)
  rw [iteratedDeriv_comp_ofReal_of_analyticAt
    (by simpa only [Complex.ofReal_zero] using ha)]
  exact iteratedDeriv_actualSaddleIntegrand_imaginary φ hx N
    (analyticAt_complexAmplitude φ (by simpa using saddleBeta_pos hx))
    (fun k _ => iteratedDeriv_complexAmplitude_ofReal φ (saddleBeta_pos hx) k) t hn

/-- Polynomial Gaussian functions have every absolute-power weighted norm moment. -/
theorem integrable_abs_pow_norm_polynomial_gaussian {h : ℝ} (hh : 0 < h)
    (p : Polynomial ℝ) (q : ℕ) :
    Integrable (fun t : ℝ => |t| ^ q *
      ‖p.eval₂ Complex.ofRealHom ((t : ℂ) * Complex.I) *
        (Real.exp (-h * t ^ 2 / 2) : ℂ)‖) := by
  have hi := (integrable_polynomial_gaussian hh (Polynomial.X ^ q * p)).norm
  simpa only [Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
    mul_one, mul_assoc] using hi

/-- Every real scale derivative at zero is integrable over the saddle coordinate. -/
theorem integrable_rescaledSaddleIntegrand_real_jet (φ : SmoothKernel)
    {x : ℝ} (hx : 0 < x) (n : ℕ) :
    Integrable (fun t : ℝ => iteratedDeriv n
      (fun ε : ℝ => rescaledSaddleIntegrand (complexAmplitude φ) (saddleBeta x) t (ε : ℂ)) 0) := by
  let p := (amplitudeTaylor φ x n * phaseExponential x n).coeff n
  have hi := (integrable_polynomial_gaussian (saddleHessian_pos hx) p).const_mul
    (n.factorial : ℂ)
  refine hi.congr ?_
  filter_upwards [] with t
  rw [iteratedDeriv_rescaledSaddleIntegrand_real_zero φ hx n t le_rfl]
  dsimp [p]
  ring

/-- The actual real saddle jet has all polynomially weighted norm moments. -/
theorem integrable_abs_pow_norm_rescaledSaddleIntegrand_real_jet (φ : SmoothKernel)
    {x : ℝ} (hx : 0 < x) (n q : ℕ) :
    Integrable (fun t : ℝ => |t| ^ q * ‖iteratedDeriv n
      (fun ε : ℝ => rescaledSaddleIntegrand (complexAmplitude φ) (saddleBeta x) t (ε : ℂ)) 0‖) := by
  let p := (amplitudeTaylor φ x n * phaseExponential x n).coeff n
  have hi := (integrable_abs_pow_norm_polynomial_gaussian (saddleHessian_pos hx) p q).const_mul
    ‖(n.factorial : ℂ)‖
  refine hi.congr ?_
  filter_upwards [] with t
  rw [iteratedDeriv_rescaledSaddleIntegrand_real_zero φ hx n t le_rfl]
  dsimp [p]
  simp only [norm_mul]
  ring

/-- Integrating a retained actual jet produces the coefficient functional exactly. -/
theorem integral_rescaledSaddleIntegrand_real_jet (φ : SmoothKernel)
    {x : ℝ} (hx : 0 < x) (N : ℕ) {n : ℕ} (hn : n ≤ N) :
    (∫ t : ℝ, iteratedDeriv n
      (fun ε : ℝ => rescaledSaddleIntegrand (complexAmplitude φ) (saddleBeta x) t (ε : ℂ)) 0) =
      (Real.sqrt (2 * Real.pi / saddleHessian x) : ℂ) * (n.factorial : ℂ) *
        (gaussianEvaluation (saddleHessian x)
          ((amplitudeTaylor φ x N * phaseExponential x N).coeff n) : ℂ) := by
  let p := (amplitudeTaylor φ x N * phaseExponential x N).coeff n
  calc
    _ = ∫ t : ℝ, (n.factorial : ℂ) *
        (p.eval₂ Complex.ofRealHom ((t : ℂ) * Complex.I) *
          (Real.exp (-saddleHessian x * t ^ 2 / 2) : ℂ)) := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [iteratedDeriv_rescaledSaddleIntegrand_real_zero φ hx N t hn]
      dsimp [p]
      ring
    _ = _ := by
      rw [integral_const_mul, integral_polynomial_gaussian_eq_evaluation (saddleHessian_pos hx)]
      dsimp [p]
      ring

end BTZEntropy
