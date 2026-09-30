import BTZEntropy.Coefficient
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Exact phase loss on the vertical BTZ contour

The identities and estimates below concern the actual rational BTZ phase.
They separate the local Gaussian estimate from the positive phase loss off
any fixed saddle window. An estimate for the amplitude and integration of
the contour are separate requirements.
-/

noncomputable section

namespace BTZEntropy

theorem saddleRadius_sq {x : ℝ} (hx : 0 ≤ x) : saddleRadius x ^ 2 = 12 * x := by
  exact Real.sq_sqrt (by positivity)

/-- The chosen point solves the exact saddle equation. -/
theorem saddleBeta_equation {x : ℝ} (hx : 0 < x) :
    x * saddleBeta x ^ 2 = phaseConstant := by
  have hr := saddleRadius_sq (le_of_lt hx)
  have hr0 : saddleRadius x ≠ 0 := ne_of_gt (saddleRadius_pos hx)
  dsimp [saddleBeta, phaseConstant]
  field_simp
  nlinarith [sq_nonneg Real.pi]

theorem saddlePhase_at_saddle {x : ℝ} (hx : 0 < x) :
    saddlePhase x (saddleBeta x) = Real.pi * saddleRadius x / 3 := by
  have hr := saddleRadius_sq (le_of_lt hx)
  have hr0 : saddleRadius x ≠ 0 := ne_of_gt (saddleRadius_pos hx)
  have hp0 : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  dsimp [saddlePhase, saddleBeta, phaseConstant]
  field_simp
  nlinarith

theorem saddleHessian_eq {x : ℝ} (hx : 0 < x) :
    saddleHessian x = saddleRadius x ^ 3 / (12 * Real.pi) := by
  have hr0 : saddleRadius x ≠ 0 := ne_of_gt (saddleRadius_pos hx)
  have hp0 : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  dsimp [saddleHessian, saddleBeta, phaseConstant]
  field_simp
  ring

theorem saddleHessian_pos {x : ℝ} (hx : 0 < x) : 0 < saddleHessian x := by
  dsimp [saddleHessian]
  exact div_pos (mul_pos (by norm_num) phaseConstant_pos) (pow_pos (saddleBeta_pos hx) _)

theorem saddleBeta_antitone {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    saddleBeta y ≤ saddleBeta x := by
  apply div_le_div_of_nonneg_left (by positivity) (saddleRadius_pos hx)
  exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hxy (by norm_num))

/-- A compact positive energy-ratio interval gives a compact positive saddle interval. -/
theorem saddleBeta_mem_Icc {L U x : ℝ} (hL : 0 < L) (hx : x ∈ Set.Icc L U) :
    saddleBeta x ∈ Set.Icc (saddleBeta U) (saddleBeta L) := by
  exact ⟨saddleBeta_antitone (lt_of_lt_of_le hL hx.1) hx.2,
    saddleBeta_antitone hL hx.1⟩

/-- The holomorphic BTZ phase, with the same real constant as `saddlePhase`. -/
def complexSaddlePhase (x : ℝ) (z : ℂ) : ℂ :=
  (x : ℂ) * z + (phaseConstant : ℂ) / z

/-- Parameterization of the vertical contour through the real saddle. -/
def saddleContour (β t : ℝ) : ℂ := (β : ℂ) + (t : ℂ) * Complex.I

@[simp] theorem saddleContour_re (β t : ℝ) : (saddleContour β t).re = β := by
  simp [saddleContour]

@[simp] theorem saddleContour_im (β t : ℝ) : (saddleContour β t).im = t := by
  simp [saddleContour]

theorem saddleContour_ne_zero {β : ℝ} (hβ : β ≠ 0) (t : ℝ) :
    saddleContour β t ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  apply hβ
  simpa using this

@[simp] theorem saddleContour_normSq (β t : ℝ) :
    Complex.normSq (saddleContour β t) = β ^ 2 + t ^ 2 := by
  simp [Complex.normSq_apply, pow_two]

theorem complexSaddlePhase_re (x β t : ℝ) :
    (complexSaddlePhase x (saddleContour β t)).re =
      x * β + phaseConstant * β / (β ^ 2 + t ^ 2) := by
  simp [complexSaddlePhase, Complex.div_re, saddleContour_normSq]

/-- The loss relative to the real point of the contour is exact, at every height. -/
theorem complexSaddlePhase_re_eq_loss (x t : ℝ) {β : ℝ} (hβ : 0 < β) :
    (complexSaddlePhase x (saddleContour β t)).re =
      saddlePhase x β - phaseConstant * t ^ 2 / (β * (β ^ 2 + t ^ 2)) := by
  rw [complexSaddlePhase_re]
  have hden : β ^ 2 + t ^ 2 ≠ 0 := ne_of_gt (by positivity)
  dsimp [saddlePhase]
  field_simp
  <;> ring

theorem complexSaddlePhase_re_le (x t : ℝ) {β : ℝ} (hβ : 0 < β) :
    (complexSaddlePhase x (saddleContour β t)).re ≤ saddlePhase x β := by
  rw [complexSaddlePhase_re_eq_loss x t hβ]
  have h := phaseConstant_pos
  have : 0 ≤ phaseConstant * t ^ 2 / (β * (β ^ 2 + t ^ 2)) := by positivity
  linarith

/-- On the window `|t| ≤ β` the exact loss dominates a Gaussian quadratic. -/
theorem complexSaddlePhase_re_le_quadratic (x : ℝ) {β t : ℝ}
    (hβ : 0 < β) (ht : |t| ≤ β) :
    (complexSaddlePhase x (saddleContour β t)).re ≤
      saddlePhase x β - phaseConstant / (2 * β ^ 3) * t ^ 2 := by
  rw [complexSaddlePhase_re_eq_loss x t hβ]
  have hsq : t ^ 2 ≤ β ^ 2 := by
    simpa using (sq_le_sq₀ (abs_nonneg t) (le_of_lt hβ)).2 ht
  have hden : 0 < β * (β ^ 2 + t ^ 2) := by positivity
  have hcube : 0 < 2 * β ^ 3 := by positivity
  have hb := phaseConstant_pos
  have hloss : phaseConstant / (2 * β ^ 3) * t ^ 2 ≤
      phaseConstant * t ^ 2 / (β * (β ^ 2 + t ^ 2)) := by
    rw [div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_left (by positivity) hden
    nlinarith [mul_le_mul_of_nonneg_left hsq (le_of_lt hβ)]
  linarith

/-- The nonlocal contour has a fixed strictly positive loss once `|t| ≥ ε`. -/
theorem complexSaddlePhase_re_le_outside (x : ℝ) {β t ε : ℝ}
    (hβ : 0 < β) (hε : 0 ≤ ε) (ht : ε ≤ |t|) :
    (complexSaddlePhase x (saddleContour β t)).re ≤
      saddlePhase x β - phaseConstant * ε ^ 2 / (β * (β ^ 2 + ε ^ 2)) := by
  rw [complexSaddlePhase_re_eq_loss x t hβ]
  have hsq : ε ^ 2 ≤ t ^ 2 := by
    have := (sq_le_sq₀ hε (abs_nonneg t)).2 ht
    simpa using this
  have hβt : 0 < β * (β ^ 2 + t ^ 2) := by positivity
  have hβε : 0 < β * (β ^ 2 + ε ^ 2) := by positivity
  have hb := phaseConstant_pos
  have hloss : phaseConstant * ε ^ 2 / (β * (β ^ 2 + ε ^ 2)) ≤
      phaseConstant * t ^ 2 / (β * (β ^ 2 + t ^ 2)) := by
    apply (div_le_div_iff₀ hβε hβt).2
    nlinarith [mul_le_mul_of_nonneg_left hsq (show 0 ≤ phaseConstant * β ^ 3 by positivity)]
  linarith

/-- The local Gaussian constant can be chosen uniformly on a positive energy interval. -/
theorem complexSaddlePhase_re_le_uniform_quadratic {L U x t : ℝ}
    (hL : 0 < L) (hx : x ∈ Set.Icc L U) (ht : |t| ≤ saddleBeta U) :
    (complexSaddlePhase x (saddleContour (saddleBeta x) t)).re ≤
      Real.pi * saddleRadius x / 3 - phaseConstant / (2 * saddleBeta L ^ 3) * t ^ 2 := by
  have hxp : 0 < x := lt_of_lt_of_le hL hx.1
  have hβ := saddleBeta_pos hxp
  have hb := phaseConstant_pos
  have hβb := saddleBeta_mem_Icc hL hx
  have hlocal := complexSaddlePhase_re_le_quadratic x hβ (ht.trans hβb.1)
  rw [saddlePhase_at_saddle hxp] at hlocal
  have hc : phaseConstant / (2 * saddleBeta L ^ 3) ≤
      phaseConstant / (2 * saddleBeta x ^ 3) := by
    apply div_le_div_of_nonneg_left (le_of_lt hb) (by positivity)
    gcongr
    exact hβb.2
  have := mul_le_mul_of_nonneg_right hc (sq_nonneg t)
  linarith

/-- A fixed excluded height has a uniform positive phase loss on the same interval. -/
theorem complexSaddlePhase_re_le_uniform_outside {L U x t ε : ℝ}
    (hL : 0 < L) (hx : x ∈ Set.Icc L U) (hε : 0 ≤ ε) (ht : ε ≤ |t|) :
    (complexSaddlePhase x (saddleContour (saddleBeta x) t)).re ≤
      Real.pi * saddleRadius x / 3 -
        phaseConstant * ε ^ 2 / (saddleBeta L * (saddleBeta L ^ 2 + ε ^ 2)) := by
  have hxp : 0 < x := lt_of_lt_of_le hL hx.1
  have hβ := saddleBeta_pos hxp
  have hb := phaseConstant_pos
  have hβb := saddleBeta_mem_Icc hL hx
  have hlocal := complexSaddlePhase_re_le_outside x hβ hε ht
  rw [saddlePhase_at_saddle hxp] at hlocal
  have hc : phaseConstant * ε ^ 2 /
      (saddleBeta L * (saddleBeta L ^ 2 + ε ^ 2)) ≤
      phaseConstant * ε ^ 2 / (saddleBeta x * (saddleBeta x ^ 2 + ε ^ 2)) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    gcongr <;> first | exact hβb.2 | exact le_of_lt (saddleBeta_pos hL)
  linarith

/-- Exact normalized exponential modulus on the vertical contour. -/
theorem norm_exp_complexSaddlePhase (x c t : ℝ) {β : ℝ} (hβ : 0 < β) :
    ‖Complex.exp ((c : ℂ) *
      (complexSaddlePhase x (saddleContour β t) - (saddlePhase x β : ℂ)))‖ =
      Real.exp (-c * (phaseConstant * t ^ 2 / (β * (β ^ 2 + t ^ 2)))) := by
  rw [Complex.norm_exp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.sub_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  rw [complexSaddlePhase_re_eq_loss x t hβ]
  congr 1
  ring

/-- The local contour integrand has the expected Gaussian envelope. -/
theorem norm_exp_complexSaddlePhase_le_gaussian (x : ℝ) {β c t : ℝ}
    (hβ : 0 < β) (hc : 0 ≤ c) (ht : |t| ≤ β) :
    ‖Complex.exp ((c : ℂ) *
      (complexSaddlePhase x (saddleContour β t) - (saddlePhase x β : ℂ)))‖ ≤
      Real.exp (-c * (phaseConstant / (2 * β ^ 3) * t ^ 2)) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.sub_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  have h := complexSaddlePhase_re_le_quadratic x hβ ht
  nlinarith [mul_le_mul_of_nonneg_left h hc]

end BTZEntropy
