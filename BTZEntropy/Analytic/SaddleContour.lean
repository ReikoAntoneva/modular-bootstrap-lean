import BTZEntropy.Analytic.SaddlePhase
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The nonlocal BTZ contour

An integrable amplitude and the exact rational phase yield an exponentially
small integral off every fixed saddle window. The constants below are uniform
over a positive compact energy interval. The amplitude's integrability remains
a separate analytic input; no asymptotic expansion is assumed here.
-/

noncomputable section

open MeasureTheory

namespace BTZEntropy

/-- The phase after extracting the real saddle exponential. -/
def normalizedSaddleExponential (x c t : ℝ) : ℂ :=
  Complex.exp ((c : ℂ) * (complexSaddlePhase x (saddleContour (saddleBeta x) t) -
    (saddlePhase x (saddleBeta x) : ℂ)))

/-- A positive lower bound for the phase loss away from height `ε`. -/
def contourLoss (L ε : ℝ) : ℝ :=
  phaseConstant * ε ^ 2 / (saddleBeta L * (saddleBeta L ^ 2 + ε ^ 2))

theorem contourLoss_pos {L ε : ℝ} (hL : 0 < L) (hε : 0 < ε) :
    0 < contourLoss L ε := by
  have hβ := saddleBeta_pos hL
  have hb := phaseConstant_pos
  unfold contourLoss
  positivity

theorem continuous_normalizedSaddleExponential {x : ℝ} (hx : 0 < x) (c : ℝ) :
    Continuous (normalizedSaddleExponential x c) := by
  have hcont : Continuous (saddleContour (saddleBeta x)) := by
    unfold saddleContour
    fun_prop
  have hphase : Continuous (fun t => complexSaddlePhase x (saddleContour (saddleBeta x) t)) := by
    unfold complexSaddlePhase
    exact (continuous_const.mul hcont).add
      (continuous_const.div hcont (fun t => saddleContour_ne_zero (ne_of_gt (saddleBeta_pos hx)) t))
  exact Complex.continuous_exp.comp (continuous_const.mul (hphase.sub continuous_const))

theorem norm_normalizedSaddleExponential_le_one {x c : ℝ}
    (hx : 0 < x) (hc : 0 ≤ c) (t : ℝ) :
    ‖normalizedSaddleExponential x c t‖ ≤ 1 := by
  rw [normalizedSaddleExponential, norm_exp_complexSaddlePhase x c t (saddleBeta_pos hx)]
  apply Real.exp_le_one_iff.mpr
  have hb := phaseConstant_pos
  have hβ := saddleBeta_pos hx
  have : 0 ≤ phaseConstant * t ^ 2 /
      (saddleBeta x * (saddleBeta x ^ 2 + t ^ 2)) := by positivity
  nlinarith

theorem norm_normalizedSaddleExponential_le_outside {L U x c ε t : ℝ}
    (hL : 0 < L) (hx : x ∈ Set.Icc L U) (hc : 0 ≤ c) (hε : 0 ≤ ε) (ht : ε ≤ |t|) :
    ‖normalizedSaddleExponential x c t‖ ≤ Real.exp (-c * contourLoss L ε) := by
  rw [normalizedSaddleExponential, Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.sub_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  rw [saddlePhase_at_saddle (lt_of_lt_of_le hL hx.1)]
  have h := complexSaddlePhase_re_le_uniform_outside hL hx hε ht
  change _ ≤ Real.pi * saddleRadius x / 3 - contourLoss L ε at h
  nlinarith [mul_le_mul_of_nonneg_left h hc]

/-- Multiplication by the actual normalized phase preserves absolute integrability. -/
theorem integrable_mul_normalizedSaddleExponential {x c : ℝ} {A : ℝ → ℂ}
    (hx : 0 < x) (hc : 0 ≤ c) (hA : Integrable A) :
    Integrable (fun t => A t * normalizedSaddleExponential x c t) := by
  exact hA.mul_bdd (continuous_normalizedSaddleExponential hx c).aestronglyMeasurable
    (Filter.Eventually.of_forall (norm_normalizedSaddleExponential_le_one hx hc))

/-- The integrated off-window remainder is bounded by an explicit exponential,
uniformly in the saddle location. -/
theorem norm_integral_mul_normalizedSaddleExponential_outside {L U x c ε : ℝ}
    {A : ℝ → ℂ} (hL : 0 < L) (hx : x ∈ Set.Icc L U)
    (hc : 0 ≤ c) (hε : 0 ≤ ε) (hA : Integrable A) :
    ‖∫ t in {t : ℝ | ε ≤ |t|}, A t * normalizedSaddleExponential x c t‖ ≤
      Real.exp (-c * contourLoss L ε) * ∫ t : ℝ, ‖A t‖ := by
  have hbound : ∀ᵐ t ∂volume.restrict {t : ℝ | ε ≤ |t|},
      ‖A t * normalizedSaddleExponential x c t‖ ≤
        Real.exp (-c * contourLoss L ε) * ‖A t‖ := by
    filter_upwards [ae_restrict_mem (measurableSet_le measurable_const (continuous_abs.measurable))]
      with t ht
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right
      (norm_normalizedSaddleExponential_le_outside hL hx hc hε ht) (norm_nonneg _)
  calc
    ‖∫ t in {t : ℝ | ε ≤ |t|}, A t * normalizedSaddleExponential x c t‖ ≤
        ∫ t in {t : ℝ | ε ≤ |t|}, Real.exp (-c * contourLoss L ε) * ‖A t‖ :=
      norm_integral_le_of_norm_le (hA.norm.integrableOn.const_mul _) hbound
    _ = Real.exp (-c * contourLoss L ε) * ∫ t in {t : ℝ | ε ≤ |t|}, ‖A t‖ :=
      integral_const_mul _ _
    _ ≤ Real.exp (-c * contourLoss L ε) * ∫ t : ℝ, ‖A t‖ := by
      apply mul_le_mul_of_nonneg_left _ (le_of_lt (Real.exp_pos _))
      exact setIntegral_le_integral hA.norm (Filter.Eventually.of_forall (fun t => norm_nonneg (A t)))

/-- An explicit form of exponential suppression stronger than every inverse power. -/
theorem exp_neg_mul_le_factorial {c η : ℝ} (hc : 0 < c) (hη : 0 < η) (N : ℕ) :
    Real.exp (-c * η) ≤ (N.factorial : ℝ) / (η ^ N * c ^ N) := by
  have ha : 0 < c * η := mul_pos hc hη
  have hf : 0 < (N.factorial : ℝ) := by positivity
  have h := (div_le_iff₀ hf).mp (Real.pow_div_factorial_le_exp (c * η) (le_of_lt ha) N)
  have he : Real.exp (-(c * η)) * (c * η) ^ N ≤ (N.factorial : ℝ) := by
    calc
      Real.exp (-(c * η)) * (c * η) ^ N ≤
          Real.exp (-(c * η)) * ((N.factorial : ℝ) * Real.exp (c * η)) :=
        mul_le_mul_of_nonneg_left (by simpa [mul_comm] using h) (le_of_lt (Real.exp_pos _))
      _ = (N.factorial : ℝ) := by rw [Real.exp_neg]; field_simp
  apply (le_div_iff₀ (mul_pos (pow_pos hη N) (pow_pos hc N))).mpr
  simpa [mul_pow, mul_comm, neg_mul] using he

/-- Every finite inverse-power target follows from the same nonlocal contour bound. -/
theorem norm_integral_mul_normalizedSaddleExponential_outside_pow {L U x c ε : ℝ}
    {A : ℝ → ℂ} (hL : 0 < L) (hx : x ∈ Set.Icc L U)
    (hc : 0 < c) (hε : 0 < ε) (hA : Integrable A) (N : ℕ) :
    ‖∫ t in {t : ℝ | ε ≤ |t|}, A t * normalizedSaddleExponential x c t‖ ≤
      ((N.factorial : ℝ) / contourLoss L ε ^ N) * (∫ t : ℝ, ‖A t‖) / c ^ N := by
  calc
    _ ≤ Real.exp (-c * contourLoss L ε) * ∫ t : ℝ, ‖A t‖ :=
      norm_integral_mul_normalizedSaddleExponential_outside hL hx (le_of_lt hc) (le_of_lt hε) hA
    _ ≤ ((N.factorial : ℝ) / (contourLoss L ε ^ N * c ^ N)) * ∫ t : ℝ, ‖A t‖ :=
      mul_le_mul_of_nonneg_right (exp_neg_mul_le_factorial hc (contourLoss_pos hL hε) N)
        (integral_nonneg (fun _ => norm_nonneg _))
    _ = _ := by ring

end BTZEntropy
