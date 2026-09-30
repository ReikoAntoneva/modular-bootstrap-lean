import GapFamily.Analytic.Foundation.Propagation
import GapFamily.Analytic.Foundation.ThresholdAnchorBand
import GapFamily.Analytic.Foundation.ThresholdAnchorObservation

/-!
# Nonvanishing of the scalar threshold response on the anchor band

The value minus one at the scalar origin forces a quantitative observation
mass. The estimate is derived from the proved fixed-disk propagation theorem.
-/

noncomputable section

open MeasureTheory Set Metric Real

namespace GapFamily.Analytic

/-- A disk bound for a function with value minus one must be at least one. -/
theorem thresholdResponse_disk_bound_ge_one (F : ℂ → ℂ) (A : ℝ)
    (hF0 : F 0 = -1)
    (hbound : ∀ z : ℂ, ‖z‖ ≤ 16384 → ‖F z‖ ≤ A) : 1 ≤ A := by
  have h := hbound 0 (by norm_num)
  simpa only [hF0, norm_neg, norm_one] using h

/-- Actual propagation gives a quantitative positive ordinary observation
integral whenever the entire response takes value minus one at zero. -/
theorem thresholdResponse_observation_mass_lower (F : ℂ → ℂ) (A : ℝ)
    (hA : 0 ≤ A) (hf : Differentiable ℂ F) (hF0 : F 0 = -1)
    (hbound : ∀ z : ℂ, ‖z‖ ≤ 16384 → ‖F z‖ ≤ A) :
    1 / (10000 * A) ^ 2 ≤
      ∫ t in sqrt 2..sqrt 3, ‖F (t : ℂ)‖ ^ 2 := by
  let T : ℝ := ∫ t in sqrt 2..sqrt 3, ‖F (t : ℂ)‖ ^ 2
  have hT : 0 ≤ T :=
    intervalIntegral.integral_nonneg (sqrt_le_sqrt (by norm_num))
      (fun _ _ => sq_nonneg _)
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one
    (thresholdResponse_disk_bound_ge_one F A hF0 hbound)
  have hprop := norm_le_sqrt_l2_of_fixed_disk hA hf.diffContOnCl
    (fun z hz => hbound z (by simpa only [mem_closedBall, dist_zero_right] using hz))
    (show (0 : ℝ) ∈ Icc 0 1 by simp)
  have hp : 1 ≤ 100 * sqrt (A * sqrt T) := by
    simpa only [Complex.ofReal_zero, hF0, norm_neg, norm_one] using hprop
  have hfirst : 1 ≤ 10000 * A * sqrt T := by
    have hh := (sq_le_sq₀ (show (0 : ℝ) ≤ 1 by norm_num)
      (show 0 ≤ 100 * sqrt (A * sqrt T) by positivity)).mpr hp
    nlinarith [sq_sqrt (mul_nonneg hA (sqrt_nonneg T))]
  have hsecond : 1 ≤ (10000 * A) ^ 2 * T := by
    have hh := (sq_le_sq₀ (show (0 : ℝ) ≤ 1 by norm_num)
      (show 0 ≤ 10000 * A * sqrt T by positivity)).mpr hfirst
    calc
      1 ≤ (10000 * A * sqrt T) ^ 2 := by simpa using hh
      _ = (10000 * A) ^ 2 * T := by rw [mul_pow, sq_sqrt hT]
  apply (div_le_iff₀ (sq_pos_of_pos (show 0 < 10000 * A by positivity))).mpr
  simpa only [mul_comm] using hsecond

/-- Physical agreement on the observation interval identifies the actual
complex observation integral with the real response-square integral. -/
theorem thresholdResponse_observation_eq (F : ℂ → ℂ) (B : ℝ) (ζ : ℝ → ℝ)
    (hagree : ∀ t ∈ Icc (sqrt 2) (sqrt 3), F (t : ℂ) = (ζ (B * t ^ 2) : ℂ)) :
    (∫ t in sqrt 2..sqrt 3, ‖F (t : ℂ)‖ ^ 2) =
      ∫ t in sqrt 2..sqrt 3, ζ (B * t ^ 2) ^ 2 := by
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (sqrt 2) (sqrt 3) := by
    simpa only [uIcc_of_le (sqrt_le_sqrt (by norm_num : (2 : ℝ) ≤ 3))] using ht
  dsimp only
  rw [hagree t ht', Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- The actual high-band normalization has the quantitative lower bound
forced by holomorphy, its value at zero, and the physical agreement. -/
theorem scalarAnchorSquareMass_lower_of_entire (F : ℂ → ℂ) (A B : ℝ)
    (ζ : ℝ → ℝ) (hA : 0 ≤ A) (hB : 0 < B)
    (hf : Differentiable ℂ F) (hF0 : F 0 = -1)
    (hbound : ∀ z : ℂ, ‖z‖ ≤ 16384 → ‖F z‖ ≤ A)
    (hζ : ContinuousOn ζ (scalarAnchorBand B))
    (hagree : ∀ t ∈ Icc (sqrt 2) (sqrt 3), F (t : ℂ) = (ζ (B * t ^ 2) : ℂ)) :
    1 / (10000 * A) ^ 2 ≤ scalarAnchorSquareMass B ζ := by
  have hlower := thresholdResponse_observation_mass_lower F A hA hf hF0 hbound
  rw [thresholdResponse_observation_eq F B ζ hagree] at hlower
  exact hlower.trans (integral_scalarAnchor_observation_le B hB ζ hζ)

/-- No positive-square-mass premise remains once the entire scalar response
and its physical restriction have been established. -/
theorem scalarAnchorSquareMass_pos_of_entire (F : ℂ → ℂ) (A B : ℝ)
    (ζ : ℝ → ℝ) (hA : 0 ≤ A) (hB : 0 < B)
    (hf : Differentiable ℂ F) (hF0 : F 0 = -1)
    (hbound : ∀ z : ℂ, ‖z‖ ≤ 16384 → ‖F z‖ ≤ A)
    (hζ : ContinuousOn ζ (scalarAnchorBand B))
    (hagree : ∀ t ∈ Icc (sqrt 2) (sqrt 3), F (t : ℂ) = (ζ (B * t ^ 2) : ℂ)) :
    0 < scalarAnchorSquareMass B ζ := by
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one
    (thresholdResponse_disk_bound_ge_one F A hF0 hbound)
  exact lt_of_lt_of_le (by positivity : 0 < 1 / (10000 * A) ^ 2)
    (scalarAnchorSquareMass_lower_of_entire F A B ζ hA hB hf hF0 hbound hζ hagree)

end GapFamily.Analytic
