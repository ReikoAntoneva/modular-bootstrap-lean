import BTZEntropy.Coefficient
import GapFamily.GapFamilyLimit

/-!
# Charge normalization of the discrete reference comparison

The fixed enlargement of the test window costs a constant exponential
factor on every positive ratio interval. Four additional inverse powers
absorb the quadratic band mass and the square-root BTZ normalization.
-/

noncomputable section

open Real Filter Set

namespace BTZEntropy.Comparison

/-- The saddle definition is the usual BTZ action at energy `x * c`. -/
theorem leadingAction_eq_btz (x c : ℝ) :
    leadingAction x c = 2 * π * c * sqrt (x / 3) := by
  have hs : sqrt (12 * x) = 6 * sqrt (x / 3) := by
    rw [show 12 * x = 36 * (x / 3) by ring, sqrt_mul (by norm_num)]
    rw [show (36 : ℝ) = 6 ^ 2 by norm_num, sqrt_sq (by norm_num : (0 : ℝ) ≤ 6)]
  simp only [leadingAction, saddleRadius, hs]
  ring

/-- The reference square root differs from its leading BTZ value by at
most a constant when the observation window has fixed width. -/
theorem discreteReference_sqrt_le {a c x L D : ℝ}
    (ha : 0 ≤ a) (hc : c = 12 * a + 1) (hL : 0 < L)
    (hx : L ≤ x) (hD : 0 ≤ D) :
    sqrt (a * (x * c + D)) ≤
      c * sqrt (12 * x) / 12 + D / sqrt (12 * L) := by
  have hc1 : 1 ≤ c := by linarith
  have hc0 : 0 ≤ c := by linarith
  have hx0 : 0 ≤ x := hL.le.trans hx
  have hsL : 0 < sqrt (12 * L) := by positivity
  have hroot : sqrt (12 * L) ≤ sqrt (12 * x) :=
    sqrt_le_sqrt (by linarith)
  have hcross : c * D ≤ c * sqrt (12 * x) * (D / sqrt (12 * L)) := by
    have h := mul_le_mul_of_nonneg_right hroot (div_nonneg hD hsL.le)
    have hcancel : sqrt (12 * L) * (D / sqrt (12 * L)) = D := by
      field_simp
    rw [hcancel] at h
    nlinarith [mul_le_mul_of_nonneg_left h hc0]
  have hbase : (c * sqrt (12 * x) / 12) ^ 2 = c ^ 2 * x / 12 := by
    rw [div_pow, mul_pow, sq_sqrt (by positivity : 0 ≤ 12 * x)]
    ring
  apply (sqrt_le_iff).mpr
  refine ⟨by positivity, ?_⟩
  have hsq := sq_nonneg (D / sqrt (12 * L))
  have hxc : 0 ≤ x * c := mul_nonneg hx0 hc0
  rw [add_sq, hbase]
  nlinarith [mul_nonneg hD hc0]

/-- The fixed-window exponential factor is uniform in the central charge
and in every ratio `x ≥ L`. -/
theorem discreteReference_exp_le {a c x L D : ℝ}
    (ha : 0 ≤ a) (hc : c = 12 * a + 1) (hL : 0 < L)
    (hx : L ≤ x) (hD : 0 ≤ D) :
    exp (4 * π * sqrt (a * (x * c + D))) ≤
      exp (4 * π * D / sqrt (12 * L)) * exp (leadingAction x c) := by
  rw [← exp_add]
  apply exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left
    (discreteReference_sqrt_le ha hc hL hx hD) (show 0 ≤ 4 * π by positivity)
  dsimp [leadingAction, saddleRadius]
  convert h using 1
  ring

/-- The quadratic band factor and the BTZ square-root normalization cost
at most four additional inverse powers of the shifted charge. -/
theorem discreteReference_polynomial_scale_le {a c x U D : ℝ}
    (ha : 0 ≤ a) (hc : c = 12 * a + 1) (hU : 0 ≤ U)
    (hx0 : 0 ≤ x) (hxU : x ≤ U) (hD : 0 ≤ D) (P : ℕ) :
    sqrt c * c ^ P * (1 + x * c + D) ^ 2 ≤
      ((1 + U + D) ^ 2 * 12 ^ (P + 4)) * (1 + a) ^ (P + 4) := by
  have hc1 : 1 ≤ c := by linarith
  have hc0 : 0 ≤ c := by linarith
  have hs : sqrt c ≤ c := sqrt_le_self_iff.mpr (Or.inr hc1)
  have hpoly : 1 + x * c + D ≤ (1 + U + D) * c := by
    have hxc := mul_le_mul_of_nonneg_right hxU hc0
    have hDc := mul_nonneg hD (sub_nonneg.mpr hc1)
    nlinarith
  calc
    _ ≤ c * c ^ P * ((1 + U + D) * c) ^ 2 := by gcongr
    _ = (1 + U + D) ^ 2 * c ^ (P + 3) := by rw [pow_add]; ring
    _ ≤ (1 + U + D) ^ 2 * c ^ (P + 4) := by
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hc1 (show P + 3 ≤ P + 4 by omega)) (sq_nonneg _)
    _ ≤ (1 + U + D) ^ 2 * (12 * (1 + a)) ^ (P + 4) := by
      gcongr
      linarith
    _ = _ := by rw [mul_pow]; ring

/-- Explicit normalization on any positive compact interval. The extra
nonnegative multiplier can include the convergent descendant thermal sum. -/
theorem discreteReference_normalized_le {a c x L U D M : ℝ}
    (ha : 0 ≤ a) (hc : c = 12 * a + 1) (hL : 0 < L)
    (hx : x ∈ Icc L U) (hD : 0 ≤ D) (hM : 0 ≤ M) (P : ℕ) :
    M * (1 + x * c + D) ^ 2 * exp (4 * π * sqrt (a * (x * c + D))) /
        (1 + a) ^ (P + 4) ≤
      (M * (1 + U + D) ^ 2 * 12 ^ (P + 4) *
        exp (4 * π * D / sqrt (12 * L))) * exp (leadingAction x c) /
          (sqrt c * c ^ P) := by
  have hc0 : 0 < c := by linarith
  have hx0 : 0 ≤ x := hL.le.trans hx.1
  have hU : 0 ≤ U := hx0.trans hx.2
  have hp := discreteReference_polynomial_scale_le ha hc hU hx0 hx.2 hD P
  have he := discreteReference_exp_le ha hc hL hx.1 hD
  apply (div_le_div_iff₀ (by positivity : 0 < (1 + a) ^ (P + 4))
    (by positivity : 0 < sqrt c * c ^ P)).mpr
  calc
    _ = M * (sqrt c * c ^ P * (1 + x * c + D) ^ 2) *
        exp (4 * π * sqrt (a * (x * c + D))) := by ring
    _ ≤ M * (((1 + U + D) ^ 2 * 12 ^ (P + 4)) * (1 + a) ^ (P + 4)) *
        (exp (4 * π * D / sqrt (12 * L)) * exp (leadingAction x c)) := by
      gcongr
    _ = _ := by ring

/-- One positive constant works at every nonnegative real shifted charge
and at every ratio in the given compact interval. The enlargement `13/12`
retains both the descendant cylinder shift and the full cell width. -/
theorem discreteReference_gapFamilyCharge_le {L U R M : ℝ}
    (hL : 0 < L) (_hLU : L ≤ U) (hR : 0 ≤ R) (hM : 0 ≤ M) (P : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : ℝ, 0 ≤ a → ∀ x ∈ Icc L U,
      M * (1 + (x * GapFamily.gapFamilyCharge a + R + 13 / 12)) ^ 2 *
          exp (4 * π * sqrt (a *
            (x * GapFamily.gapFamilyCharge a + R + 13 / 12))) /
          (1 + a) ^ (P + 4) ≤
        C * exp (leadingAction x (GapFamily.gapFamilyCharge a)) /
          (sqrt (GapFamily.gapFamilyCharge a) * GapFamily.gapFamilyCharge a ^ P) := by
  let D : ℝ := R + 13 / 12
  let C₀ : ℝ := M * (1 + U + D) ^ 2 * 12 ^ (P + 4) *
    exp (4 * π * D / sqrt (12 * L))
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  refine ⟨C₀ + 1, by positivity, ?_⟩
  intro a ha x hx
  have hc : GapFamily.gapFamilyCharge a = 12 * a + 1 := rfl
  have hc0 : 0 ≤ GapFamily.gapFamilyCharge a := by rw [hc]; positivity
  have h := discreteReference_normalized_le ha hc hL hx hD hM P
  change _ ≤ C₀ * exp (leadingAction x (GapFamily.gapFamilyCharge a)) / _ at h
  calc
    _ ≤ C₀ * exp (leadingAction x (GapFamily.gapFamilyCharge a)) /
        (sqrt (GapFamily.gapFamilyCharge a) * GapFamily.gapFamilyCharge a ^ P) := by
      simpa only [D, add_assoc] using h
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right (by linarith) (exp_nonneg _)

/-- Eventual form for the all-orders comparison: the central-charge
normalization has the required square-root and inverse-power factors. -/
theorem discreteReference_eventually_gapFamilyCharge_le {L U R M : ℝ}
    (hL : 0 < L) (hLU : L ≤ U) (hR : 0 ≤ R) (hM : 0 ≤ M) (P : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ a : ℝ in atTop, ∀ x ∈ Icc L U,
      M * (1 + (x * GapFamily.gapFamilyCharge a + R + 13 / 12)) ^ 2 *
          exp (4 * π * sqrt (a *
            (x * GapFamily.gapFamilyCharge a + R + 13 / 12))) /
          (1 + a) ^ (P + 4) ≤
        C * exp (leadingAction x (GapFamily.gapFamilyCharge a)) /
          (sqrt (GapFamily.gapFamilyCharge a) * GapFamily.gapFamilyCharge a ^ P) := by
  obtain ⟨C, hC, hbound⟩ := discreteReference_gapFamilyCharge_le hL hLU hR hM P
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with a ha
  exact hbound a ha

/-- A real threshold version suitable for the uniform family contract. -/
theorem exists_discreteReference_gapFamilyCharge_threshold {L U R M : ℝ}
    (hL : 0 < L) (hLU : L ≤ U) (hR : 0 ≤ R) (hM : 0 ≤ M) (P : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ a₀ : ℝ, 1 ≤ a₀ ∧ ∀ a, a₀ ≤ a → ∀ x ∈ Icc L U,
      M * (1 + (x * GapFamily.gapFamilyCharge a + R + 13 / 12)) ^ 2 *
          exp (4 * π * sqrt (a *
            (x * GapFamily.gapFamilyCharge a + R + 13 / 12))) /
          (1 + a) ^ (P + 4) ≤
        C * exp (leadingAction x (GapFamily.gapFamilyCharge a)) /
          (sqrt (GapFamily.gapFamilyCharge a) * GapFamily.gapFamilyCharge a ^ P) := by
  obtain ⟨C, hC, hbound⟩ := discreteReference_gapFamilyCharge_le hL hLU hR hM P
  exact ⟨C, hC, 1, le_rfl, fun a ha => hbound a (zero_le_one.trans ha)⟩

end BTZEntropy.Comparison
