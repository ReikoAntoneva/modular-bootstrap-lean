import BTZEntropy.Comparison.DensityErrorState
import BTZEntropy.Comparison.DensityErrorRate

/-!
# Uniform inverse-power decay of actual density errors

The local almost-everywhere repair envelope is integrated against all integer
spins and descendant packets before applying the explicit exponential
advantage. Thresholds are independent of the error function, fronts, packet,
marker and selector.
-/

noncomputable section

open Set Filter MeasureTheory Real
open GapFamily.Analytic

namespace BTZEntropy.Comparison

/-- Every density with the proved local envelope has arbitrarily small
inverse-power relative error. The numerator functions remain quantified
inside the common charge threshold. -/
theorem densityErrorFullPacket_eventually_inverse_pow (φ : SmoothKernel)
    {L U R H : ℝ} (hL : 0 < L) (hLU : L ≤ U) (hR0 : 0 ≤ R) (hH : 0 ≤ H)
    (hR : ∀ u, φ u ≠ 0 → u ≤ R) (hφ : ∀ u, φ u ≤ H) (P : ℕ) :
    ∀ᶠ c : ℝ in atTop, ∀ x ∈ Icc L U, ∀ F : Finset (ℕ × ℕ),
      ∀ (ε : ℤ → ℝ → ℝ) (lower : ℤ → ℝ),
      (∀ j, 1 ≤ lower j) → (∀ j : ℤ, |(j : ℝ)| ≤ lower j) →
      (∀ j, ∀ᵐ e ∂referenceMeasure j, lower j ≤ e →
        |ε j e| ≤ exp (7 * sqrt (((c - 1) / 12) * e))) →
      |densityErrorFullPacket φ (x * c) F ε lower| /
        exp (2 * π * c * sqrt (x / 3)) ≤ 1 / c ^ P := by
  have hU : 0 ≤ U := hL.le.trans hLU
  have hC : 0 ≤ (2 * (U + R + 3) + 1) * (U + R + 3) * H := by positivity
  have hr := densityError_eventually_inverse_pow
    (C := (2 * (U + R + 3) + 1) * (U + R + 3) * H)
    (D := U + R + 1 / 12 + 4) hL (show 0 ≤ R + 1 / 12 by positivity) hC 2 P
  filter_upwards [hr, eventually_ge_atTop (1 : ℝ)] with c hc hc1
  intro x hx F ε lower hlow hj hε
  apply (div_le_div_of_nonneg_right
    (densityErrorFullPacket_abs_le_polynomial φ F ε lower
      (by linarith : 0 ≤ (c - 1) / 12) hc1 (hL.le.trans hx.1) hx.2
      hR0 hH hlow hj hR hφ hε) (exp_pos _).le).trans
  simpa only [add_assoc] using hc x hx.1

/-- The standard Gaussian `c^(-1/2)` prefactor is absorbed by one extra
inverse-power order, without weakening the uniformity in the density. -/
theorem densityErrorFullPacket_eventually_sqrt_scale (φ : SmoothKernel)
    {L U R H : ℝ} (hL : 0 < L) (hLU : L ≤ U) (hR0 : 0 ≤ R) (hH : 0 ≤ H)
    (hR : ∀ u, φ u ≠ 0 → u ≤ R) (hφ : ∀ u, φ u ≤ H) (P : ℕ) :
    ∀ᶠ c : ℝ in atTop, ∀ x ∈ Icc L U, ∀ F : Finset (ℕ × ℕ),
      ∀ (ε : ℤ → ℝ → ℝ) (lower : ℤ → ℝ),
      (∀ j, 1 ≤ lower j) → (∀ j : ℤ, |(j : ℝ)| ≤ lower j) →
      (∀ j, ∀ᵐ e ∂referenceMeasure j, lower j ≤ e →
        |ε j e| ≤ exp (7 * sqrt (((c - 1) / 12) * e))) →
      |densityErrorFullPacket φ (x * c) F ε lower| /
        (exp (2 * π * c * sqrt (x / 3)) / sqrt c) ≤ 1 / c ^ P := by
  filter_upwards [densityErrorFullPacket_eventually_inverse_pow φ hL hLU hR0 hH
    hR hφ (P + 1), eventually_ge_atTop (1 : ℝ)] with c hc hc1
  intro x hx F ε lower hlow hj hε
  have hc0 : 0 < c := by linarith
  have hs : 0 < sqrt c := sqrt_pos.mpr hc0
  have hsq : sqrt c ≤ c := by
    have hs1 : 1 ≤ sqrt c := by simpa using sqrt_le_sqrt hc1
    nlinarith [sq_sqrt hc0.le]
  calc
    _ = (|densityErrorFullPacket φ (x * c) F ε lower| /
        exp (2 * π * c * sqrt (x / 3))) * sqrt c := by field_simp
    _ ≤ (1 / c ^ (P + 1)) * sqrt c :=
      mul_le_mul_of_nonneg_right (hc x hx F ε lower hlow hj hε) hs.le
    _ ≤ (1 / c ^ (P + 1)) * c := mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = 1 / c ^ P := by rw [pow_succ]; field_simp

/-- Direct application to the actual numerator stored at each finite stage
of every fixed-cutoff datum at every sufficiently large real charge. -/
theorem state_densityError_eventually_inverse_pow (φ : SmoothKernel)
    {L U R H : ℝ} (hL : 0 < L) (hLU : L ≤ U) (hR0 : 0 ≤ R) (hH : 0 ≤ H)
    (hR : ∀ u, φ u ≠ 0 → u ≤ R) (hφ : ∀ u, φ u ≤ H) (P : ℕ) :
    ∀ᶠ a : ℝ in atTop, ∀ {B : ℝ} {g : BTZEntropy.Construction.FixedFamilyGeometry B}
      {δ : ℝ} (d : BTZEntropy.Construction.FixedFamilyDatum g a δ) (n : ℕ)
      (F : Finset (ℕ × ℕ)) (x : ℝ), x ∈ Icc L U →
      |densityErrorFullPacket φ (x * GapFamily.gapFamilyCharge a) F
        (finiteStateDensityError (GapFamily.shift (GapFamily.gapFamilyCharge a))
          (d.state n)) (d.state n).front| /
        exp (2 * π * GapFamily.gapFamilyCharge a * sqrt (x / 3)) ≤
          1 / GapFamily.gapFamilyCharge a ^ P := by
  have hr := GapFamily.tendsto_gapFamilyCharge_atTop.eventually
    (densityErrorFullPacket_eventually_inverse_pow φ hL hLU hR0 hH hR hφ P)
  filter_upwards [hr] with a ha
  intro B g δ d n F x hx
  exact ha x hx F _ _ (FixedFamilyDatum.state_front_one d n)
    (FixedFamilyDatum.state_front_spin d n) (FixedFamilyDatum.state_densityError_bound d n)

end BTZEntropy.Comparison
