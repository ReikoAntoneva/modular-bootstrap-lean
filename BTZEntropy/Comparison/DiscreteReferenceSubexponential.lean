import BTZEntropy.Comparison.DensityErrorRate
import BTZEntropy.Comparison.InitialPacketFamily

/-!
# Negligible finite packets at the saddle count scale

The complete initial packet and vacuum are controlled at a fixed square
root exponential rate. Every inverse power remains available after division
by the BTZ count scale, including its square root prefactor.
-/

noncomputable section

open Set Filter Real
open GapFamily BTZEntropy.Construction

namespace BTZEntropy.Comparison

theorem sqrt_mul_pow_le_one_add_pow {c : ℝ} (hc : 1 ≤ c) (P : ℕ) :
    sqrt c * c ^ P ≤ (1 + c) ^ (P + 1) := by
  have hc0 : 0 ≤ c := by linarith
  have hs : sqrt c ≤ 1 + c := by
    apply (sqrt_le_iff).mpr
    constructor
    · positivity
    · nlinarith [sq_nonneg c]
  calc
    _ ≤ (1 + c) * (1 + c) ^ P :=
      mul_le_mul hs (pow_le_pow_left₀ hc0 (by linarith) P) (pow_nonneg hc0 P)
        (by positivity)
    _ = _ := by rw [pow_succ]; ring

/-- A fixed square-root exponential is negligible at every polynomial
order relative to the full leading saddle count scale. -/
theorem subexponential_eventually_gapFamily_le {L A D : ℝ}
    (hL : 0 < L) (hA : 0 ≤ A) (P : ℕ) :
    ∀ᶠ a : ℝ in atTop, ∀ x : ℝ, L ≤ x →
      A * exp (D * sqrt (gapFamilyCharge a)) ≤
        exp (2 * π * gapFamilyCharge a * sqrt (x / 3)) /
          (sqrt (gapFamilyCharge a) * gapFamilyCharge a ^ P) := by
  filter_upwards [densityError_eventually_gapFamilyCharge_le
    (D := D) hL (by norm_num : (0 : ℝ) ≤ 0) hA 0 (P + 1),
    eventually_ge_atTop (1 : ℝ)] with a ha ha1 x hx
  have hc : 1 ≤ gapFamilyCharge a := (gapFamilyCharge_gt_one (lt_of_lt_of_le zero_lt_one ha1)).le
  have hc0 : 0 < gapFamilyCharge a := lt_of_lt_of_le (by norm_num) hc
  have hbase := ha x hx
  simp only [pow_zero, mul_one, add_zero] at hbase
  have hexp : exp (2 * π * gapFamilyCharge a * sqrt (x / 3) -
      sqrt L / 3 * gapFamilyCharge a) ≤
      exp (2 * π * gapFamilyCharge a * sqrt (x / 3)) := by
    apply exp_le_exp.mpr
    have : 0 ≤ sqrt L / 3 * gapFamilyCharge a := by positivity
    linarith
  calc
    _ ≤ A * exp (7 * sqrt (a * (x * gapFamilyCharge a)) +
        D * sqrt (gapFamilyCharge a)) := by
      apply mul_le_mul_of_nonneg_left _ hA
      apply exp_le_exp.mpr
      have := sqrt_nonneg (a * (x * gapFamilyCharge a))
      linarith
    _ ≤ exp (2 * π * gapFamilyCharge a * sqrt (x / 3) -
        sqrt L / 3 * gapFamilyCharge a) / (1 + gapFamilyCharge a) ^ (P + 1) := hbase
    _ ≤ exp (2 * π * gapFamilyCharge a * sqrt (x / 3)) /
        (1 + gapFamilyCharge a) ^ (P + 1) :=
      div_le_div_of_nonneg_right hexp (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_left (exp_nonneg _) (by positivity)
      (sqrt_mul_pow_le_one_add_pow hc P)

/-- The actual initial unit nodes, marker, and vacuum satisfy the estimate
uniformly over the admitted construction class and the whole gap interval. -/
theorem initial_vacuum_eventually_saddle_scale (B : ℝ) (φ : SmoothKernel)
    {L U : ℝ} (hL : 0 < L) (P : ℕ) :
    ∀ᶠ a : ℝ in atTop, ∀ (σ : ActualFixedFamilySelector B),
      σ ∈ fixedFamilySelectors B → ∀ (ha : fixedFamilyThreshold B ≤ a)
      (δ : ℝ) (hδ : δ ∈ Ico (0 : ℝ) B) (x : ℝ), x ∈ Icc L U →
        fixedFamilyMarkedInitialSmoothCount φ (σ a ha δ hδ) (x * gapFamilyCharge a) +
          vacuumSmoothCount φ (gapFamilyCharge a) (x * gapFamilyCharge a) ≤
            exp (2 * π * gapFamilyCharge a * sqrt (x / 3)) /
              (sqrt (gapFamilyCharge a) * gapFamilyCharge a ^ P) := by
  obtain ⟨A, D, hA, _, hpacket⟩ := fixedFamily_initial_vacuum_uniform_sqrt_bound B φ U
  filter_upwards [subexponential_eventually_gapFamily_le (D := D) hL hA P]
    with a hscale σ hσ ha δ hδ x hx
  exact (hpacket σ hσ a ha δ hδ x hx.2).trans (hscale x hx.1)

end BTZEntropy.Comparison
