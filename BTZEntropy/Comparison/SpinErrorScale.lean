import BTZEntropy.Analytic.Prefactor
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Exponential error at the saddle count scale

An exponentially suppressed absolute count error, measured against the BTZ
exponential, is smaller than every inverse charge power after division by the
actual Gaussian scale. Compact-uniform positivity of its prefactor is proved
in `Prefactor`; the remaining estimate is scalar exponential domination.
-/

noncomputable section

open Filter
open scoped Topology

namespace BTZEntropy

private theorem eventually_sqrt_charge_exp_le {D d : ℝ} (hD : 0 ≤ D) (hd : 0 < d)
    (q : ℕ) :
    ∀ᶠ a : ℝ in atTop,
      D * Real.sqrt (12 * a + 1) * Real.exp (-d * a) ≤ 1 / (12 * a + 1) ^ q := by
  have hlim : Tendsto (fun a : ℝ => D * 13 ^ (q + 1) *
      (a ^ (q + 1) * Real.exp (-d * a))) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast, mul_zero] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (q + 1 : ℕ) d hd).const_mul
        (D * 13 ^ (q + 1))
  filter_upwards [eventually_ge_atTop (2 : ℝ), hlim.eventually_le_const zero_lt_one]
    with a ha hsmall
  have ha0 : 0 < a := by linarith
  have hc : 1 ≤ 12 * a + 1 := by linarith
  have hs : Real.sqrt (12 * a + 1) ≤ 12 * a + 1 := Real.sqrt_le_self_iff.mpr (Or.inr hc)
  have hca : 12 * a + 1 ≤ 13 * a := by linarith
  apply (le_div_iff₀ (pow_pos (zero_lt_one.trans_le hc) q)).mpr
  calc
    _ ≤ D * (13 * a) * Real.exp (-d * a) * (13 * a) ^ q := by
      gcongr
      exact hs.trans hca
    _ = D * 13 ^ (q + 1) * (a ^ (q + 1) * Real.exp (-d * a)) := by
      simp only [mul_pow, pow_succ]
      ring
    _ ≤ 1 := hsmall

/-- Exponential suppression implies every normalized inverse-charge bound,
with one threshold for the entire compact energy-ratio interval. -/
theorem eventually_normalized_exponential_error_le (φ : SmoothKernel)
    {L U C d : ℝ} (hL : 0 < L) (hLU : L ≤ U) (hC : 0 < C) (hd : 0 < d)
    (err : ℝ → ℝ → ℝ)
    (herr : ∀ a : ℝ, 2 ≤ a → ∀ x ∈ Set.Icc L U,
      |err a x| ≤ C * Real.exp (leadingAction x (12 * a + 1)) * Real.exp (-d * a))
    (q : ℕ) :
    ∀ᶠ a : ℝ in atTop, ∀ x ∈ Set.Icc L U,
      |err a x / saddleCountScale φ x (12 * a + 1)| ≤ 1 / (12 * a + 1) ^ q := by
  obtain ⟨m, M, hm, hM, hpref⟩ := saddlePrefactor_uniform_bounds φ hL hLU
  filter_upwards [eventually_ge_atTop (2 : ℝ),
    eventually_sqrt_charge_exp_le (div_nonneg hC.le hm.le) hd q] with a ha hsmall
  intro x hx
  have hx0 : 0 < x := hL.trans_le hx.1
  have hc0 : 0 < 12 * a + 1 := by linarith
  have hp0 := saddlePrefactor_pos φ hx0
  have hs0 := saddleCountScale_pos φ hx0 hc0
  rw [abs_div, abs_of_pos hs0]
  calc
    _ ≤ (C * Real.exp (leadingAction x (12 * a + 1)) * Real.exp (-d * a)) /
        saddleCountScale φ x (12 * a + 1) := div_le_div_of_nonneg_right (herr a ha x hx) hs0.le
    _ = (C / saddlePrefactor φ x) * Real.sqrt (12 * a + 1) * Real.exp (-d * a) := by
      unfold saddleCountScale
      field_simp [hp0.ne', Real.exp_ne_zero, (Real.sqrt_pos.2 hc0).ne']
    _ ≤ (C / m) * Real.sqrt (12 * a + 1) * Real.exp (-d * a) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      exact div_le_div_of_nonneg_left hC.le hm (hpref x hx).1
    _ ≤ _ := hsmall

/-- An explicit quantified threshold form of the same scalar transfer. -/
theorem exists_normalized_exponential_error_threshold (φ : SmoothKernel)
    {L U C d : ℝ} (hL : 0 < L) (hLU : L ≤ U) (hC : 0 < C) (hd : 0 < d)
    (err : ℝ → ℝ → ℝ)
    (herr : ∀ a : ℝ, 2 ≤ a → ∀ x ∈ Set.Icc L U,
      |err a x| ≤ C * Real.exp (leadingAction x (12 * a + 1)) * Real.exp (-d * a))
    (q : ℕ) :
    ∃ A : ℝ, 2 ≤ A ∧ ∀ a, A ≤ a → ∀ x ∈ Set.Icc L U,
      |err a x / saddleCountScale φ x (12 * a + 1)| ≤ 1 / (12 * a + 1) ^ q := by
  obtain ⟨A, hA⟩ := Filter.eventually_atTop.mp
    (eventually_normalized_exponential_error_le φ hL hLU hC hd err herr q)
  exact ⟨max A 2, le_max_right _ _, fun a ha => hA a ((le_max_left _ _).trans ha)⟩

end BTZEntropy
