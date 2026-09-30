import BTZEntropy.Analytic.Prefactor
import BTZEntropy.Contract
import GapFamily.GapFamilyLimit

/-!
# Normalizing the discrete-reference comparison

The Gaussian prefactor has a positive lower bound on each compact positive
energy-ratio interval. Consequently the actual exponential-scale raw error
becomes an inverse-charge remainder after division by the saddle count scale.
-/

noncomputable section

open Set Filter GapFamily

namespace BTZEntropy.Comparison

universe u

/-- Dividing the raw count error cancels its precise exponential and
square-root factors. The lower prefactor bound is uniform in energy ratio. -/
theorem abs_div_saddleCountScale_le {φ : SmoothKernel} {x c z C m : ℝ} {P : ℕ}
    (hx : 0 < x) (hc : 0 < c) (hC : 0 ≤ C) (hm : 0 < m)
    (hmp : m ≤ saddlePrefactor φ x)
    (hz : |z| ≤ C * Real.exp (leadingAction x c) / (Real.sqrt c * c ^ P)) :
    |z / saddleCountScale φ x c| ≤ (C / m) / c ^ P := by
  have hs := saddleCountScale_pos φ hx hc
  have hp := saddlePrefactor_pos φ hx
  have hr := Real.sqrt_pos.2 hc
  rw [abs_div, abs_of_pos hs]
  calc
    _ ≤ (C * Real.exp (leadingAction x c) / (Real.sqrt c * c ^ P)) /
        saddleCountScale φ x c := div_le_div_of_nonneg_right hz hs.le
    _ = (C / saddlePrefactor φ x) / c ^ P := by
      unfold saddleCountScale
      field_simp
    _ ≤ _ := div_le_div_of_nonneg_right
      (div_le_div_of_nonneg_left hC hm hmp) (pow_nonneg hc.le P)

/-- A uniform raw comparison at the real central charge yields exactly
the normalized remainder contract. The constant and threshold precede all
selector, gap, and energy-ratio choices. -/
theorem uniformRemainder_div_saddleCountScale_of_raw_bound
    {ι : Type u} (B : ℝ) (selectors : Set ι) (φ : SmoothKernel) (P : ℕ)
    (f : ι → ℝ → ℝ → ℝ → ℝ)
    (hraw : ∀ L U : ℝ, 0 < L → L ≤ U →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ a in atTop,
        ∀ σ ∈ selectors, ∀ δ ∈ Ico (0 : ℝ) B, ∀ x ∈ Icc L U,
          |f σ a δ x| ≤ C * Real.exp (leadingAction x (gapFamilyCharge a)) /
            (Real.sqrt (gapFamilyCharge a) * (gapFamilyCharge a) ^ P)) :
    UniformRemainder B selectors P
      (fun σ a δ x => f σ a δ x / saddleCountScale φ x (gapFamilyCharge a)) := by
  intro L U hL hLU
  obtain ⟨C, hC, hraw⟩ := hraw L U hL hLU
  obtain ⟨m, M, hm, _, hpref⟩ := saddlePrefactor_uniform_bounds φ hL hLU
  obtain ⟨N, hN⟩ := eventually_atTop.1 hraw
  refine ⟨(C + 1) / m, div_pos (by linarith) hm, max N 1,
    le_max_right _ _, ?_⟩
  intro σ hσ a hK δ hδ x hx
  have hc : 0 < gapFamilyCharge a :=
    lt_trans (by norm_num : (0 : ℝ) < 1)
      (gapFamilyCharge_gt_one (by have := (le_max_right N 1).trans hK; linarith))
  calc
    _ ≤ (C / m) / (gapFamilyCharge a) ^ P :=
      abs_div_saddleCountScale_le (hL.trans_le hx.1) hc hC hm (hpref x hx).1
        (hN a ((le_max_left N 1).trans hK) σ hσ δ hδ x hx)
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg hc.le P)
      exact div_le_div_of_nonneg_right (by linarith) hm.le

end BTZEntropy.Comparison
