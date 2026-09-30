import BTZEntropy.Analytic.SaddleEntropy
import BTZEntropy.Analytic.SaddleEntropyAlgebra
import BTZEntropy.Analytic.CoefficientRegularity

/-! Actual coefficient regularity and charge growth turn a uniform real-charge
count expansion into the exact quantified entropy remainder in the contract. -/

noncomputable section

open Set Filter

namespace BTZEntropy

universe u

/-- The charge threshold is common to all ratios in the chosen compact
interval; both positivity and the next-order log error hold at that threshold. -/
theorem saddleCount_log_bound_on_charge
    (φ : SmoothKernel) (reference : ℝ → ℝ → ℝ)
    (hexp : UniformSaddleCountExpansion φ reference)
    (P : ℕ) (L U : ℝ) (hL : 0 < L) (hLU : L ≤ U) :
    ∃ C > 0, ∃ a₀ : ℝ, 1 ≤ a₀ ∧ ∀ a, a₀ ≤ a → ∀ x ∈ Icc L U,
      0 < reference x (GapFamily.gapFamilyCharge a) ∧
      |Real.log (reference x (GapFamily.gapFamilyCharge a)) -
        entropyTruncation φ x (GapFamily.gapFamilyCharge a) P| ≤
      C / GapFamily.gapFamilyCharge a ^ (P + 1) := by
  obtain ⟨M, hM, hcoeff⟩ := exists_pos_bound_saddleCountCoefficient_range φ P (U := U) hL
  obtain ⟨D, hD, c₀, hc₀, hcount⟩ := hexp P L U hL hLU
  obtain ⟨a₁, ha₁⟩ := eventually_atTop.1
    (GapFamily.tendsto_gapFamilyCharge_atTop.eventually_ge_atTop
      (max c₀ (max (2 * (P * M)) (4 * D))))
  have hpoly := logarithmPolynomialCoeffBound_nonneg P hM.le
  have hA : 0 ≤ (P : ℝ) * M := mul_nonneg (Nat.cast_nonneg P) hM.le
  refine ⟨4 * D + 2 * (P * M) ^ (P + 1) + logarithmPolynomialCoeffBound P M,
    by positivity, max 1 a₁, le_max_left _ _, ?_⟩
  intro a ha x hx
  have hapos : 1 ≤ a := (le_max_left 1 a₁).trans ha
  have hcharge := ha₁ a ((le_max_right 1 a₁).trans ha)
  have hc : 1 < GapFamily.gapFamilyCharge a :=
    GapFamily.gapFamilyCharge_gt_one (zero_lt_one.trans_le hapos)
  have hc₀a : c₀ ≤ GapFamily.gapFamilyCharge a := (le_max_left _ _).trans hcharge
  have hcMa : 2 * (P * M) ≤ GapFamily.gapFamilyCharge a :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hcharge)
  have hcDa : 4 * D ≤ GapFamily.gapFamilyCharge a :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hcharge)
  have hxpos : 0 < x := hL.trans_le hx.1
  have h := saddle_count_pos_and_normalized_log_error φ P hxpos hc.le hM.le
    (fun n _ hn => hcoeff n hn x hx) hcMa hcDa
    (hcount _ hc₀a x hx)
  refine ⟨h.1, ?_⟩
  rw [log_sub_entropyTruncation_eq_log_ratio_sub φ hxpos (zero_lt_one.trans hc) h.1 P]
  exact h.2

/-- Positivity is derived from the order-zero count expansion. -/
theorem uniformReferencePositive_of_saddleCountExpansion
    (φ : SmoothKernel) (reference : ℝ → ℝ → ℝ)
    (hexp : UniformSaddleCountExpansion φ reference) :
    UniformReferencePositive (fun a x => reference x (GapFamily.gapFamilyCharge a)) := by
  intro L U hL hLU
  obtain ⟨C, hC, a₀, ha₀, h⟩ := saddleCount_log_bound_on_charge φ reference hexp 0 L U hL hLU
  exact ⟨a₀, ha₀, fun a ha x hx => (h a ha x hx).1⟩

/-- No selector or gap can enter the constants: the reference depends only
on the common charge and energy ratio. -/
theorem uniformRemainder_log_reference_of_saddleCountExpansion
    {ι : Type u} (B : ℝ) (selectors : Set ι)
    (φ : SmoothKernel) (reference : ℝ → ℝ → ℝ)
    (hexp : UniformSaddleCountExpansion φ reference) (P : ℕ) :
    UniformRemainder B selectors (P + 1) (fun _ a _ x =>
      Real.log (reference x (GapFamily.gapFamilyCharge a)) -
        entropyTruncation φ x (GapFamily.gapFamilyCharge a) P) := by
  intro L U hL hLU
  obtain ⟨C, hC, a₀, ha₀, h⟩ := saddleCount_log_bound_on_charge φ reference hexp P L U hL hLU
  exact ⟨C, hC, a₀, ha₀, fun _ _ a ha _ _ x hx => (h a ha x hx).2⟩

/-- Relative matching to an actual count expansion proves the complete
uniform entropy property with its preassigned coefficient sequence. -/
theorem uniformSmoothEntropyExpansion_of_saddleCountExpansion
    {ι : Type u} {B : ℝ} {selectors : Set ι}
    {family : ι → ℝ → ℝ → GapFamily.Spectrum}
    (φ : SmoothKernel) (reference : ℝ → ℝ → ℝ)
    (hexp : UniformSaddleCountExpansion φ reference)
    (hmatch : ∀ q : ℕ, 1 ≤ q → UniformRemainder B selectors q
      (fun σ a δ x => smoothCount φ (GapFamily.gapFamilyCharge a) (family σ a δ)
        (x * GapFamily.gapFamilyCharge a) /
          reference x (GapFamily.gapFamilyCharge a) - 1)) :
    UniformSmoothEntropyExpansion B selectors family φ := by
  apply uniformSmoothEntropyExpansion_of_relative_matching
    (reference := fun a x => reference x (GapFamily.gapFamilyCharge a))
  · exact ⟨uniformReferencePositive_of_saddleCountExpansion φ reference hexp, hmatch⟩
  · exact uniformRemainder_log_reference_of_saddleCountExpansion B selectors φ reference hexp

end BTZEntropy
