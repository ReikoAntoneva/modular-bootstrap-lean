import GapFamily.Analytic.Poincare.Seed.PoincareEnergySeedBasic
import GapFamily.Analytic.Poincare.Seed.PoincareEnergyFactorHigher
import GapFamily.Analytic.Poincare.Seed.PoincareSeedHigher

noncomputable section
namespace GapFamily.Analytic.PoincareEnergyHigher
open Set UpperHalfPlane PoincareSeedGradient PoincareTermRegularity
  PoincareSeedHigher PoincareEnergySeedBasic PoincareEnergyFactorHigher

/-- A finite product-rule coefficient retaining the extra energy-difference height. -/
def differenceSeedDerivativeConstant (n : ℕ) (S : ℝ) (E : ℂ) (J : ℤ) (M : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
    (seedDerivativeConstant i S J * (1 + M) ^ i) * energyDerivativeConstant (n - i) E M

theorem differenceSeedDerivativeConstant_nonneg (n : ℕ) {S M : ℝ}
    (hS : 0 ≤ S) (E : ℂ) (J : ℤ) (hM : 0 ≤ M) :
    0 ≤ differenceSeedDerivativeConstant n S E J M := by
  apply Finset.sum_nonneg
  intro i _hi
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
    (mul_nonneg (seedDerivativeConstant_nonneg i hS J) (pow_nonneg (by linarith) i)))
    (energyDerivativeConstant_nonneg (n - i) E hM)

/-- The actual energy-difference seed gains one image-height power in every
ordinary real derivative, for all complex energies and exponents. -/
theorem norm_iteratedFDeriv_rawDifferenceSeed_le (n : ℕ) (E : ℂ) (J : ℤ)
    {s : ℂ} {S M : ℝ} (hs : ‖s‖ ≤ S) (τ : UpperHalfPlane) (hM : τ.im ≤ M) :
    ‖iteratedFDeriv ℝ n (rawDifferenceSeed E J s) τ‖ ≤
      differenceSeedDerivativeConstant n S E J M * τ.im ^ (s.re + 1 - (n : ℝ)) := by
  have hS : 0 ≤ S := (norm_nonneg s).trans hs
  have hM0 : 0 ≤ M := τ.im_pos.le.trans hM
  have hf : ContDiffOn ℝ n (rawSeed J s) upperHalfPlaneSet := by
    intro z hz
    exact (contDiffAt_rawSeed (n := n) J s ⟨z, hz⟩).contDiffWithinAt
  have hg : ContDiff ℝ n (fun z : ℂ =>
      Complex.exp ((-2 * (Real.pi : ℂ) * E) * (z.im : ℂ)) - 1) := contDiff_energyFactor E
  have hp := norm_iteratedFDerivWithin_mul_le hf hg.contDiffOn
    isOpen_upperHalfPlaneSet.uniqueDiffOn τ.im_pos (n := n) le_rfl
  simp_rw [iteratedFDerivWithin_of_isOpen _ isOpen_upperHalfPlaneSet τ.im_pos] at hp
  calc
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (rawSeed J s) τ‖ *
        ‖iteratedFDeriv ℝ (n - i) (fun z : ℂ =>
          Complex.exp ((-2 * (Real.pi : ℂ) * E) * (z.im : ℂ)) - 1) τ‖ := hp
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ((seedDerivativeConstant i S J * (1 + M) ^ i) * τ.im ^ (s.re - (i : ℝ))) *
        (energyDerivativeConstant (n - i) E M * τ.im ^ (1 - ((n - i : ℕ) : ℝ))) := by
      apply Finset.sum_le_sum
      intro i _hi
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left
          (norm_iteratedFDeriv_rawSeed_le_of_height_le i J hs τ hM) (Nat.cast_nonneg _)
      · exact norm_iteratedFDeriv_energyFactor_le (n - i) E τ hM
      · exact norm_nonneg _
      · exact mul_nonneg (Nat.cast_nonneg _)
          (mul_nonneg (mul_nonneg (seedDerivativeConstant_nonneg i hS J)
            (pow_nonneg (by linarith) i)) (Real.rpow_nonneg τ.im_pos.le _))
    _ = ∑ i ∈ Finset.range (n + 1),
        ((n.choose i : ℝ) * (seedDerivativeConstant i S J * (1 + M) ^ i) *
          energyDerivativeConstant (n - i) E M) * τ.im ^ (s.re + 1 - (n : ℝ)) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have hy : τ.im ^ (s.re - (i : ℝ)) * τ.im ^ (1 - ((n - i : ℕ) : ℝ)) =
          τ.im ^ (s.re + 1 - (n : ℝ)) := by
        rw [← Real.rpow_add τ.im_pos]
        congr 1
        rw [Nat.cast_sub hi']
        ring
      calc
        _ = ((n.choose i : ℝ) * (seedDerivativeConstant i S J * (1 + M) ^ i) *
          energyDerivativeConstant (n - i) E M) *
          (τ.im ^ (s.re - (i : ℝ)) * τ.im ^ (1 - ((n - i : ℕ) : ℝ))) := by ring
        _ = _ := by rw [hy]
    _ = _ := by
      rw [← Finset.sum_mul]
      rfl

end GapFamily.Analytic.PoincareEnergyHigher
