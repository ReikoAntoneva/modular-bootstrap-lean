import GapFamily.Analytic.Poincare.Arithmetic.PoincareCentralQuotient
import GapFamily.Analytic.Poincare.Arithmetic.PoincareCentralFrequencyBound
import GapFamily.Analytic.Poincare.Fourier.PoincareFourierRemainderThreshold
import GapFamily.Analytic.Poincare.Threshold.PoincareThresholdHeightReduction
import GapFamily.Analytic.Poincare.Arithmetic.PoincareCentralBaseHeight

noncomputable section
namespace GapFamily.Analytic.PoincareCentralZeta
open Set MeasureTheory UpperHalfPlane PoincareCanonical
  PoincareFourierContinuation PoincareFourierRemainder
  PoincareCentralFactor PoincareThresholdHeightReduction

/-- The actual central numerator at threshold inherits its ordinary Fourier bound
from the single closed-fundamental-domain estimate for the canonical spin-one seed. -/
theorem centralNumerator_threshold_norm_le_of_fd_bound {C : ℝ} (hC : 0 ≤ C)
    (hfd : ∀ τ : UpperHalfPlane, τ ∈ ModularGroup.fd →
      ‖thresholdSeed 1 τ‖ ≤ C * Real.sqrt τ.im)
    (y : ℝ) (hy : 0 < y) (hy1 : y ≤ 1) (N : ℤ) :
    ‖centralNumerator y hy N 1 0‖ ≤
      (C + 1 + fourierRemainderThresholdConstant) / Real.sqrt y := by
  have hf := thresholdFourierCoefficient_norm_le_inv_sqrt_of_fd_bound 1 hC hfd y hy hy1 N
  have hd := norm_directThreshold_le_inv_sqrt hy hy1 N
  have hr := norm_fourierRemainder_threshold_le hy N 1
  norm_num only [Int.cast_one, abs_one, mul_one] at hr
  rw [centralNumerator_zero]
  calc
    _ ≤ ‖thresholdFourierCoefficient y hy N 1‖ +
        ‖(if N = 1 then (y : ℂ) ^ (1 / 2 : ℂ) else 0)‖ +
          ‖fourierRemainder y N 1 (1 / 2 : ℂ)‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ C / Real.sqrt y + 1 / Real.sqrt y +
        fourierRemainderThresholdConstant / Real.sqrt y :=
      add_le_add (add_le_add hf hd) hr
    _ = _ := by ring

/-- The actual threshold central zeta has a uniform linear normalized-frequency bound,
given only the stated square-root height bound for the actual canonical spin-one seed.
The Fourier factorization, remainder, and factor inverse estimates are proved dependencies. -/
theorem exists_centralZeta_base_bound_of_threshold_fd_bound {C : ℝ} (hC : 0 ≤ C)
    (hfd : ∀ τ : UpperHalfPlane, τ ∈ ModularGroup.fd →
      ‖thresholdSeed 1 τ‖ ≤ C * Real.sqrt τ.im) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ N : ℤ, N ≠ 0 →
      ‖centralZeta N 1 0‖ ≤ C' * |(N : ℝ)| := by
  obtain ⟨δ, hδ, _hδ8, D, hD, hfactor⟩ := exists_centralFourierFactor_frequency_bounds
  have hR := fourierRemainderThresholdConstant_pos
  have hA : 0 < C + 1 + fourierRemainderThresholdConstant := by positivity
  refine ⟨2 * (C + 1 + fourierRemainderThresholdConstant) * D, by positivity, ?_⟩
  intro N hN
  have hy := frequencyHeight_pos N
  have hy1 := frequencyHeight_le_one N
  have hnum := centralNumerator_threshold_norm_le_of_fd_bound hC hfd
    (frequencyHeight N) hy hy1 N
  have hzero : ‖(0 : ℂ)‖ ≤ δ := by simpa only [norm_zero] using hδ.le
  have hinv : ‖(centralFourierFactor (frequencyHeight N) N 0)⁻¹‖ ≤
      D * Real.sqrt (1 + |(N : ℝ)|) := by
    simpa only [Complex.zero_re, neg_zero, Real.rpow_zero, mul_one] using
      (hfactor N hN 0 hzero).2.2
  have hn := one_le_abs_frequency hN
  rw [centralZeta_zero_eq_height (frequencyHeight N) hy N 1 hN, div_eq_mul_inv, norm_mul]
  calc
    _ ≤ ((C + 1 + fourierRemainderThresholdConstant) / Real.sqrt (frequencyHeight N)) *
        (D * Real.sqrt (1 + |(N : ℝ)|)) :=
      mul_le_mul hnum hinv (norm_nonneg _) (by positivity)
    _ = (C + 1 + fourierRemainderThresholdConstant) * D * (1 + |(N : ℝ)|) :=
      frequencyHeight_sqrt_product _ _ N
    _ ≤ ((C + 1 + fourierRemainderThresholdConstant) * D) * (2 * |(N : ℝ)|) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hA.le hD.le)
    _ = _ := by ring

end GapFamily.Analytic.PoincareCentralZeta
