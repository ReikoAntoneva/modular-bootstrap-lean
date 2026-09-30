import BTZEntropy.Comparison.CosineReconstruction
import BTZEntropy.Comparison.FourierDecay

/-! Polynomial approximation to every inverse-power order, proved from smoothness. -/

noncomputable section

open Set Polynomial
open scoped ContDiff

namespace BTZEntropy

theorem fourierCoeff_cosineCircle_eq (h : ℝ → ℝ) (hh : Continuous h) (n : ℤ) :
    fourierCoeff (cosineCircle h hh) n =
      fourierCoeffOn (by norm_num : (0 : ℝ) < 1) (cosineLine h) n :=
  fourierCoeff_cosineCircle h hh n

/-- All weighted absolute cosine coefficient sums converge for a smooth test function. -/
theorem summable_weighted_cosineCoefficient {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (P : ℕ) :
    Summable (fun n : ℤ =>
      |cosineCoefficient h hh.continuous n| * ((n.natAbs : ℝ) + 1) ^ P) := by
  have hs := summable_weighted_fourierCoeffOn (cosineLine_contDiff hh) (cosineLine_periodic h) P
  apply hs.of_norm_bounded
  intro n
  rw [Real.norm_of_nonneg (by positivity)]
  dsimp [cosineCoefficient]
  rw [fourierCoeff_cosineCircle_eq]
  have hnorm : (n.natAbs : ℝ) = ‖(n : ℝ)‖ := by
    rw [Real.norm_eq_abs]
    rw [← Int.cast_abs]
    exact Nat.cast_natAbs n
  rw [hnorm]
  exact mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm _) (by positivity)

/-- The full complex Fourier series used in reconstruction converges absolutely. -/
theorem summable_fourierCoeff_cosineCircle {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) :
    Summable (fourierCoeff (cosineCircle h hh.continuous)) := by
  have hs := summable_weighted_fourierCoeffOn (cosineLine_contDiff hh) (cosineLine_periodic h) 0
  simp only [pow_zero, mul_one] at hs
  apply Summable.of_norm
  simpa only [fourierCoeff_cosineCircle_eq] using hs

/-- A genuine quantitative polynomial approximation theorem for every `C∞` function.
The constant is independent of the polynomial degree, and the polynomial has that
literal degree bound. -/
theorem exists_rapid_polynomial_approximation {h : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (P : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, ∃ p : ℝ[X], p.degree ≤ k ∧
      ∀ x ∈ Icc (0 : ℝ) 1, |h x - p.eval x| ≤ C / ((k : ℝ) + 1) ^ P :=
  exists_polynomial_approximation_of_chebyshev
    (summable_weighted_cosineCoefficient hh P)
    (fun _ hx => hasSum_cosineCoefficient h hh.continuous
      (summable_fourierCoeff_cosineCircle hh) hx)

end BTZEntropy
