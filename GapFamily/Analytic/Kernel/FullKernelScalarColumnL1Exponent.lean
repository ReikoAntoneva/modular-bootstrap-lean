import GapFamily.Analytic.Kernel.FullKernelScalarColumnBound
import GapFamily.Analytic.Foundation.ExponentialPolynomialBound

/-!
# Fixed-disk exponential bound for the ordinary scalar-column mass

The energy and square-root energy moments produce an explicit ordinary `L¹`
coefficient. On bands of width at least one, its polynomial factor is absorbed
into an exponential whose rate depends only on the complex disk radius.
-/

noncomputable section

open Real

namespace GapFamily.Analytic

/-- The ordinary low-band mass bound for a scalar column on `‖z‖ ≤ R`. -/
def scalarColumnL1DiskBound (B R : ℝ) : ℝ :=
  higherKernelCompactBound 0 B (B * R ^ 2) * B +
    12 * sqrt B * R * (B + 2 * sqrt B)

theorem scalarColumnL1DiskBound_nonneg (B R : ℝ) (hB : 0 ≤ B) (hR : 0 ≤ R) :
    0 ≤ scalarColumnL1DiskBound B R := by
  have := higherKernelCompactBound_nonneg 0 B (B * R ^ 2) (by positivity)
  unfold scalarColumnL1DiskBound
  positivity

/-- The ordinary mass coefficient has a quadratic polynomial prefactor and
a band-linear exponential rate. -/
theorem scalarColumnL1DiskBound_le_polynomial_exp (B R : ℝ)
    (hB : 1 ≤ B) (hR : 0 ≤ R) :
    scalarColumnL1DiskBound B R ≤
      (16 * π ^ 2 * (R ^ 2 + 1) + 36 * R) * B ^ 2 *
        exp (8 * π * sqrt (R ^ 2 + 1) * B) := by
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hs : sqrt B ≤ B := sqrt_le_self_iff.mpr (Or.inr hB)
  have hExp : 1 ≤ exp (8 * π * sqrt (R ^ 2 + 1) * B) := by
    apply one_le_exp_iff.mpr
    positivity
  have hHigher := higherKernelCompactBound_scaled_le 0 B (B * R ^ 2) (R ^ 2)
    hB0 (sq_nonneg R) (by simpa using hB0) (by rw [mul_comm])
  have hRank : 12 * sqrt B * R * (B + 2 * sqrt B) ≤
      36 * R * B ^ 2 * exp (8 * π * sqrt (R ^ 2 + 1) * B) := by
    calc
      _ ≤ 12 * B * R * (B + 2 * B) := by gcongr
      _ = 36 * R * B ^ 2 := by ring
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hExp
  unfold scalarColumnL1DiskBound
  calc
    _ ≤ (16 * π ^ 2 * (R ^ 2 + 1) * B *
        exp (8 * π * sqrt (R ^ 2 + 1) * B)) * B +
        36 * R * B ^ 2 * exp (8 * π * sqrt (R ^ 2 + 1) * B) :=
      add_le_add (mul_le_mul_of_nonneg_right hHigher hB0) hRank
    _ = _ := by ring

/-- One disk-dependent rate absorbs the full ordinary mass coefficient. -/
def scalarColumnL1DiskExponent (R : ℝ) : ℝ :=
  (16 * π ^ 2 * (R ^ 2 + 1) + 36 * R) + 8 * π * sqrt (R ^ 2 + 1) + 2

theorem scalarColumnL1DiskExponent_pos (R : ℝ) (hR : 0 ≤ R) :
    0 < scalarColumnL1DiskExponent R := by
  unfold scalarColumnL1DiskExponent
  positivity

/-- The fixed-disk ordinary mass bound grows at most exponentially in `B`. -/
theorem scalarColumnL1DiskBound_le_exp (B R : ℝ) (hB : 1 ≤ B) (hR : 0 ≤ R) :
    scalarColumnL1DiskBound B R ≤ exp (scalarColumnL1DiskExponent R * B) := by
  apply (scalarColumnL1DiskBound_le_polynomial_exp B R hB hR).trans
  simpa only [scalarColumnL1DiskExponent, Nat.cast_ofNat] using
    polynomial_mul_exp_le_exp
      (A := 16 * π ^ 2 * (R ^ 2 + 1) + 36 * R)
      (D := 8 * π * sqrt (R ^ 2 + 1)) (by positivity) hB 2

/-- The exponent that also absorbs the finite physical spin count. -/
def scalarColumnL1DiskCardExponent (R : ℝ) : ℝ :=
  5 * (16 * π ^ 2 * (R ^ 2 + 1) + 36 * R) + 8 * π * sqrt (R ^ 2 + 1) + 3

theorem scalarColumnL1DiskCardExponent_pos (R : ℝ) (hR : 0 ≤ R) :
    0 < scalarColumnL1DiskCardExponent R := by
  unfold scalarColumnL1DiskCardExponent
  positivity

/-- A linear bound on the physical spin count is absorbed into the same kind
of fixed-disk exponential estimate. -/
theorem scalarColumnL1DiskBound_mul_five_band_le_exp (B R : ℝ)
    (hB : 1 ≤ B) (hR : 0 ≤ R) :
    (5 * B) * scalarColumnL1DiskBound B R ≤
      exp (scalarColumnL1DiskCardExponent R * B) := by
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  calc
    _ ≤ (5 * B) * ((16 * π ^ 2 * (R ^ 2 + 1) + 36 * R) * B ^ 2 *
        exp (8 * π * sqrt (R ^ 2 + 1) * B)) :=
      mul_le_mul_of_nonneg_left
        (scalarColumnL1DiskBound_le_polynomial_exp B R hB hR) (by positivity)
    _ = (5 * (16 * π ^ 2 * (R ^ 2 + 1) + 36 * R)) * B ^ 3 *
        exp (8 * π * sqrt (R ^ 2 + 1) * B) := by ring
    _ ≤ _ := by
      simpa only [scalarColumnL1DiskCardExponent, Nat.cast_ofNat] using
        polynomial_mul_exp_le_exp
          (A := 5 * (16 * π ^ 2 * (R ^ 2 + 1) + 36 * R))
          (D := 8 * π * sqrt (R ^ 2 + 1)) (by positivity) hB 3

end GapFamily.Analytic
