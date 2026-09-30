import GapFamily.Analytic.Kernel.FullKernelResponse
import GapFamily.Analytic.Kernel.HigherKernelSmoothingNorm
import GapFamily.Analytic.Foundation.ExponentialPolynomialBound

/-! Fixed-disk exponential bounds for the actual corrected low-band response.
The constants depend only on the disk, not the band, the finite spin family,
or the Hilbert input. No positivity premise is used. -/
noncomputable section
namespace GapFamily.Analytic
open Real

/-- A disk-dependent polynomial coefficient for the full response. -/
def correctedResponseDiskPolynomial (R : ℝ) : ℝ :=
  5 * (centralKernelBound + 16 * π ^ 2 * (R ^ 2 + 2) + 12 * R)

/-- One exponent absorbs the central term, the scalar rank term, the physical
spin count, and every remaining power of the band width. -/
def correctedResponseDiskExponent (R : ℝ) : ℝ :=
  correctedResponseDiskPolynomial R + 8 * π * sqrt (R ^ 2 + 2) + 3

theorem correctedResponseDiskPolynomial_pos (R : ℝ) (hR : 0 ≤ R) :
    0 < correctedResponseDiskPolynomial R := by
  unfold correctedResponseDiskPolynomial
  have := centralKernelBound_pos
  positivity

theorem correctedResponseDiskExponent_pos (R : ℝ) (hR : 0 ≤ R) :
    0 < correctedResponseDiskExponent R := by
  unfold correctedResponseDiskExponent
  have := correctedResponseDiskPolynomial_pos R hR
  positivity

/-- The exact compact coefficient grows at most polynomially times a band-linear
exponential on the square-root energy disk. -/
theorem fullKernelScaledCompactBound_le (j : ℤ) (B R : ℝ)
    (hB : 1 ≤ B) (hR : 0 ≤ R) (hj : |(j : ℝ)| ≤ B) :
    fullKernelCompactBound j B (|(j : ℝ)| + B * R ^ 2) * B + 12 * B * R ≤
      (centralKernelBound + 16 * π ^ 2 * (R ^ 2 + 2) + 12 * R) * B ^ 2 *
        exp (8 * π * sqrt (R ^ 2 + 2) * B) := by
  have hB0 : 0 ≤ B := by linarith
  have hC := centralKernelBound_pos.le
  have hExp : 1 ≤ exp (8 * π * sqrt (R ^ 2 + 2) * B) := by
    apply Real.one_le_exp_iff.mpr
    positivity
  have hHigher := higherKernelCompactBound_scaled_le j B
    (|(j : ℝ)| + B * R ^ 2) (R ^ 2 + 1) hB0 (by positivity) hj (by nlinarith)
  have hHigher' : higherKernelCompactBound j B (|(j : ℝ)| + B * R ^ 2) ≤
      16 * π ^ 2 * (R ^ 2 + 2) * B * exp (8 * π * sqrt (R ^ 2 + 2) * B) := by
    convert hHigher using 1
    ring_nf
  have hCentral : centralKernelBound * |(j : ℝ)| ≤
      centralKernelBound * B * exp (8 * π * sqrt (R ^ 2 + 2) * B) := by
    calc
      _ ≤ centralKernelBound * B := mul_le_mul_of_nonneg_left hj hC
      _ ≤ _ := le_mul_of_one_le_right (mul_nonneg hC hB0) hExp
  have hFull : fullKernelCompactBound j B (|(j : ℝ)| + B * R ^ 2) ≤
      (centralKernelBound + 16 * π ^ 2 * (R ^ 2 + 2)) * B *
        exp (8 * π * sqrt (R ^ 2 + 2) * B) := by
    exact (add_le_add hCentral hHigher').trans_eq (by ring)
  have hRank : 12 * B * R ≤
      12 * R * B ^ 2 * exp (8 * π * sqrt (R ^ 2 + 2) * B) := by
    calc
      _ = 12 * R * B := by ring
      _ ≤ 12 * R * B ^ 2 := by gcongr; nlinarith
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hExp
  calc
    _ ≤ ((centralKernelBound + 16 * π ^ 2 * (R ^ 2 + 2)) * B *
        exp (8 * π * sqrt (R ^ 2 + 2) * B)) * B +
        12 * R * B ^ 2 * exp (8 * π * sqrt (R ^ 2 + 2) * B) :=
      add_le_add (mul_le_mul_of_nonneg_right hFull hB0) hRank
    _ = _ := by ring

/-- The finite physical spin count is included in one disk-dependent exponent. -/
theorem fullKernelScaledCardBound_le_exp {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (hJ : Function.Injective J) (B R : ℝ)
    (hB : 1 ≤ B) (hR : 0 ≤ R) (hband : ∀ i, |(J i : ℝ)| < B)
    (j : ℤ) (hj : |(j : ℝ)| ≤ B) :
    (Fintype.card ι : ℝ) *
        (fullKernelCompactBound j B (|(j : ℝ)| + B * R ^ 2) * B + 12 * B * R) ≤
      exp (correctedResponseDiskExponent R * B) := by
  have hB0 : 0 ≤ B := by linarith
  have hCoeff : 0 ≤ fullKernelCompactBound j B (|(j : ℝ)| + B * R ^ 2) * B +
      12 * B * R := by
    have := fullKernelCompactBound_nonneg j B (|(j : ℝ)| + B * R ^ 2) (by positivity)
    positivity
  calc
    _ ≤ (5 * B) *
        ((centralKernelBound + 16 * π ^ 2 * (R ^ 2 + 2) + 12 * R) * B ^ 2 *
          exp (8 * π * sqrt (R ^ 2 + 2) * B)) :=
      mul_le_mul (physicalLowBand_card_le J hJ hB hband)
        (fullKernelScaledCompactBound_le j B R hB hR hj) hCoeff (by positivity)
    _ = correctedResponseDiskPolynomial R * B ^ 3 *
        exp (8 * π * sqrt (R ^ 2 + 2) * B) := by
      unfold correctedResponseDiskPolynomial
      ring
    _ ≤ _ := by
      simpa only [correctedResponseDiskExponent, Nat.cast_ofNat] using
        polynomial_mul_exp_le_exp (D := 8 * π * sqrt (R ^ 2 + 2))
          (correctedResponseDiskPolynomial_pos R hR).le hB 3

/-- The full corrected response has a fixed-disk `exp(C_R B)` Hilbert bound,
uniform over every injective family of physical input spins. -/
theorem norm_correctedKernelScaledResponse_le_exp {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (hJ : Function.Injective J) (B : ℝ) (hB : 1 ≤ B)
    (hband : ∀ i, |(J i : ℝ)| < B) (f : LowBandHilbert J B)
    (j : ℤ) (hj : |(j : ℝ)| ≤ B) (R : ℝ) (hR : 0 ≤ R)
    (z : ℂ) (hz : ‖z‖ ≤ R) :
    ‖correctedKernelScaledResponse J B f j z‖ ≤
      exp (correctedResponseDiskExponent R * B) * ‖f‖ := by
  have hBpos : 0 < B := by linarith
  exact (norm_correctedKernelScaledResponse_le J B hBpos f j R hR z hz).trans
    (mul_le_mul_of_nonneg_right
      (fullKernelScaledCardBound_le_exp J hJ B R hB hR hband j hj) (norm_nonneg _))

/-- The scalar removable quotient obeys the same exponential control, using
the enclosing disk of radius `R + 1`. This includes its actual value at zero. -/
theorem norm_correctedKernelScalarNormalizedResponse_le_exp {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (hJ : Function.Injective J) (B : ℝ) (hB : 1 ≤ B)
    (hband : ∀ i, |(J i : ℝ)| < B) (f : LowBandHilbert J B)
    (R : ℝ) (hR : 0 ≤ R) (z : ℂ) (hz : ‖z‖ ≤ R) :
    ‖correctedKernelScalarNormalizedResponse J B f z‖ ≤
      exp (correctedResponseDiskExponent (R + 1) * B) * ‖f‖ := by
  have hBpos : 0 < B := by linarith
  have hc := fullKernelScaledCardBound_le_exp J hJ B (R + 1) hB (by linarith)
    hband 0 (by simpa using hBpos.le)
  simp only [Int.cast_zero, abs_zero, zero_add] at hc
  calc
    _ ≤ ((Fintype.card ι : ℝ) *
        (fullKernelCompactBound 0 B (B * (R + 1) ^ 2) * B + 12 * B * (R + 1)) * ‖f‖) /
          (R + 1) := norm_correctedKernelScalarNormalizedResponse_le J B hBpos f R hR z hz
    _ ≤ (exp (correctedResponseDiskExponent (R + 1) * B) * ‖f‖) / (R + 1) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hc (norm_nonneg _)) (by linarith)
    _ ≤ _ := div_le_self (by positivity) (by linarith)

/-- One positive disk constant works simultaneously for the full response and
its scalar removable quotient, for every admissible finite input spin family. -/
theorem exists_correctedResponse_fixedDisk_bound (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [Fintype ι]
      (J : ι → ℤ), Function.Injective J → ∀ (B : ℝ), 1 ≤ B →
      (∀ i, |(J i : ℝ)| < B) → ∀ (f : LowBandHilbert J B)
      (j : ℤ), |(j : ℝ)| ≤ B → ∀ z : ℂ, ‖z‖ ≤ R →
      ‖correctedKernelScaledResponse J B f j z‖ ≤ exp (C * B) * ‖f‖ ∧
      ‖correctedKernelScalarNormalizedResponse J B f z‖ ≤ exp (C * B) * ‖f‖ := by
  refine ⟨correctedResponseDiskExponent (R + 1),
    correctedResponseDiskExponent_pos (R + 1) (by linarith), ?_⟩
  intro ι _ J hJ B hB hband f j hj z hz
  exact ⟨norm_correctedKernelScaledResponse_le_exp J hJ B hB hband f j hj
      (R + 1) (by linarith) z (by linarith),
    norm_correctedKernelScalarNormalizedResponse_le_exp J hJ B hB hband f R hR z hz⟩

end GapFamily.Analytic
