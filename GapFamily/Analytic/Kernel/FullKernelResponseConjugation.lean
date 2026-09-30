import GapFamily.Analytic.Kernel.FullKernelResponse
import GapFamily.Analytic.Kernel.FullKernelReality
import GapFamily.Analytic.Kernel.FullKernelConjugation

/-! Schwarz reflection for the actual ordinary full-kernel response and its
scalar removable quotient. The input conjugation is the conjugation of the
physical Hilbert rows, with their almost-everywhere representatives respected. -/

noncomputable section
namespace GapFamily.Analytic
open MeasureTheory
open scoped ComplexConjugate

theorem conj_fullKernelRowResponse (j J : ℤ) (B : ℝ)
    (f : LowBandRow J B) (z : ℂ) :
    conj (fullKernelRowResponse j J B f z) =
      fullKernelRowResponse j J B (star f) (conj z) := by
  unfold fullKernelRowResponse
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star f] with E hE
  simp only [map_mul, conj_fullKernelHol, Complex.conj_ofReal, hE,
    Pi.star_apply, Complex.star_def]

theorem conj_correctedKernelRowResponse (j J : ℤ) (B : ℝ)
    (f : LowBandRow J B) (e : ℝ) :
    conj (correctedKernelRowResponse j J B f e) =
      correctedKernelRowResponse j J B (star f) e := by
  unfold correctedKernelRowResponse
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star f] with E hE
  simp only [map_mul, conj_correctedKernel, hE, Pi.star_apply, Complex.star_def]

theorem conj_lowBandHalfMoment (J : ℤ) (B : ℝ) (f : LowBandRow J B) :
    conj (lowBandHalfMoment J B f) = lowBandHalfMoment J B (star f) := by
  unfold lowBandHalfMoment
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star f] with E hE
  simp only [map_mul, Complex.conj_ofReal, hE, Pi.star_apply, Complex.star_def]

variable {ι : Type*} [Fintype ι]

/-- Schwarz reflection for every complex output energy of the actual response. -/
theorem conj_fullKernelResponse (J : ι → ℤ) (B : ℝ)
    (f : LowBandHilbert J B) (j : ℤ) (z : ℂ) :
    conj (fullKernelResponse J B f j z) =
      fullKernelResponse J B (lowBandConj J B f) j (conj z) := by
  simp only [fullKernelResponse, map_sum, conj_fullKernelRowResponse, lowBandConj_apply]

theorem conj_correctedKernelResponse (J : ι → ℤ) (B : ℝ)
    (f : LowBandHilbert J B) (j : ℤ) (e : ℝ) :
    conj (correctedKernelResponse J B f j e) =
      correctedKernelResponse J B (lowBandConj J B f) j e := by
  simp only [correctedKernelResponse, map_sum, conj_correctedKernelRowResponse,
    lowBandConj_apply]

theorem conj_lowBandScalarMoment (J : ι → ℤ) (B : ℝ)
    (f : LowBandHilbert J B) :
    conj (lowBandScalarMoment J B f) = lowBandScalarMoment J B (lowBandConj J B f) := by
  simp only [lowBandScalarMoment, map_sum, apply_ite, conj_lowBandHalfMoment,
    map_zero, lowBandConj_apply]

/-- The entire response in square-root coordinates has global Schwarz reflection. -/
theorem conj_correctedKernelScaledResponse (J : ι → ℤ) (B : ℝ)
    (f : LowBandHilbert J B) (j : ℤ) (z : ℂ) :
    conj (correctedKernelScaledResponse J B f j z) =
      correctedKernelScaledResponse J B (lowBandConj J B f) j (conj z) := by
  by_cases hj : j = 0 <;>
    simp only [correctedKernelScaledResponse, hj, ite_true, ite_false,
      map_add, conj_fullKernelResponse, map_mul, map_pow, Complex.conj_ofReal,
      map_ofNat, conj_lowBandScalarMoment, map_zero]

/-- Schwarz reflection persists through the scalar removable value at zero. -/
theorem conj_correctedKernelScalarNormalizedResponse (J : ι → ℤ) (B : ℝ)
    (hB : 0 < B) (f : LowBandHilbert J B) (z : ℂ) :
    conj (correctedKernelScalarNormalizedResponse J B f z) =
      correctedKernelScalarNormalizedResponse J B (lowBandConj J B f) (conj z) := by
  by_cases hz : z = 0
  · subst z
    simp only [map_zero, correctedKernelScalarNormalizedResponse_zero J B hB,
      map_mul, map_ofNat, Complex.conj_ofReal, conj_lowBandScalarMoment]
  · have hcz : conj z ≠ 0 := by
      simpa only [map_ne_zero] using hz
    rw [correctedKernelScalarNormalizedResponse_eq_div J B f z hz,
      correctedKernelScalarNormalizedResponse_eq_div J B (lowBandConj J B f)
        (conj z) hcz,
      map_div₀, conj_correctedKernelScaledResponse]

/-- Every real output energy has a real response for real physical Hilbert input. -/
theorem conj_fullKernelResponse_ofReal (J : ι → ℤ) (B : ℝ)
    (f : LowBandHilbert J B) (hf : LowBandIsReal J B f) (j : ℤ) (e : ℝ) :
    conj (fullKernelResponse J B f j (e : ℂ)) = fullKernelResponse J B f j e := by
  rw [conj_fullKernelResponse, hf, Complex.conj_ofReal]

theorem conj_correctedKernelResponse_of_real (J : ι → ℤ) (B : ℝ)
    (f : LowBandHilbert J B) (hf : LowBandIsReal J B f) (j : ℤ) (e : ℝ) :
    conj (correctedKernelResponse J B f j e) = correctedKernelResponse J B f j e := by
  rw [conj_correctedKernelResponse, hf]

theorem conj_lowBandScalarMoment_of_real (J : ι → ℤ) (B : ℝ)
    (f : LowBandHilbert J B) (hf : LowBandIsReal J B f) :
    conj (lowBandScalarMoment J B f) = lowBandScalarMoment J B f := by
  rw [conj_lowBandScalarMoment, hf]

/-- Real square-root coordinates of either sign have real corrected response. -/
theorem conj_correctedKernelScaledResponse_ofReal (J : ι → ℤ) (B : ℝ)
    (f : LowBandHilbert J B) (hf : LowBandIsReal J B f) (j : ℤ) (t : ℝ) :
    conj (correctedKernelScaledResponse J B f j (t : ℂ)) =
      correctedKernelScaledResponse J B f j t := by
  rw [conj_correctedKernelScaledResponse, hf, Complex.conj_ofReal]

/-- The scalar response is real on the whole real axis, including its removable point. -/
theorem conj_correctedKernelScalarNormalizedResponse_ofReal (J : ι → ℤ) (B : ℝ)
    (hB : 0 < B) (f : LowBandHilbert J B) (hf : LowBandIsReal J B f) (t : ℝ) :
    conj (correctedKernelScalarNormalizedResponse J B f (t : ℂ)) =
      correctedKernelScalarNormalizedResponse J B f t := by
  rw [conj_correctedKernelScalarNormalizedResponse J B hB, hf, Complex.conj_ofReal]

theorem fullKernelResponse_ofReal_im (J : ι → ℤ) (B : ℝ)
    (f : LowBandHilbert J B) (hf : LowBandIsReal J B f) (j : ℤ) (e : ℝ) :
    (fullKernelResponse J B f j (e : ℂ)).im = 0 :=
  Complex.conj_eq_iff_im.mp (conj_fullKernelResponse_ofReal J B f hf j e)

theorem correctedKernelResponse_im (J : ι → ℤ) (B : ℝ)
    (f : LowBandHilbert J B) (hf : LowBandIsReal J B f) (j : ℤ) (e : ℝ) :
    (correctedKernelResponse J B f j e).im = 0 :=
  Complex.conj_eq_iff_im.mp (conj_correctedKernelResponse_of_real J B f hf j e)

theorem correctedKernelScaledResponse_ofReal_im (J : ι → ℤ) (B : ℝ)
    (f : LowBandHilbert J B) (hf : LowBandIsReal J B f) (j : ℤ) (t : ℝ) :
    (correctedKernelScaledResponse J B f j (t : ℂ)).im = 0 :=
  Complex.conj_eq_iff_im.mp (conj_correctedKernelScaledResponse_ofReal J B f hf j t)

theorem correctedKernelScalarNormalizedResponse_ofReal_im (J : ι → ℤ) (B : ℝ)
    (hB : 0 < B) (f : LowBandHilbert J B) (hf : LowBandIsReal J B f) (t : ℝ) :
    (correctedKernelScalarNormalizedResponse J B f (t : ℂ)).im = 0 :=
  Complex.conj_eq_iff_im.mp
    (conj_correctedKernelScalarNormalizedResponse_ofReal J B hB f hf t)

end GapFamily.Analytic
