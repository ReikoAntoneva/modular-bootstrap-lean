import GapFamily.Analytic.Spatial.SpatialOrbitFirstDerivative
import GapFamily.Analytic.Spatial.SpatialOrbitReal

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open MeasureTheory UpperHalfPlane
open scoped MatrixGroups ContDiff

/-- Positive real point values give the exact norm of the half-weighted orbit sum. -/
theorem norm_spatialOrbitKernel_eq_half_tsum_norm (σ : ℝ) (hσ : 1 < σ)
    (z w : UpperHalfPlane) :
    ‖spatialOrbitKernel (σ : ℂ) z w‖ =
      (1 / 2 : ℝ) * ∑' γ : SL(2, ℤ), ‖pointKernel (σ : ℂ) z (γ • w : UpperHalfPlane)‖ := by
  have hsum := summable_spatialOrbit (σ : ℂ) (by simpa using hσ) z w
  have hr (v : UpperHalfPlane) : (pointKernel (σ : ℂ) z v).re = ‖pointKernel (σ : ℂ) z v‖ := by
    rw [norm_pointKernel_real_exponent, pointKernel, ← Complex.ofReal_neg,
      ← Complex.ofReal_cpow (pointParameter_pos z.im_pos v.im_pos).le]
    simp
  rw [norm_spatialOrbitKernel_eq_re σ hσ, spatialOrbitKernel_eq_half_tsum_right,
    Complex.mul_re, Complex.re_tsum hsum]
  simp only [hr]
  norm_num

/-- Genuine frame-derivative bound for the actual normalized orbit kernel. -/
theorem spatialOrbitKernel_frame_fderiv_norm_le (s : ℂ) (hs : 1 < s.re)
    (z w : UpperHalfPlane) :
    z.im * ‖fderiv ℝ (fun v : ℂ => spatialOrbitKernel s (ofComplex v) w) (z : ℂ)‖ ≤
      ‖s‖ * ‖spatialOrbitKernel (s.re : ℂ) z w‖ := by
  let d : SL(2, ℤ) → (ℂ →L[ℝ] ℂ) := fun γ =>
    fderiv ℝ (fun v : ℂ => pointKernel s v (γ • w : UpperHalfPlane)) (z : ℂ)
  have hd := summable_norm_spatialOrbit_fderiv s hs z w
  have hk := summable_norm_spatialOrbit s hs z w
  have hsum : z.im * ∑' γ, ‖d γ‖ ≤
      ‖s‖ * ∑' γ : SL(2, ℤ), ‖pointKernel s z (γ • w : UpperHalfPlane)‖ := by
    dsimp only [d]
    simpa only [tsum_mul_left, UpperHalfPlane.coe_im] using
      (Summable.tsum_le_tsum
        (fun γ => pointKernel_frame_fderiv_norm_le_sharp s z.im_pos (γ • w : UpperHalfPlane).im_pos)
        (hd.mul_left z.im) (hk.mul_left ‖s‖))
  rw [fderiv_spatialOrbitKernel s hs z w, norm_smul,
    norm_spatialOrbitKernel_eq_half_tsum_norm s.re hs]
  norm_num only [norm_div, norm_one, Complex.norm_ofNat]
  have hnorm : ‖∑' γ, d γ‖ ≤ ∑' γ, ‖d γ‖ := norm_tsum_le_tsum_norm hd
  calc
    z.im * ((1 / 2) * ‖∑' γ, d γ‖) ≤ z.im * ((1 / 2) * ∑' γ, ‖d γ‖) := by gcongr
    _ = (1 / 2) * (z.im * ∑' γ, ‖d γ‖) := by ring
    _ ≤ (1 / 2) * (‖s‖ * ∑' γ : SL(2, ℤ), ‖pointKernel s z (γ • w : UpperHalfPlane)‖) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = ‖s‖ * ((1 / 2) * ∑' γ : SL(2, ℤ), ‖pointKernel (s.re : ℂ) z (γ • w : UpperHalfPlane)‖) := by
      have he : (fun γ : SL(2, ℤ) => ‖pointKernel s z (γ • w : UpperHalfPlane)‖) =
          (fun γ : SL(2, ℤ) => ‖pointKernel (s.re : ℂ) z (γ • w : UpperHalfPlane)‖) :=
        funext (fun γ => norm_pointKernel_eq_realPart s z (γ • w))
      rw [he]
      ring

end GapFamily.Analytic.SpatialPoint
