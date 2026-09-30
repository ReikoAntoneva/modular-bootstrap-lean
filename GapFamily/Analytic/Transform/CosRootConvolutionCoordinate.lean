import GapFamily.Analytic.Transform.CosRootConvolution
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! The literal energy coordinate in the regularized cosRoot convolution. -/
noncomputable section
namespace GapFamily.Analytic.CosRootLaplace
open Set MeasureTheory

/-- The ordinary energy kernel, with the zero-energy subtraction kept together. -/
def cosRootConvolutionEnergyKernel (a : ℝ) (A B : ℂ) (j e : ℝ) : ℂ :=
  Complex.exp (-(a : ℂ) * (e : ℂ)) / (Real.sqrt (e ^ 2 - j ^ 2) : ℂ) *
    (cosRoot (A * ((e + j : ℝ) : ℂ) / 2) *
      cosRoot (B * ((e - j : ℝ) : ℂ) / 2) - 1)

/-- The two genuinely integrable summands of the convolution at `-j`. -/
def cosRootConvolutionRaw (a : ℝ) (A B : ℂ) (j t : ℝ) : ℂ :=
  regularHalfProfile a A (-t) * halfProfile a B (-j - t) +
    halfProfile a 0 (-t) * regularHalfProfile a B (-j - t)

private theorem profile_product_sub (a : ℝ) (A B : ℂ) {x z : ℝ}
    (hx : 0 < x) (hz : 0 < z) :
    regularHalfProfile a A x * halfProfile a B z +
      halfProfile a 0 x * regularHalfProfile a B z =
        (((x ^ (-1 / 2 : ℝ) * z ^ (-1 / 2 : ℝ)) : ℝ) : ℂ) *
          Complex.exp (-(a : ℂ) * ((x + z : ℝ) : ℂ)) *
            (cosRoot (A * (x : ℂ)) * cosRoot (B * (z : ℂ)) - 1) := by
  simp only [regularHalfProfile, halfProfile, ite_eq_left hx, ite_eq_left hz, zero_mul,
    cosRoot_zero, mul_one]
  have he : Complex.exp (-(a : ℂ) * ((x + z : ℝ) : ℂ)) =
      Complex.exp (-(a : ℂ) * (x : ℂ)) * Complex.exp (-(a : ℂ) * (z : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he]
  push_cast
  ring

private theorem rpow_product_eq_two_div_sqrt {x z : ℝ} (hx : 0 < x) (hz : 0 < z) :
    x ^ (-1 / 2 : ℝ) * z ^ (-1 / 2 : ℝ) =
      2 / Real.sqrt ((x + z) ^ 2 - (x - z) ^ 2) := by
  have he : (x + z) ^ 2 - (x - z) ^ 2 = (2 : ℝ) ^ 2 * (x * z) := by ring
  rw [he, Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num),
    Real.sqrt_mul hx.le]
  have hp (w : ℝ) (hw : 0 < w) : w ^ (-1 / 2 : ℝ) = (Real.sqrt w)⁻¹ := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring, Real.rpow_neg hw.le,
      ← Real.sqrt_eq_rpow]
  rw [hp x hx, hp z hz]
  norm_num [div_eq_mul_inv, mul_inv]
  ring

/-- The open support is exactly the strict energy threshold under the affine change. -/
theorem cosRootConvolution_energy_support (j t : ℝ) :
    (0 < -t ∧ 0 < -j - t) ↔ |j| < -2 * t - j := by
  rw [abs_lt]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

/-- The two inverse-square-root profiles contribute the exact factor two Jacobian. -/
theorem cosRootConvolutionRaw_eq_energyKernel (a : ℝ) (A B : ℂ) (j t : ℝ) :
    cosRootConvolutionRaw a A B j t =
      2 * (Ioi |j|).indicator (cosRootConvolutionEnergyKernel a A B j) (-2 * t - j) := by
  by_cases h : 0 < -t ∧ 0 < -j - t
  · have he : -2 * t - j ∈ Ioi |j| := (cosRootConvolution_energy_support j t).mp h
    rw [indicator_of_mem he, cosRootConvolutionRaw, profile_product_sub a A B h.1 h.2]
    rw [rpow_product_eq_two_div_sqrt h.1 h.2]
    have hsum : -t + (-j - t) = -2 * t - j := by ring
    have hdiff : -t - (-j - t) = j := by ring
    rw [hsum, hdiff]
    have hA : A * (((-2 * t - j + j : ℝ) : ℂ)) / 2 = A * ((-t : ℝ) : ℂ) := by
      push_cast
      ring
    have hB : B * (((-2 * t - j - j : ℝ) : ℂ)) / 2 = B * ((-j - t : ℝ) : ℂ) := by
      push_cast
      ring
    unfold cosRootConvolutionEnergyKernel
    rw [hA, hB]
    push_cast
    ring
  · have he : -2 * t - j ∉ Ioi |j| := by
      exact fun hh => h ((cosRootConvolution_energy_support j t).mpr hh)
    rw [indicator_of_notMem he, mul_zero]
    by_cases ht : 0 < -t
    · have hz : ¬ 0 < -j - t := fun hz => h ⟨ht, hz⟩
      simp [cosRootConvolutionRaw, regularHalfProfile, halfProfile, hz]
    · simp [cosRootConvolutionRaw, regularHalfProfile, halfProfile, ht]

/-- Concrete pointwise convolution existence proves ordinary integrability of the raw sum. -/
theorem integrable_cosRootConvolutionRaw {a : ℝ} (ha : 0 < a) (A B : ℂ) (j : ℝ) :
    Integrable (cosRootConvolutionRaw a A B j) := by
  exact (cosRootConvolution_left_exists ha A B (-j)).integrable.add
    (cosRootConvolution_right_exists ha B (-j)).integrable

/-- The actual convolution is the ordinary integral of its combined integrable summands. -/
theorem cosRootConvolution_eq_integral_raw {a : ℝ} (ha : 0 < a) (A B : ℂ) (j : ℝ) :
    cosRootConvolution a A B (-j) = ∫ t : ℝ, cosRootConvolutionRaw a A B j t := by
  change (∫ t : ℝ, regularHalfProfile a A (-t) * halfProfile a B (-j - t)) +
    (∫ t : ℝ, halfProfile a 0 (-t) * regularHalfProfile a B (-j - t)) = _
  exact (integral_add (cosRootConvolution_left_exists ha A B (-j)).integrable
    (cosRootConvolution_right_exists ha B (-j)).integrable).symm

/-- The strict energy-threshold kernel is genuinely integrable, including the zero-spin endpoint. -/
theorem integrableOn_cosRootConvolutionEnergyKernel {a : ℝ} (ha : 0 < a)
    (A B : ℂ) (j : ℝ) :
    IntegrableOn (cosRootConvolutionEnergyKernel a A B j) (Ioi |j|) := by
  let F : ℝ → ℂ := (Ioi |j|).indicator (cosRootConvolutionEnergyKernel a A B j)
  have hi : Integrable (fun t : ℝ => (2 : ℂ) * F (-2 * t - j)) := by
    have hfn : cosRootConvolutionRaw a A B j = fun t => 2 * F (-2 * t - j) := by
      funext t
      exact cosRootConvolutionRaw_eq_energyKernel a A B j t
    rw [← hfn]
    exact integrable_cosRootConvolutionRaw ha A B j
  have hc : Integrable (fun t : ℝ => F (-2 * t - j)) :=
    (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (by norm_num : (2 : ℂ) ≠ 0)) _).mp hi
  have hs : Integrable (fun e : ℝ => F (e - j)) :=
    (integrable_comp_mul_left_iff (fun e : ℝ => F (e - j))
      (by norm_num : (-2 : ℝ) ≠ 0)).mp hc
  have hF : Integrable F := by simpa only [add_sub_cancel_right] using hs.comp_add_right j
  exact (integrable_indicator_iff measurableSet_Ioi).mp hF

/-- The reflected convolution at `-j` is exactly the literal ordinary energy integral. -/
theorem cosRootConvolution_eq_energy_integral {a : ℝ} (ha : 0 < a)
    (A B : ℂ) (j : ℝ) :
    cosRootConvolution a A B (-j) =
      ∫ e in Ioi |j|, cosRootConvolutionEnergyKernel a A B j e := by
  let F : ℝ → ℂ := (Ioi |j|).indicator (cosRootConvolutionEnergyKernel a A B j)
  rw [cosRootConvolution_eq_integral_raw ha]
  simp_rw [cosRootConvolutionRaw_eq_energyKernel]
  change (∫ t : ℝ, (2 : ℂ) * F (-2 * t - j)) = _
  rw [integral_const_mul]
  have hs : (∫ t : ℝ, F (-2 * t - j)) =
      |(-2 : ℝ)⁻¹| • ∫ e : ℝ, F (e - j) :=
    Measure.integral_comp_mul_left (fun e : ℝ => F (e - j)) (-2)
  rw [hs, integral_sub_right_eq_self]
  have hcoef (z : ℂ) : 2 * (|(-2 : ℝ)⁻¹| • z) = z := by
    norm_num [Complex.real_smul]
    ring
  rw [hcoef]
  exact integral_indicator (s := Ioi |j|) measurableSet_Ioi

/-- At zero spin the ordinary denominator is exactly the positive energy itself. -/
theorem cosRootConvolutionEnergyKernel_zero (a : ℝ) (A B : ℂ) {e : ℝ} (he : 0 < e) :
    cosRootConvolutionEnergyKernel a A B 0 e =
      Complex.exp (-(a : ℂ) * (e : ℂ)) / (e : ℂ) *
        (cosRoot (A * (e : ℂ) / 2) * cosRoot (B * (e : ℂ) / 2) - 1) := by
  simp [cosRootConvolutionEnergyKernel, Real.sqrt_sq he.le]

end GapFamily.Analytic.CosRootLaplace
