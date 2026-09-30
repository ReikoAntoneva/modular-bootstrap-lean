import GapFamily.Analytic.Poincare.Repair.PoincareExteriorMoment
import GapFamily.Analytic.Foundation.GeometricMomentDecay

/-! Elementary short-cell bounds in the actual square-root input coordinate.
The unit-radius analytic disk has an explicit polynomial coefficient linear
in the physical band cutoff, uniformly over all physical input spins.
-/
noncomputable section
namespace GapFamily.Analytic
open Real

/-- The square-root coordinate width is at most the square root of the actual
energy width, including cells touching the physical edge. -/
theorem sqrtInputWidth_le_sqrt_sub (jin : ℤ) (L V : ℝ)
    (hL : |(jin : ℝ)| ≤ L) (hLV : L ≤ V) :
    sqrtInputWidth jin L V ≤ sqrt (V - L) := by
  have hleft := sq_sqrt (sub_nonneg.mpr hL)
  have hright := sq_sqrt (sub_nonneg.mpr (hL.trans hLV))
  have hwidth := sq_sqrt (sub_nonneg.mpr hLV)
  have hdiff := sqrtInputWidth_nonneg jin L V hLV
  have hmul := mul_nonneg (sqrt_nonneg (L - |(jin : ℝ)|)) hdiff
  have hw := sqrt_nonneg (V - L)
  dsimp [sqrtInputWidth] at hdiff hmul ⊢
  nlinarith

/-- Every physical energy cell of length at most one has square-root width at most one. -/
theorem sqrtInputWidth_le_one (jin : ℤ) (L V : ℝ)
    (hL : |(jin : ℝ)| ≤ L) (hLV : L ≤ V) (hshort : V - L ≤ 1) :
    sqrtInputWidth jin L V ≤ 1 := by
  calc
    _ ≤ sqrt (V - L) := sqrtInputWidth_le_sqrt_sub jin L V hL hLV
    _ ≤ sqrt 1 := sqrt_le_sqrt hshort
    _ = 1 := sqrt_one

/-- The literal square-root cell center is always nonnegative. -/
theorem sqrtInputCenter_nonneg (jin : ℤ) (L V : ℝ) :
    0 ≤ sqrtInputCenter jin L V := by
  unfold sqrtInputCenter
  positivity

/-- The actual center lies below the square root of the physical band cutoff. -/
theorem sqrtInputCenter_le_sqrt (jin : ℤ) (L V B : ℝ)
    (hLV : L ≤ V) (hVB : V ≤ B) :
    sqrtInputCenter jin L V ≤ sqrt B := by
  have hleft : sqrt (L - |(jin : ℝ)|) ≤ sqrt B :=
    sqrt_le_sqrt (by linarith [abs_nonneg (jin : ℝ)])
  have hright : sqrt (V - |(jin : ℝ)|) ≤ sqrt B :=
    sqrt_le_sqrt (by linarith [abs_nonneg (jin : ℝ)])
  unfold sqrtInputCenter
  linarith

/-- The actual unit-radius cell disk has an explicit strip coefficient linear
in the band cutoff, uniformly over every physical cell and input spin. -/
theorem inputColumnStripPolynomial_sqrtInputCenter_le
    (B : ℝ) (hB : 1 ≤ B) (jin : ℤ) (L V : ℝ)
    (hL : |(jin : ℝ)| ≤ L) (hLV : L ≤ V) (hVB : V ≤ B) :
    inputColumnStripPolynomial jin (|sqrtInputCenter jin L V| + 1) ≤
      (centralKernelBound + 96 * π ^ 2 + 25) * B := by
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hc0 := sqrtInputCenter_nonneg jin L V
  have hc := sqrtInputCenter_le_sqrt jin L V B hLV hVB
  have hsB : sqrt B ≤ B := sqrt_le_self_iff.mpr (Or.inr hB)
  have hcB : sqrtInputCenter jin L V ≤ B := hc.trans hsB
  have hcsq : (sqrtInputCenter jin L V) ^ 2 ≤ B := by
    simpa only [sq_sqrt hB0] using (sq_le_sq₀ hc0 (sqrt_nonneg B)).mpr hc
  have hj : |(jin : ℝ)| ≤ B := hL.trans (hLV.trans hVB)
  rw [abs_of_nonneg hc0]
  have hR : sqrtInputCenter jin L V + 1 ≤ 2 * B := by linarith
  have hRsq : (sqrtInputCenter jin L V + 1) ^ 2 ≤ 4 * B := by nlinarith
  have hcentral : centralKernelBound * |(jin : ℝ)| ≤ centralKernelBound * B :=
    mul_le_mul_of_nonneg_left hj centralKernelBound_pos.le
  have hhigh : 16 * π ^ 2 * ((sqrtInputCenter jin L V + 1) ^ 2 + 2 * |(jin : ℝ)|) ≤
      16 * π ^ 2 * (6 * B) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hrank : 12 * (sqrtInputCenter jin L V + 1) + 1 ≤ 25 * B := by linarith
  calc
    _ = (centralKernelBound * |(jin : ℝ)| +
        16 * π ^ 2 * ((sqrtInputCenter jin L V + 1) ^ 2 + 2 * |(jin : ℝ)|)) +
        (12 * (sqrtInputCenter jin L V + 1) + 1) := by
      unfold inputColumnStripPolynomial
      ring
    _ ≤ (centralKernelBound * B + 16 * π ^ 2 * (6 * B)) + 25 * B :=
      add_le_add (add_le_add hcentral hhigh) hrank
    _ = _ := by ring

/-- The unit-radius geometric ratio of a short physical cell lies in `[0,1/2]`. -/
theorem sqrtInputWidth_half_mem_Icc (jin : ℤ) (L V : ℝ)
    (hL : |(jin : ℝ)| ≤ L) (hLV : L ≤ V) (hshort : V - L ≤ 1) :
    sqrtInputWidth jin L V / 2 ∈ Set.Icc (0 : ℝ) (1 / 2) := by
  constructor
  · exact div_nonneg (sqrtInputWidth_nonneg jin L V hLV) (by norm_num)
  · exact div_le_div_of_nonneg_right (sqrtInputWidth_le_one jin L V hL hLV hshort)
      (by norm_num)

end GapFamily.Analytic
