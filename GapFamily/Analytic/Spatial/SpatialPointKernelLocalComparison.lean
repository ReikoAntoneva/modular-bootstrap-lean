import GapFamily.Analytic.Spatial.SpatialPointKernelBasic

/-! Uniform local comparison for the literal point-kernel parameter. -/
noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open Complex
open scoped ComplexConjugate

private theorem im_le_norm_sub_conj {z w : ℂ} (hw : 0 < w.im) :
    z.im ≤ ‖z - conj w‖ := by
  have h := Complex.abs_im_le_norm (z - conj w)
  simp only [Complex.sub_im, Complex.conj_im, sub_neg_eq_add] at h
  exact (le_add_of_nonneg_right hw.le).trans ((le_abs_self _).trans h)

private theorem pointParameter_le_eight_of_norm_sub_le
    {z z' w : ℂ} (hz : 0 < z.im) (hz' : 0 < z'.im) (hw : 0 < w.im)
    (hd : ‖z' - z‖ ≤ z.im) (hi : z.im ≤ 2 * z'.im) :
    pointParameter z' w ≤ 8 * pointParameter z w := by
  have hn : ‖z' - conj w‖ ≤ 2 * ‖z - conj w‖ := by
    calc
      _ = ‖(z' - z) + (z - conj w)‖ := by congr 1; ring
      _ ≤ ‖z' - z‖ + ‖z - conj w‖ := norm_add_le _ _
      _ ≤ _ := by linarith [im_le_norm_sub_conj (z := z) hw]
  have hs : Complex.normSq (z' - conj w) ≤ 4 * Complex.normSq (z - conj w) := by
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg (z' - conj w), norm_nonneg (z - conj w)]
  have hp : Complex.normSq (z' - conj w) * z.im ≤
      (8 * Complex.normSq (z - conj w)) * z'.im := by
    calc
      _ ≤ (4 * Complex.normSq (z - conj w)) * (2 * z'.im) :=
        mul_le_mul hs hi hz.le (mul_nonneg (by norm_num) (Complex.normSq_nonneg _))
      _ = _ := by ring
  rw [pointParameter_eq_normSq_sub_conj hz' hw,
    pointParameter_eq_normSq_sub_conj hz hw, ← mul_div_assoc]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hp (show 0 ≤ 4 * w.im by positivity)]

/-- One radius tied only to the first height compares q uniformly in the other point. -/
theorem pointParameter_local_comparison {z z' w : ℂ}
    (hz : 0 < z.im) (hz' : 0 < z'.im) (hw : 0 < w.im)
    (hd : ‖z' - z‖ ≤ z.im / 2) :
    pointParameter z' w ≤ 8 * pointParameter z w ∧
      pointParameter z w ≤ 8 * pointParameter z' w := by
  have him : |z'.im - z.im| ≤ z.im / 2 := by
    simpa only [Complex.sub_im] using (Complex.abs_im_le_norm (z' - z)).trans hd
  have hlo := (abs_le.mp him).1
  have hhi := (abs_le.mp him).2
  constructor
  · exact pointParameter_le_eight_of_norm_sub_le hz hz' hw
      (hd.trans (by linarith)) (by linarith)
  · apply pointParameter_le_eight_of_norm_sub_le hz' hz hw
    · rw [norm_sub_rev]
      exact hd.trans (by linarith)
    · linarith

/-- Comparing the second point uses the actual symmetry of q, with no group input. -/
theorem pointParameter_local_comparison_right {z w w' : ℂ}
    (hz : 0 < z.im) (hw : 0 < w.im) (hw' : 0 < w'.im)
    (hd : ‖w' - w‖ ≤ w.im / 2) :
    pointParameter z w' ≤ 8 * pointParameter z w ∧
      pointParameter z w ≤ 8 * pointParameter z w' := by
  simpa only [pointParameter_symm w' z, pointParameter_symm w z] using
    pointParameter_local_comparison hw hw' hz hd

end GapFamily.Analytic.SpatialPoint
