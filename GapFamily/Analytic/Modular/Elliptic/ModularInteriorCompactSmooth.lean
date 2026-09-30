import GapFamily.Analytic.Modular.ModularGradientCore

/-!
# Smooth interior cutoff of the actual modular core

An interior cutoff turns a genuine smooth automorphic core function into a
globally smooth compactly supported function on the Euclidean plane.  The
derivative formulas remain valid even away from the upper half-plane, since
the cutoff vanishes on a neighborhood there.
-/

noncomputable section

namespace GapFamily.Analytic.ModularGradient

open Set MeasureTheory UpperHalfPlane
open scoped ContDiff

/-- The two real coordinate directions control the full operator norm. -/
theorem complex_real_opNorm_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : ℂ →L[ℝ] E) : ‖L‖ ≤ ‖L 1‖ + ‖L Complex.I‖ := by
  apply L.opNorm_le_bound (add_nonneg (norm_nonneg _) (norm_nonneg _))
  intro z
  have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    simpa only [Complex.real_smul, mul_one] using (Complex.re_add_im z).symm
  calc
    ‖L z‖ = ‖z.re • L 1 + z.im • L Complex.I‖ := by
      conv_lhs => rw [hz]
      rw [map_add, map_smul, map_smul]
    _ ≤ ‖z.re • L 1‖ + ‖z.im • L Complex.I‖ := norm_add_le _ _
    _ = |z.re| * ‖L 1‖ + |z.im| * ‖L Complex.I‖ := by
      simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ ‖z‖ * ‖L 1‖ + ‖z‖ * ‖L Complex.I‖ :=
      add_le_add
        (mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm z) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm z) (norm_nonneg _))
    _ = (‖L 1‖ + ‖L Complex.I‖) * ‖z‖ := by ring

/-- A smooth interior cutoff produces a globally smooth Euclidean function. -/
theorem cutoff_contDiff {χ : ℂ → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hs : tsupport χ ⊆ modularInterior) (F : smoothCore) :
    ContDiff ℝ ∞ (fun z => χ z * F.val z) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ tsupport χ
  · exact hχ.contDiffAt.mul (F.property.1.contDiffAt
      (isOpen_upperHalfPlaneSet.mem_nhds (im_pos_of_mem_modularInterior (hs hz))))
  · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hz] with w hw
    simp [hw]

/-- Multiplication cannot enlarge the support of an interior cutoff. -/
theorem cutoff_tsupport_subset (χ : ℂ → ℂ) (F : smoothCore) :
    tsupport (fun z => χ z * F.val z) ⊆ tsupport χ :=
  tsupport_mul_subset_left

theorem cutoff_hasCompactSupport {χ : ℂ → ℂ} (hc : HasCompactSupport χ)
    (F : smoothCore) : HasCompactSupport (fun z => χ z * F.val z) :=
  hc.mul_right

/-- The product rule holds globally, including where the raw core function is
not required to be smooth: both the cutoff and its derivative vanish there. -/
theorem cutoff_fderiv {χ : ℂ → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hs : tsupport χ ⊆ modularInterior) (F : smoothCore) (z : ℂ) :
    fderiv ℝ (fun w => χ w * F.val w) z =
      χ z • fderiv ℝ F.val z + F.val z • fderiv ℝ χ z := by
  by_cases hz : z ∈ tsupport χ
  · apply fderiv_fun_mul (hχ.differentiable (by simp) z)
    exact smooth_differentiableAt F.property.1
      ⟨z, im_pos_of_mem_modularInterior (hs hz)⟩
  · have hp : z ∉ tsupport (fun w => χ w * F.val w) :=
      fun h => hz (cutoff_tsupport_subset χ F h)
    rw [fderiv_of_notMem_tsupport ℝ hp, fderiv_of_notMem_tsupport ℝ hz,
      image_eq_zero_of_notMem_tsupport hz]
    simp

theorem cutoff_fderiv_apply {χ : ℂ → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hs : tsupport χ ⊆ modularInterior) (F : smoothCore) (z v : ℂ) :
    fderiv ℝ (fun w => χ w * F.val w) z v =
      fderiv ℝ χ z v * F.val z + χ z * fderiv ℝ F.val z v := by
  rw [cutoff_fderiv hχ hs]
  simp [mul_comm, add_comm]

theorem cutoff_tsupport_fderiv_subset (χ : ℂ → ℂ) (F : smoothCore) :
    tsupport (fderiv ℝ (fun z => χ z * F.val z)) ⊆ tsupport χ :=
  (tsupport_fderiv_subset ℝ).trans (cutoff_tsupport_subset χ F)

/-- The elementary product estimate, using operator norms of both derivatives. -/
theorem cutoff_norm_fderiv_le_opNorm {χ : ℂ → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hs : tsupport χ ⊆ modularInterior) (F : smoothCore) (z : ℂ) :
    ‖fderiv ℝ (fun w => χ w * F.val w) z‖ ≤
      ‖fderiv ℝ χ z‖ * ‖F.val z‖ + ‖χ z‖ * ‖fderiv ℝ F.val z‖ := by
  rw [cutoff_fderiv hχ hs]
  calc
    ‖χ z • fderiv ℝ F.val z + F.val z • fderiv ℝ χ z‖ ≤
        ‖χ z • fderiv ℝ F.val z‖ + ‖F.val z • fderiv ℝ χ z‖ := norm_add_le _ _
    _ = _ := by simp only [norm_smul]; ring

/-- The cutoff derivative is controlled by its own derivative and the two
actual Euclidean directional derivatives of the smooth modular core. -/
theorem cutoff_norm_fderiv_le {χ : ℂ → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hs : tsupport χ ⊆ modularInterior) (F : smoothCore) (z : ℂ) :
    ‖fderiv ℝ (fun w => χ w * F.val w) z‖ ≤
      ‖fderiv ℝ χ z‖ * ‖F.val z‖ +
        ‖χ z‖ * (‖fderiv ℝ F.val z 1‖ + ‖fderiv ℝ F.val z Complex.I‖) :=
  (cutoff_norm_fderiv_le_opNorm hχ hs F z).trans
    (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (complex_real_opNorm_le _) (norm_nonneg _)))

/-- A squared version convenient for direct Lebesgue energy bounds. -/
theorem cutoff_norm_fderiv_sq_le {χ : ℂ → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hs : tsupport χ ⊆ modularInterior) (F : smoothCore) (z : ℂ) :
    ‖fderiv ℝ (fun w => χ w * F.val w) z‖ ^ 2 ≤
      2 * ‖fderiv ℝ χ z‖ ^ 2 * ‖F.val z‖ ^ 2 +
        4 * ‖χ z‖ ^ 2 * (‖fderiv ℝ F.val z 1‖ ^ 2 +
          ‖fderiv ℝ F.val z Complex.I‖ ^ 2) := by
  have h := cutoff_norm_fderiv_le hχ hs F z
  have hsquare := mul_self_le_mul_self (norm_nonneg _) h
  nlinarith [sq_nonneg (‖fderiv ℝ χ z‖ * ‖F.val z‖ -
      ‖χ z‖ * (‖fderiv ℝ F.val z 1‖ + ‖fderiv ℝ F.val z Complex.I‖)),
    mul_nonneg (sq_nonneg ‖χ z‖)
      (sq_nonneg (‖fderiv ℝ F.val z 1‖ - ‖fderiv ℝ F.val z Complex.I‖))]

end GapFamily.Analytic.ModularGradient
