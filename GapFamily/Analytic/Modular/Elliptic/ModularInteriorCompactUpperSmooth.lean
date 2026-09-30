import GapFamily.Analytic.Modular.Elliptic.ModularInteriorCompactSmooth

/-!
# Smooth cutoff estimates throughout the upper half-plane

These Euclidean cutoff estimates require support only in the upper half-plane,
so they also apply to cutoffs meeting identified edges of the modular domain.
No seam change of variables or energy transport is asserted here.
-/

noncomputable section

namespace GapFamily.Analytic.ModularGradient

open Set MeasureTheory UpperHalfPlane
open scoped ContDiff

/-- A cutoff supported anywhere in the upper half-plane gives a globally
smooth Euclidean function when multiplied by an actual smooth core function. -/
theorem upperCutoff_contDiff {χ : ℂ → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet) (F : smoothCore) :
    ContDiff ℝ ∞ (fun z => χ z * F.val z) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ tsupport χ
  · exact hχ.contDiffAt.mul (F.property.1.contDiffAt
      (isOpen_upperHalfPlaneSet.mem_nhds (hs hz)))
  · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hz] with w hw
    simp [hw]

/-- The literal product rule remains valid globally, since the cutoff and
its derivative vanish off the upper half-plane. -/
theorem upperCutoff_fderiv {χ : ℂ → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet) (F : smoothCore) (z : ℂ) :
    fderiv ℝ (fun w => χ w * F.val w) z =
      χ z • fderiv ℝ F.val z + F.val z • fderiv ℝ χ z := by
  by_cases hz : z ∈ tsupport χ
  · apply fderiv_fun_mul (hχ.differentiable (by simp) z)
    exact smooth_differentiableAt F.property.1 ⟨z, hs hz⟩
  · have hp : z ∉ tsupport (fun w => χ w * F.val w) :=
      fun h => hz (cutoff_tsupport_subset χ F h)
    rw [fderiv_of_notMem_tsupport ℝ hp, fderiv_of_notMem_tsupport ℝ hz,
      image_eq_zero_of_notMem_tsupport hz]
    simp

theorem upperCutoff_fderiv_apply {χ : ℂ → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet) (F : smoothCore) (z v : ℂ) :
    fderiv ℝ (fun w => χ w * F.val w) z v =
      fderiv ℝ χ z v * F.val z + χ z * fderiv ℝ F.val z v := by
  rw [upperCutoff_fderiv hχ hs]
  simp [mul_comm, add_comm]

theorem upperCutoff_norm_fderiv_le_opNorm {χ : ℂ → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet) (F : smoothCore) (z : ℂ) :
    ‖fderiv ℝ (fun w => χ w * F.val w) z‖ ≤
      ‖fderiv ℝ χ z‖ * ‖F.val z‖ + ‖χ z‖ * ‖fderiv ℝ F.val z‖ := by
  rw [upperCutoff_fderiv hχ hs]
  calc
    ‖χ z • fderiv ℝ F.val z + F.val z • fderiv ℝ χ z‖ ≤
        ‖χ z • fderiv ℝ F.val z‖ + ‖F.val z • fderiv ℝ χ z‖ := norm_add_le _ _
    _ = _ := by simp only [norm_smul]; ring

/-- The full real derivative is controlled by the two coordinate directions. -/
theorem upperCutoff_norm_fderiv_le {χ : ℂ → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet) (F : smoothCore) (z : ℂ) :
    ‖fderiv ℝ (fun w => χ w * F.val w) z‖ ≤
      ‖fderiv ℝ χ z‖ * ‖F.val z‖ +
        ‖χ z‖ * (‖fderiv ℝ F.val z 1‖ + ‖fderiv ℝ F.val z Complex.I‖) :=
  (upperCutoff_norm_fderiv_le_opNorm hχ hs F z).trans
    (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (complex_real_opNorm_le _) (norm_nonneg _)))

/-- The squared derivative estimate is available also across identified
edges; its subsequent energy transport is a separate assertion. -/
theorem upperCutoff_norm_fderiv_sq_le {χ : ℂ → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet) (F : smoothCore) (z : ℂ) :
    ‖fderiv ℝ (fun w => χ w * F.val w) z‖ ^ 2 ≤
      2 * ‖fderiv ℝ χ z‖ ^ 2 * ‖F.val z‖ ^ 2 +
        4 * ‖χ z‖ ^ 2 * (‖fderiv ℝ F.val z 1‖ ^ 2 +
          ‖fderiv ℝ F.val z Complex.I‖ ^ 2) := by
  have h := upperCutoff_norm_fderiv_le hχ hs F z
  have hsquare := mul_self_le_mul_self (norm_nonneg _) h
  nlinarith [sq_nonneg (‖fderiv ℝ χ z‖ * ‖F.val z‖ -
      ‖χ z‖ * (‖fderiv ℝ F.val z 1‖ + ‖fderiv ℝ F.val z Complex.I‖)),
    mul_nonneg (sq_nonneg ‖χ z‖)
      (sq_nonneg (‖fderiv ℝ F.val z 1‖ - ‖fderiv ℝ F.val z Complex.I‖))]

end GapFamily.Analytic.ModularGradient
