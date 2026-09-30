import GapFamily.Analytic.Foundation.IntervalTrace
import GapFamily.Analytic.Cusp.Fourier.CuspHorizontalSlice

/-!
# Local vertical trace estimates for the actual smooth modular core

A vertical segment between heights one and one plus a positive width lies
inside the upper half-plane. The ordinary vertical derivative is the real
Fréchet derivative in direction `I`, and the local interval estimates apply
without prescribing any behavior below the real axis.
-/

noncomputable section

namespace GapFamily.Analytic

open Set MeasureTheory UpperHalfPlane ModularGradient
open scoped ContDiff

/-- A vertical slice is continuous at all positive heights. -/
theorem continuousOn_cuspVerticalSlice {F : ℂ → ℂ}
    (hF : ContinuousOn F upperHalfPlaneSet) (x : ℝ) :
    ContinuousOn (fun y : ℝ => F (Complex.mk x y)) (Ioi 0) := by
  have hline : Continuous (fun y : ℝ => Complex.mk x y) := by
    simp only [cuspPoint_eq]
    fun_prop
  exact hF.comp hline.continuousOn (fun _ hy => hy)

/-- The actual vertical directional derivative is continuous at positive heights. -/
theorem continuousOn_cuspVerticalDerivative {F : ℂ → ℂ}
    (hF : ContDiffOn ℝ ∞ F upperHalfPlaneSet) (x : ℝ) :
    ContinuousOn (fun y : ℝ => fderiv ℝ F (Complex.mk x y) Complex.I) (Ioi 0) := by
  have hD := hF.continuousOn_fderiv_of_isOpen isOpen_upperHalfPlaneSet (by simp)
  have hline : Continuous (fun y : ℝ => Complex.mk x y) := by
    simp only [cuspPoint_eq]
    fun_prop
  exact (hD.comp hline.continuousOn (fun _ hy => hy)).clm_apply continuousOn_const

/-- The vertical derivative is exactly evaluation of the real Fréchet derivative on `I`. -/
theorem hasDerivAt_cuspVerticalSlice {F : ℂ → ℂ}
    (hF : ContDiffOn ℝ ∞ F upperHalfPlaneSet) (x : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => F (Complex.mk x t))
      (fderiv ℝ F (Complex.mk x y) Complex.I) y := by
  have hline : HasDerivAt (fun t : ℝ => Complex.mk x t) Complex.I y := by
    simpa [cuspPoint_eq] using
      ((Complex.ofRealCLM.hasFDerivAt (x := y)).hasDerivAt.mul_const Complex.I).const_add (x : ℂ)
  have hpoint := (hF.contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds
    (show (Complex.mk x y) ∈ upperHalfPlaneSet from hy))).differentiableAt (by simp)
  exact hpoint.hasFDerivAt.comp_hasDerivAt y hline

/-- The literal height-one trace is controlled by mass and vertical derivative
energy on a collar of width `ε`. All interval integrands are continuous there. -/
theorem cusp_vertical_trace_sq_le (F : smoothCore) (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ‖F.val (Complex.mk x 1)‖ ^ 2 ≤
      (2 / ε) * (∫ y in (1 : ℝ)..(1 + ε), ‖F.val (Complex.mk x y)‖ ^ 2) +
      2 * ε * (∫ y in (1 : ℝ)..(1 + ε),
        ‖fderiv ℝ F.val (Complex.mk x y) Complex.I‖ ^ 2) := by
  have hsub : Icc (1 : ℝ) (1 + ε) ⊆ Ioi 0 := by
    intro y hy
    exact lt_of_lt_of_le zero_lt_one hy.1
  have h := IntervalTrace.left_norm_sq_le (g := fun y => F.val (Complex.mk x y))
    (g' := fun y => fderiv ℝ F.val (Complex.mk x y) Complex.I)
    (show (1 : ℝ) < 1 + ε by linarith)
    ((continuousOn_cuspVerticalSlice F.property.1.continuousOn x).mono hsub)
    ((continuousOn_cuspVerticalDerivative F.property.1 x).mono hsub)
    (fun y hy => hasDerivAt_cuspVerticalSlice F.property.1 x (by linarith [hy.1]))
  simpa only [add_sub_cancel_left] using h

/-- The height-one trace differs from the normalized ordinary collar average
by at most width times the actual vertical derivative energy. -/
theorem cusp_vertical_mean_error_sq_le (F : smoothCore) (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ‖F.val (Complex.mk x 1) -
      ε⁻¹ • (∫ y in (1 : ℝ)..(1 + ε), F.val (Complex.mk x y))‖ ^ 2 ≤
      ε * (∫ y in (1 : ℝ)..(1 + ε),
        ‖fderiv ℝ F.val (Complex.mk x y) Complex.I‖ ^ 2) := by
  have hsub : Icc (1 : ℝ) (1 + ε) ⊆ Ioi 0 := by
    intro y hy
    exact lt_of_lt_of_le zero_lt_one hy.1
  have h := IntervalTrace.left_sub_mean_sq_le (g := fun y => F.val (Complex.mk x y))
    (g' := fun y => fderiv ℝ F.val (Complex.mk x y) Complex.I)
    (show (1 : ℝ) < 1 + ε by linarith)
    ((continuousOn_cuspVerticalSlice F.property.1.continuousOn x).mono hsub)
    ((continuousOn_cuspVerticalDerivative F.property.1 x).mono hsub)
    (fun y hy => hasDerivAt_cuspVerticalSlice F.property.1 x (by linarith [hy.1]))
  simpa only [add_sub_cancel_left] using h

end GapFamily.Analytic
