import GapFamily.Analytic.Cusp.CuspLowIntegral
import GapFamily.Analytic.Cusp.CuspLowInterval
import GapFamily.Analytic.Cusp.CuspProjectedBoundary

/-!
# The lower fundamental-domain mass estimate

The actual one-dimensional estimate is integrated over the curved fibers.
All scalar integrals are integrable, and derivative energy remains inside
the fundamental domain rather than a surrounding rectangle.
-/

noncomputable section
namespace GapFamily.Analytic
open Set MeasureTheory ModularGradient UpperHalfPlane

theorem continuousOn_cuspLowValueMass (F : smoothCore) :
    ContinuousOn (fun z : ℂ =>
      ‖F.val z - cuspHorizontalAverage F.val 1‖ ^ 2 / z.im ^ 2) upperHalfPlaneSet := by
  have hc : ContinuousOn (fun z : ℂ => F.val z - cuspHorizontalAverage F.val 1)
      upperHalfPlaneSet := F.property.1.continuousOn.sub continuousOn_const
  exact (hc.norm.pow 2).div (Complex.continuous_im.continuousOn.pow 2)
    (fun _ hz => pow_ne_zero 2 (ne_of_gt hz))

theorem continuousOn_cuspLowVerticalEnergy (F : smoothCore) :
    ContinuousOn (fun z : ℂ => ‖fderiv ℝ F.val z Complex.I‖ ^ 2) upperHalfPlaneSet :=
  ((F.property.1.continuousOn_fderiv_of_isOpen isOpen_upperHalfPlaneSet (by simp)).clm_apply
    continuousOn_const).norm.pow 2

/-- The uniform weighted estimate uses each literal lower endpoint. -/
theorem cuspProjected_low_fiber_mass_le (F : smoothCore) (x : ℝ)
    (hx : x ∈ Icc (-1/2 : ℝ) (1/2)) :
    (∫ y in (cuspLowFiber x)..1,
      ‖F.val (Complex.mk x y) - cuspHorizontalAverage F.val 1‖ ^ 2 / y ^ 2) ≤
      (2 / 3 : ℝ) * ‖F.val (Complex.mk x 1) - cuspHorizontalAverage F.val 1‖ ^ 2 +
        (1 / 6 : ℝ) * (∫ y in (cuspLowFiber x)..1,
          ‖fderiv ℝ F.val (Complex.mk x y) Complex.I‖ ^ 2) := by
  have hs : Icc (cuspLowFiber x) 1 ⊆ Ioi 0 := by
    intro y hy
    exact (cuspLowFiber_pos hx).trans_le hy.1
  apply IntervalTrace.low_weighted_mass_le (cuspLowFiber_lower hx) (cuspLowFiber_le_one x)
    (((continuousOn_cuspVerticalSlice F.property.1.continuousOn x).sub
      continuousOn_const).mono hs)
    ((continuousOn_cuspVerticalDerivative F.property.1 x).mono hs)
  intro y hy
  exact (hasDerivAt_cuspVerticalSlice F.property.1 x
    ((cuspLowFiber_pos hx).trans hy.1)).sub_const (cuspHorizontalAverage F.val 1)

/-- Ordinary Fubini gives the low mass bound in the actual domain. -/
theorem cuspProjected_low_mass_le_boundary (F : smoothCore) :
    (∫ z : ℂ in cuspLowRegion,
      ‖F.val z - cuspHorizontalAverage F.val 1‖ ^ 2 / z.im ^ 2) ≤
      (2 / 3 : ℝ) * (∫ x in (-1/2 : ℝ)..(1/2),
        ‖F.val (Complex.mk x 1) - cuspHorizontalAverage F.val 1‖ ^ 2) +
      (1 / 6 : ℝ) * (∫ z : ℂ in cuspLowRegion, ‖fderiv ℝ F.val z Complex.I‖ ^ 2) := by
  have hM := cuspLow_iterated_intervalIntegrable (continuousOn_cuspLowValueMass F)
  have hE := cuspLow_iterated_intervalIntegrable (continuousOn_cuspLowVerticalEnergy F)
  have hB : IntervalIntegrable (fun x : ℝ =>
      ‖F.val (Complex.mk x 1) - cuspHorizontalAverage F.val 1‖ ^ 2)
      volume (-1/2) (1/2) := cuspResidual_boundary_integrable F
  have h := intervalIntegral.integral_mono_on (by norm_num : (-1/2 : ℝ) ≤ 1/2)
    hM ((hB.const_mul (2 / 3)).add (hE.const_mul (1 / 6)))
    (fun x hx => cuspProjected_low_fiber_mass_le F x hx)
  rw [intervalIntegral.integral_add (hB.const_mul (2 / 3)) (hE.const_mul (1 / 6)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h
  simpa only [← cuspLow_integral_eq_iterated _ (continuousOn_cuspLowValueMass F),
    ← cuspLow_integral_eq_iterated _ (continuousOn_cuspLowVerticalEnergy F)] using h

end GapFamily.Analytic
