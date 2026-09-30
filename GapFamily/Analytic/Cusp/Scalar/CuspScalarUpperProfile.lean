import GapFamily.Analytic.Cusp.Scalar.CuspScalarUpperLift
import GapFamily.Analytic.Cusp.Threshold.CuspThresholdScalarBound

/-! Literal continuous scalar profiles of the actual Schur field on upper cusp charts. -/
noncomputable section
namespace GapFamily.Analytic.CuspScalarUpperProfile
open Set Filter MeasureTheory ModularGradient CuspHalfLineLaplace
  CuspScalarUpperCore CuspScalarUpperLift CuspThresholdScalar
  CuspThresholdGreenProfile CuspThresholdTraceScalar CuspConstrainedThreshold
open scoped Topology ContDiff

/-- The scalar trace cancellation holds for the actual ordinary upper lift,
with its constructed height absorption and without restricting horizontal position. -/
theorem upperCutoff_scalarTrace_ae_high
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ UpperHalfPlane.upperHalfPlaneSet) {L : ℝ} (hL : 0 ≤ L)
    (hAbs : (upperCutoffHilbertValueOperator χ hχ hc hs).comp (modularLowCut (Real.exp L)) =
      upperCutoffHilbertValueOperator χ hχ hc hs) :
    ∀ᵐ z : ℂ ∂volume, 1 < z.im → z.im ≤ Real.exp L →
      upperCutoffHilbertValueOperator χ hχ hc hs (thresholdScalarTrace L) z =
        χ z * (Real.sqrt z.im : ℂ) := by
  let P := upperCutoffHilbertValueOperator χ hχ hc hs
  let R := cuspConstantLocalResponse L 0
  have hpr : P (thresholdScalarTrace L) = P modularConstant + (1 / 4 : ℂ) • P R := by
    change P (modularLowCut (Real.exp L) modularConstant + (1 / 4 : ℂ) • R) = _
    rw [map_add, map_smul]
    exact congrArg (fun v => v + (1 / 4 : ℂ) • P R)
      (congrArg (fun T : ModularHilbert →L[ℂ] Lp ℂ 2 (volume : Measure ℂ) => T modularConstant) hAbs)
  have hr := upperCutoff_sourceEmbedding_toLp_ae_high χ hχ hc hs L hL
    (cuspConstantCollarResponse L 0) (cuspConstantLogResponse 0) (cuspConstantCollarResponse_apply L 0)
  filter_upwards [Lp.coeFn_add (P modularConstant) ((1 / 4 : ℂ) • P R),
    Lp.coeFn_smul (1 / 4 : ℂ) (P R), upperCutoff_constant_ae χ hχ hc hs, hr]
    with z ha hsm hq hr
  intro hy hcap
  change P (thresholdScalarTrace L) z = _
  rw [hpr, ha, Pi.add_apply, hsm, Pi.smul_apply, hq]
  have hr' : P R z = χ z * cuspConstantPhysicalResponse 0 z.im := by
    simpa only [P, R, cuspConstantLocalResponse, hcap, ite_true,
      cuspConstantPhysicalResponse, cuspLift] using hr hy
  rw [hr', smul_eq_mul]
  have hcancel := cuspConstantPhysicalResponse_zero_cancellation (by linarith : 0 < z.im)
  linear_combination χ z * hcancel

/-- The actual Green upper lift agrees with the ordinary continuous min-kernel
profile on every finite high window, including translated and seam charts. -/
theorem upperCutoff_greenOutput_ae_high
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ UpperHalfPlane.upperHalfPlaneSet) {α L T : ℝ}
    (hα : 0 < α) (hL : 0 ≤ L) (hT : 0 ≤ T) (hLT : L ≤ T) (f : HalfLineL2) :
    ∀ᵐ z : ℂ ∂volume, 1 < z.im → z.im ≤ Real.exp L →
      upperCutoffHilbertValueOperator χ hχ hc hs
        (cuspGreenWeightedLocalOutput α hα.le L T 0 f) z =
          χ z * (Real.sqrt z.im • greenProfile α f (Real.log z.im)) := by
  have h := upperCutoff_sourceEmbedding_toLp_ae_high χ hχ hc hs L hL
    (cuspGreenWeightedLocalOperator α hα.le L T 0 f) (greenProfile α f)
    (fun t => (greenProfile_eq_local hα hT hLT f t).symm)
  filter_upwards [h] with z hz
  intro hy hcap
  simpa only [cuspGreenWeightedLocalOutput, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap, hcap, ite_true] using hz hy

/-- This is the literal scalar part of the actual Schur operator upstairs,
not a newly prescribed representative or a bare kernel replacement. -/
theorem upperCutoff_scalarOutput_ae_high
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ UpperHalfPlane.upperHalfPlaneSet) {α L T : ℝ}
    (hα : 0 < α) (hL : 0 ≤ L) (hT : 0 ≤ T) (hLT : L ≤ T)
    (hAbs : (upperCutoffHilbertValueOperator χ hχ hc hs).comp (modularLowCut (Real.exp L)) =
      upperCutoffHilbertValueOperator χ hχ hc hs) (F : ModularHilbert) :
    ∀ᵐ z : ℂ ∂volume, 1 < z.im → z.im ≤ Real.exp L →
      upperCutoffHilbertValueOperator χ hχ hc hs (scalarLocalOutput α hα.le L T F) z =
        χ z * (Real.sqrt z.im • scalarProfile α hα.le F (Real.log z.im)) := by
  let P := upperCutoffHilbertValueOperator χ hχ hc hs
  let G := cuspGreenWeightedLocalOutput α hα.le L T 0 (cuspHalfLineSourceCoefficient F)
  let S := thresholdScalarTrace L
  let c := traceCoefficient α hα.le F
  have he : P (scalarLocalOutput α hα.le L T F) = P G + c • P S := by
    change P (G + c • S) = _
    rw [map_add, map_smul]
  filter_upwards [Lp.coeFn_add (P G) (c • P S), Lp.coeFn_smul c (P S),
    upperCutoff_greenOutput_ae_high χ hχ hc hs hα hL hT hLT (cuspHalfLineSourceCoefficient F),
    upperCutoff_scalarTrace_ae_high χ hχ hc hs hL hAbs] with z ha hc hg ht
  intro hy hcap
  change P (scalarLocalOutput α hα.le L T F) z = _
  rw [he, ha, Pi.add_apply, hc, Pi.smul_apply, hg hy hcap, ht hy hcap]
  simp only [scalarProfile, smul_add, Complex.real_smul, smul_eq_mul]
  ring

/-- The scalar height profile has its actual continuity throughout the upper cusp. -/
theorem continuousOn_scalarLift {α : ℝ} (hα : 0 < α) (F : ModularHilbert) :
    ContinuousOn (fun z : ℂ => Real.sqrt z.im • scalarProfile α hα.le F (Real.log z.im))
      {z : ℂ | 1 < z.im} := by
  intro z hz
  change 1 < z.im at hz
  apply ContinuousAt.continuousWithinAt
  have hy : 0 < z.im := by linarith
  have hlog : ContinuousAt (fun w : ℂ => Real.log w.im) z :=
    (Real.continuousAt_log hy.ne').comp Complex.continuous_im.continuousAt
  have hp : ContinuousAt (scalarProfile α hα.le F) (Real.log z.im) :=
    (scalarProfile_continuousOn hα F).continuousAt (isOpen_Ioi.mem_nhds (Real.log_pos hz))
  have hcomp : ContinuousAt (fun w : ℂ => scalarProfile α hα.le F (Real.log w.im)) z := hp.comp_of_eq hlog rfl
  have hsq : ContinuousAt (fun w : ℂ => Real.sqrt w.im) z :=
    Real.continuous_sqrt.continuousAt.comp Complex.continuous_im.continuousAt
  exact hsq.smul hcomp

end GapFamily.Analytic.CuspScalarUpperProfile
