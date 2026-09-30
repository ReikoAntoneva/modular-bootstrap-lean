import GapFamily.Analytic.Cusp.Threshold.CuspThresholdGreenBound
import GapFamily.Analytic.Cusp.Threshold.CuspThresholdGreenOutput
import GapFamily.Analytic.Cusp.Threshold.CuspThresholdTraceScalar
import GapFamily.Analytic.Cusp.Threshold.CuspConstrainedThreshold

/-! The bounded scalar component of the actual weighted threshold Schur response. -/
noncomputable section
namespace GapFamily.Analytic.CuspThresholdScalar
open Set MeasureTheory CuspHalfLineLaplace CuspThresholdGreenProfile
  CuspThresholdGreenOutput CuspThresholdTraceScalar CuspConstrainedThreshold

/-- The literal scalar Schur profile after the actual threshold trace cancellation. -/
def scalarProfile (α : ℝ) (hα : 0 ≤ α) (F : ModularHilbert) (t : ℝ) : ℂ :=
  greenProfile α (cuspHalfLineSourceCoefficient F) t + traceCoefficient α hα F

/-- The actual two scalar summands of the finite-height weighted Schur operator. -/
def scalarLocalOutput (α : ℝ) (hα : 0 ≤ α) (L T : ℝ) :
    ModularHilbert →L[ℂ] ModularHilbert :=
  (cuspGreenWeightedLocalOutput α hα L T 0).comp cuspHalfLineSourceCoefficient +
    (traceCoefficient α hα).smulRight (thresholdScalarTrace L)

/-- The full finite-height Schur value retains its genuine constrained form coordinate. -/
theorem continuedLocalSchur_eq_constrained_add_scalar (α : ℝ) (hα : 0 ≤ α)
    (L T : ℝ) (F : ModularHilbert) :
    CuspSchurWeighted.continuedLocalSchur α hα L T 0 F =
      modularLowCut (Real.exp L) (meanZeroCuspEmbedding (constrainedForm α hα F)) +
        scalarLocalOutput α hα L T F := by
  rw [continuedLocalSchur_threshold_split]
  simp only [scalarLocalOutput, add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply, thresholdScalarTrace, add_assoc]

/-- Every scalar output collar has the same literal lifted profile above height one. -/
theorem scalarLocalOutput_ae_cusp {α L T : ℝ} (hα : 0 < α)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hLT : L ≤ T) (F : ModularHilbert) :
    ∀ᵐ τ : UpperHalfPlane ∂modularMeasure, 1 < τ.im → τ.im ≤ Real.exp L →
      scalarLocalOutput α hα.le L T F τ =
        Real.sqrt τ.im • scalarProfile α hα.le F (Real.log τ.im) := by
  let G := cuspGreenWeightedLocalOutput α hα.le L T 0 (cuspHalfLineSourceCoefficient F)
  let S := thresholdScalarTrace L
  let c := traceCoefficient α hα.le F
  filter_upwards [Lp.coeFn_add G (c • S), Lp.coeFn_smul c S,
    cuspGreenWeightedLocalOutput_zero_ae hα hL hT hLT (cuspHalfLineSourceCoefficient F),
    thresholdScalarTrace_ae_cusp hL] with τ ha hc hg hs
  intro hy hcap
  change (G + c • S) τ = _
  rw [ha, Pi.add_apply, hc, Pi.smul_apply]
  change G τ + c • S τ = _
  have hG : G τ = Real.sqrt τ.im • greenProfile α (cuspHalfLineSourceCoefficient F)
      (Real.log τ.im) := by
    simpa only [G, hy, hcap, and_self, ite_true, greenProfile, cuspGreen_zero, sub_zero] using hg
  rw [hG, show S τ = (Real.sqrt τ.im : ℂ) from hs hy hcap]
  simp only [scalarProfile, smul_add, Complex.real_smul, smul_eq_mul]
  ring

/-- One constant controls the genuine scalar profile at all nonnegative logarithmic heights. -/
theorem scalarProfile_norm_le {α t : ℝ} (hα : 0 < α) (ht : 0 ≤ t) (F : ModularHilbert) :
    ‖scalarProfile α hα.le F t‖ ≤
      (((2 / α) * ‖exponential ((α / 2 : ℝ) : ℂ)‖) + ‖traceCoefficient α hα.le‖) * ‖F‖ := by
  calc
    _ ≤ ‖greenProfile α (cuspHalfLineSourceCoefficient F) t‖ + ‖traceCoefficient α hα.le F‖ :=
      norm_add_le _ _
    _ ≤ ((2 / α) * ‖exponential ((α / 2 : ℝ) : ℂ)‖) * ‖F‖ +
        ‖traceCoefficient α hα.le‖ * ‖F‖ := by
      apply add_le_add
      · exact (greenProfile_norm_le hα ht _).trans
          (mul_le_mul_of_nonneg_left (cuspHalfLineSourceCoefficient_norm_le F) (by positivity))
      · exact (traceCoefficient α hα.le).le_opNorm F
    _ = _ := (add_mul _ _ _).symm

/-- This is a physical square-root-height bound for the scalar component, uniform in height. -/
theorem scalarProfile_lift_norm_le {α y : ℝ} (hα : 0 < α) (hy : 1 ≤ y)
    (F : ModularHilbert) :
    ‖Real.sqrt y • scalarProfile α hα.le F (Real.log y)‖ ≤
      ((((2 / α) * ‖exponential ((α / 2 : ℝ) : ℂ)‖) + ‖traceCoefficient α hα.le‖) * ‖F‖) *
        Real.sqrt y := by
  rw [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg y)]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left
    (scalarProfile_norm_le hα (Real.log_nonneg hy) F) (Real.sqrt_nonneg y)

/-- The actual scalar profile is continuous at every positive logarithmic height. -/
theorem scalarProfile_continuousOn {α : ℝ} (hα : 0 < α) (F : ModularHilbert) :
    ContinuousOn (scalarProfile α hα.le F) (Ioi 0) :=
  (greenProfile_continuousOn hα _).add continuousOn_const

/-- The bound applies to the actual scalar modular output, not just an auxiliary integral. -/
theorem scalarLocalOutput_norm_ae_cusp {α L T : ℝ} (hα : 0 < α)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hLT : L ≤ T) (F : ModularHilbert) :
    ∀ᵐ τ : UpperHalfPlane ∂modularMeasure, 1 < τ.im → τ.im ≤ Real.exp L →
      ‖scalarLocalOutput α hα.le L T F τ‖ ≤
        ((((2 / α) * ‖exponential ((α / 2 : ℝ) : ℂ)‖) + ‖traceCoefficient α hα.le‖) * ‖F‖) *
          Real.sqrt τ.im := by
  filter_upwards [scalarLocalOutput_ae_cusp hα hL hT hLT F] with τ hτ
  intro hy hcap
  rw [hτ hy hcap]
  exact scalarProfile_lift_norm_le hα hy.le F

/-- On each actual cusp output window the full Schur field has its constrained
coordinate plus the proved, uniformly bounded scalar logarithmic profile. -/
theorem continuedLocalSchur_ae_cusp {α L T : ℝ} (hα : 0 < α)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hLT : L ≤ T) (F : ModularHilbert) :
    ∀ᵐ τ : UpperHalfPlane ∂modularMeasure, 1 < τ.im → τ.im ≤ Real.exp L →
      CuspSchurWeighted.continuedLocalSchur α hα.le L T 0 F τ =
        meanZeroCuspEmbedding (constrainedForm α hα.le F) τ +
          Real.sqrt τ.im • scalarProfile α hα.le F (Real.log τ.im) := by
  let u := meanZeroCuspEmbedding (constrainedForm α hα.le F)
  filter_upwards [Lp.coeFn_add (modularLowCut (Real.exp L) u) (scalarLocalOutput α hα.le L T F),
    modularLowCut_ae (Real.exp L) u,
    scalarLocalOutput_ae_cusp hα hL hT hLT F] with τ ha hu hs
  intro hy hcap
  rw [continuedLocalSchur_eq_constrained_add_scalar]
  change (modularLowCut (Real.exp L) u + scalarLocalOutput α hα.le L T F) τ = _
  rw [ha, Pi.add_apply, hu, hs hy hcap]
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, hcap, ite_true]
  rfl

end GapFamily.Analytic.CuspThresholdScalar
