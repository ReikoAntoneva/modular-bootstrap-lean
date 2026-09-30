import GapFamily.Analytic.Cusp.Green.CuspGreenCoefficient
import GapFamily.Analytic.Cusp.Green.CuspGreenHeightSupport
import GapFamily.Analytic.Cusp.Green.CuspGreenSourceRepresentative
import GapFamily.Analytic.Cusp.Scalar.CuspConstantResponseForm

noncomputable section
namespace GapFamily.Analytic
open Set MeasureTheory ModularGradient

private theorem constant_profile_continuous {κ : ℂ} (hκ : 0 < κ.re) :
    Continuous (cuspConstantLogResponse κ) := by
  have hm : κ ≠ -(1 / 2 : ℂ) := by
    intro h
    subst κ
    norm_num at hκ
  exact (cuspConstantLogResponse_contDiff hm).continuous

private theorem constant_conj_re_pos {κ : ℂ} (hκ : 0 < κ.re) :
    0 < (star κ).re := by
  simpa only [Complex.star_def, Complex.conj_re] using hκ

/-- The actual collar lift of the constant response is its genuine low-height cutoff. -/
theorem cuspConstant_sourceEmbedding_eq_lowCut {T : ℝ} (hT : 0 ≤ T)
    {κ : ℂ} (hκ : 0 < κ.re) :
    cuspGreenSourceEmbedding T
      (cuspGreenCollarSource 0 T (cuspConstantLogResponse κ) (constant_profile_continuous hκ)) =
      modularLowCut (Real.exp T) (scalarCuspEmbedding (cuspConstantScalarForm hκ)) := by
  have hrep : scalarCuspEmbedding (cuspConstantScalarForm hκ) =ᵐ[modularMeasure]
      (fun τ : UpperHalfPlane => if 1 < τ.im then cuspConstantPhysicalResponse κ τ.im else 0) :=
    cuspConstantForm_embedding_ae hκ
  apply Lp.ext
  filter_upwards [cuspGreenSourceEmbedding_continuous_ae T hT (cuspConstantLogResponse κ)
      (constant_profile_continuous hκ),
    modularLowCut_ae (Real.exp T) (scalarCuspEmbedding (cuspConstantScalarForm hκ)), hrep]
    with τ hJ hcut hvalue
  rw [hJ, hcut, Set.indicator_apply]
  simp only [Set.mem_ofPred_eq, hvalue]
  by_cases hy : 1 < τ.im <;> by_cases hTτ : τ.im ≤ Real.exp T <;>
    simp [hy, hTτ, cuspConstantPhysicalResponse]

theorem cuspConstantLogResponse_star {κ : ℂ}
    (hm : κ ≠ -(1 / 2 : ℂ)) (t : ℝ) :
    star (cuspConstantLogResponse (star κ) t) = cuspConstantLogResponse κ t := by
  by_cases hp : κ = (1 / 2 : ℂ)
  · subst κ
    have hh : star (1 / 2 : ℂ) = (1 / 2 : ℂ) := by norm_num
    simp only [hh, cuspConstantLogResponse_half]
    simp [← Complex.exp_conj, map_ofNat]
  · have hmp : star κ ≠ -(1 / 2 : ℂ) := by
      intro h
      apply hm
      simpa using congrArg star h
    have hpp : star κ ≠ (1 / 2 : ℂ) := by
      intro h
      apply hp
      simpa using congrArg star h
    rw [cuspConstantLogResponse_eq_quotient hpp hmp,
      cuspConstantLogResponse_eq_quotient hp hm]
    simp [← Complex.exp_conj, map_ofNat]

/-- The actual coefficient integrand is ordinarily integrable on the finite collar. -/
theorem cuspConstantCoefficient_integrable (T : ℝ) {κ : ℂ} (hκ : 0 < κ.re)
    (F : ModularHilbert) :
    Integrable (fun u : CuspGreenCollar 0 T =>
      cuspConstantLogResponse κ u * (cuspGreenSourceCoefficient T F) u)
      (cuspGreenCollarMeasure 0 T) := by
  have hm : κ ≠ -(1 / 2 : ℂ) := by intro h; subst κ; norm_num at hκ
  have hi := (cuspGreenCollarSource_inner_integral T (cuspConstantLogResponse (star κ))
    (constant_profile_continuous (constant_conj_re_pos hκ)) (cuspGreenSourceCoefficient T F)).1
  simpa only [RCLike.inner_apply, starRingEnd_apply, cuspConstantLogResponse_star hm, mul_comm] using hi

/-- The actual constant-response test pairing of a height-supported source is
the ordinary coefficient integral, including the removable physical parameter. -/
theorem cuspConstantScalarForm_coefficient_pairing {T : ℝ} (hT : 0 ≤ T)
    {κ : ℂ} (hκ : 0 < κ.re) (F : ModularHilbert)
    (hF : modularHighCut (Real.exp T) F = 0) :
    inner ℂ (scalarCuspEmbedding
      (cuspConstantScalarForm (constant_conj_re_pos hκ))) F =
      ∫ u : CuspGreenCollar 0 T,
        cuspConstantLogResponse κ u * (cuspGreenSourceCoefficient T F) u
          ∂cuspGreenCollarMeasure 0 T := by
  have hm : κ ≠ -(1 / 2 : ℂ) := by intro h; subst κ; norm_num at hκ
  let hc : 0 < (star κ).re := constant_conj_re_pos hκ
  calc
    _ = inner ℂ (modularLowCut (Real.exp T)
        (scalarCuspEmbedding (cuspConstantScalarForm hc))) F :=
      (modularLowCut_inner_of_highCut_zero (Real.exp T) F _ hF).symm
    _ = inner ℂ (cuspGreenSourceEmbedding T
        (cuspGreenCollarSource 0 T (cuspConstantLogResponse (star κ))
          (constant_profile_continuous hc))) F := by
      rw [cuspConstant_sourceEmbedding_eq_lowCut hT hc]
    _ = inner ℂ (cuspGreenCollarSource 0 T (cuspConstantLogResponse (star κ))
        (constant_profile_continuous hc)) (cuspGreenSourceCoefficient T F) :=
      (cuspGreenSourceCoefficient_inner_right T _ F).symm
    _ = _ := by
      simpa only [RCLike.inner_apply, starRingEnd_apply, cuspConstantLogResponse_star hm, mul_comm] using
        (cuspGreenCollarSource_inner_integral T (cuspConstantLogResponse (star κ))
          (constant_profile_continuous hc) (cuspGreenSourceCoefficient T F)).2


end GapFamily.Analytic
