import GapFamily.Analytic.Cusp.Profile.CuspHalfLineSourceEmbedding
import GapFamily.Analytic.Cusp.Scalar.CuspConstantCoefficientPairing
import GapFamily.Analytic.Cusp.Scalar.CuspConstantResponseReciprocity

noncomputable section
namespace GapFamily.Analytic
open Set MeasureTheory

/-- The actual logarithmic constant response as a vector on the whole half-line. -/
def cuspConstantHalfLineResponse {κ : ℂ} (hκ : 0 < κ.re) : cuspHalfLineSourceHilbert :=
  (cuspConstantLogResponse_memLp hκ).toLp _

theorem cuspConstantHalfLineResponse_ae {κ : ℂ} (hκ : 0 < κ.re) :
    cuspConstantHalfLineResponse hκ =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      cuspConstantLogResponse κ := MemLp.coeFn_toLp _

theorem cuspConstantHalfLineResponse_embedding {κ : ℂ} (hκ : 0 < κ.re) :
    cuspHalfLineSourceEmbedding (cuspConstantHalfLineResponse hκ) =
      scalarCuspEmbedding (cuspConstantScalarForm hκ) := by
  apply Lp.ext
  filter_upwards [cuspHalfLineSourceValue_ae (cuspConstantHalfLineResponse hκ),
    cuspHalfLine_lift_congr_ae (cuspConstantHalfLineResponse_ae hκ),
    cuspConstantForm_embedding_ae hκ] with τ hJ heq hF
  change cuspHalfLineSourceValue (cuspConstantHalfLineResponse hκ) τ = _
  rw [hJ, heq]
  exact hF.symm

/-- The full half-line observation is an ordinary convergent integral for every source. -/
theorem cuspConstantHalfLinePairing_integrable {κ : ℂ} (hκ : 0 < κ.re)
    (F : ModularHilbert) :
    IntegrableOn (fun t : ℝ =>
      cuspConstantLogResponse κ t * cuspHalfLineSourceCoefficient F t) (Ioi 0) :=
  (cuspConstantLogResponse_memLp hκ).integrable_mul
    (Lp.memLp (cuspHalfLineSourceCoefficient F))

theorem cuspConstantScalarForm_halfLinePairing {κ : ℂ} (hκ : 0 < κ.re)
    (F : ModularHilbert) :
    inner ℂ (scalarCuspEmbedding
      (cuspConstantScalarForm (cuspPhysical_conj_re_pos hκ))) F =
      ∫ t : ℝ in Ioi 0,
        cuspConstantLogResponse κ t * cuspHalfLineSourceCoefficient F t := by
  have hm : κ ≠ -(1 / 2 : ℂ) := by intro h; subst κ; norm_num at hκ
  rw [← cuspConstantHalfLineResponse_embedding (cuspPhysical_conj_re_pos hκ),
    ← cuspHalfLineSourceCoefficient_inner_right, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [cuspConstantHalfLineResponse_ae (cuspPhysical_conj_re_pos hκ)] with t ht
  simp only [RCLike.inner_apply, starRingEnd_apply, ht, cuspConstantLogResponse_star hm,
    mul_comm]

/-- Actual constant observation of the scalar resolvent, with no source height bound. -/
theorem cuspScalarPencilSolution_constant_halfLinePairing {κ : ℂ} (hκ : 0 < κ.re)
    (F : ModularHilbert) :
    inner ℂ modularConstant
      (scalarCuspEmbedding (cuspScalarPencilSolution ((1 / 4 : ℂ) - κ ^ 2) F)) =
      ∫ t : ℝ in Ioi 0,
        cuspConstantLogResponse κ t * cuspHalfLineSourceCoefficient F t := by
  rw [cuspScalarPencilSolution_constant_reciprocity hκ F]
  exact cuspConstantScalarForm_halfLinePairing hκ F

end GapFamily.Analytic
