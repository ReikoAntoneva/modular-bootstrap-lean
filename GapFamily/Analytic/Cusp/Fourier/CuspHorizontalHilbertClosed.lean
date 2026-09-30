import GapFamily.Analytic.Cusp.Fourier.CuspHorizontalHilbert
import GapFamily.Analytic.Modular.Elliptic.ModularInteriorCompactCore

/-!
# Horizontal cusp tails on the completed modular form domain

The actual bounded residual operator turns the core tail estimate into a
closed inequality on the gradient graph. It therefore holds on its genuine
closure, and supplies a norm-small tail map on the complete form domain.
-/

noncomputable section
namespace GapFamily.Analytic

open Set MeasureTheory ModularGradient

/-- The actual bounded high-cusp nonconstant-mode map on the complete form domain. -/
def cuspFormResidual (H : ℝ) (hH : 1 ≤ H) : FormDomain →L[ℂ] cuspHilbert H :=
  ((cuspResidual H hH).comp (cuspRestrict H)).comp formEmbedding

/-- The core estimate extends along the proved dense graph core. -/
theorem cuspFormResidual_energy_bound (H : ℝ) (hH : 1 ≤ H) (u : FormDomain) :
    ‖cuspFormResidual H hH u‖^2 ≤ (1/H^2) * ‖formGradient u‖^2 := by
  have hc : IsClosed {v : FormDomain |
      ‖cuspFormResidual H hH v‖^2 ≤ (1/H^2) * ‖formGradient v‖^2} :=
    isClosed_le ((cuspFormResidual H hH).continuous.norm.pow 2)
      (continuous_const.mul (formGradient.continuous.norm.pow 2))
  have hs : Set.range coreForm ⊆ {v : FormDomain |
      ‖cuspFormResidual H hH v‖^2 ≤ (1/H^2) * ‖formGradient v‖^2} := by
    rintro _ ⟨F, rfl⟩
    change ‖cuspResidual H hH (cuspRestrict H (formEmbedding (coreForm F)))‖^2 ≤ _
    rw [formEmbedding_coreForm, formGradient_coreForm]
    exact cuspResidual_core_norm_sq H hH F
  exact closure_minimal hs hc (coreForm_denseRange u)

/-- The actual core estimate persists on the closed-gradient domain. -/
theorem cuspResidual_closedGradient_norm_sq (H : ℝ) (hH : 1 ≤ H)
    (u : closedGradient.domain) :
    ‖cuspResidual H hH (cuspRestrict H (u : ModularHilbert))‖^2 ≤
      (1 / H^2) * ‖closedGradient u‖^2 := by
  have h := cuspFormResidual_energy_bound H hH (formLift u)
  simpa only [cuspFormResidual, ContinuousLinearMap.comp_apply, formEmbedding,
    formGradient, formLift, Dirichlet.gradientEmbedding_lift, Dirichlet.gradientValue_lift] using h

theorem cuspResidual_closedGradient_norm_le (H : ℝ) (hH : 1 ≤ H)
    (u : closedGradient.domain) :
    ‖cuspResidual H hH (cuspRestrict H (u : ModularHilbert))‖ ≤
      (1/H) * ‖closedGradient u‖ := by
  have h := cuspResidual_closedGradient_norm_sq H hH u
  have heq : (1/H^2) * ‖closedGradient u‖^2 = ((1/H) * ‖closedGradient u‖)^2 := by
    rw [mul_pow, one_div_pow]
  rw [heq] at h
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by positivity) (norm_nonneg _))).mp h

/-- The extended residual has an actual ordinary squared-norm integral on the cusp. -/
theorem cuspResidual_closedGradient_integral (H : ℝ) (hH : 1 ≤ H)
    (u : closedGradient.domain) :
    Integrable (fun τ => ‖cuspResidual H hH (cuspRestrict H (u : ModularHilbert)) τ‖^2)
        (modularMeasure.restrict {τ | H < τ.im}) ∧
      (∫ τ, ‖cuspResidual H hH (cuspRestrict H (u : ModularHilbert)) τ‖^2
        ∂modularMeasure.restrict {τ | H < τ.im}) ≤
        (1/H^2) * ‖closedGradient u‖^2 := by
  refine ⟨(memLp_two_iff_integrable_sq_norm
    (Lp.aestronglyMeasurable _)).mp (Lp.memLp _), ?_⟩
  rw [← cuspMean_l2_norm_sq]
  exact cuspResidual_closedGradient_norm_sq H hH u

theorem cuspFormResidual_norm_le (H : ℝ) (hH : 1 ≤ H) (u : FormDomain) :
    ‖cuspFormResidual H hH u‖ ≤ (1/H) * ‖u‖ := by
  have h := cuspFormResidual_energy_bound H hH u
  have hG : ‖formGradient u‖^2 ≤ ‖u‖^2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
      (Dirichlet.gradientValue_norm_le closedGradient u)
  have h' := h.trans (mul_le_mul_of_nonneg_left hG (by positivity : 0 ≤ 1/H^2))
  have heq : (1/H^2) * ‖u‖^2 = ((1/H) * ‖u‖)^2 := by rw [mul_pow, one_div_pow]
  rw [heq] at h'
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by positivity) (norm_nonneg _))).mp h'

/-- Uniform tail suppression in the actual complete form norm. -/
theorem cuspFormResidual_opNorm_le (H : ℝ) (hH : 1 ≤ H) :
    ‖cuspFormResidual H hH‖ ≤ 1/H := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  exact cuspFormResidual_norm_le H hH

theorem cuspFormResidual_core_ae (H : ℝ) (hH : 1 ≤ H) (F : smoothCore) :
    cuspFormResidual H hH
      (formLift ⟨value F, gradient_le_closedGradient.1 (LinearMap.mem_range_self value F)⟩)
      =ᵐ[modularMeasure.restrict {τ | H < τ.im}]
        (fun τ => cuspHorizontalResidual F.val τ) :=
  cuspResidual_core_ae H hH F

end GapFamily.Analytic
