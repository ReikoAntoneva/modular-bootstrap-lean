import GapFamily.Analytic.Elliptic.C1ModularForm
import GapFamily.Analytic.Spatial.SpatialOrbitGradientIdentification

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open Set Filter MeasureTheory UpperHalfPlane ModularGradient
open scoped ContDiff MatrixGroups Topology

/-- Every actual Schur integral output has a form lift with exactly the proved L² gradient. -/
theorem exists_form_spatialOrbitIntegralOperator (s : ℝ) (hs : 1 < s) (f : ModularHilbert) :
    ∃ u : FormDomain,
      formEmbedding u = spatialOrbitIntegralOperator s hs f ∧
      formGradient u = spatialOrbitGradientOperator s hs f := by
  have hf : MemLp (fun τ : UpperHalfPlane => spatialOrbitIntegralFunction s f τ) 2 modularMeasure :=
    (memLp_congr_ae (spatialOrbitIntegralFunction_ae s hs f)).mp (Lp.memLp _)
  have hd (v : ℂ) : MemLp (directional (spatialOrbitIntegralFunction s f) v) 2 modularMeasure := by
    change MemLp (fun z : UpperHalfPlane => (z.im : ℂ) * fderiv ℝ (spatialOrbitIntegralFunction s f) (z : ℂ) v) 2 modularMeasure
    simpa only [Complex.real_smul] using
      memLp_spatialOrbitIntegralFunction_frame s hs v f
  obtain ⟨u, hu, hx, hy⟩ := C1ModularForm.exists_form_of_C1
    (spatialOrbitIntegralFunction s f) (contDiffOn_spatialOrbitIntegralFunction s hs f)
    (fun γ τ => spatialOrbitIntegralFunction_modular s f τ γ) hf (hd 1) (hd Complex.I)
  refine ⟨u, ?_, ?_⟩
  · rw [hu]
    exact Lp.ext (hf.coeFn_toLp.trans (spatialOrbitIntegralFunction_ae s hs f).symm)
  · apply (WithLp.linearEquiv 2 ℂ (ModularHilbert × ModularHilbert)).injective
    apply Prod.ext
    · change (formGradient u).ofLp.1 = (spatialOrbitGradientOperator s hs f).ofLp.1
      rw [hx]
      apply Lp.ext
      exact (hd 1).coeFn_toLp.trans (by
        change (fun z : UpperHalfPlane => (z.im : ℂ) * fderiv ℝ (spatialOrbitIntegralFunction s f) (z : ℂ) 1) =ᵐ[modularMeasure] _
        simpa only [Complex.real_smul] using
          (spatialOrbitGradientOperator_ae_fderiv s hs f).1.symm)
    · change (formGradient u).ofLp.2 = (spatialOrbitGradientOperator s hs f).ofLp.2
      rw [hy]
      apply Lp.ext
      exact (hd Complex.I).coeFn_toLp.trans (by
        change (fun z : UpperHalfPlane => (z.im : ℂ) * fderiv ℝ (spatialOrbitIntegralFunction s f) (z : ℂ) Complex.I) =ᵐ[modularMeasure] _
        simpa only [Complex.real_smul] using
          (spatialOrbitGradientOperator_ae_fderiv s hs f).2.symm)

/-- The actual value and gradient operators land in the original closed gradient graph. -/
theorem spatialOrbit_value_gradient_mem_graph (s : ℝ) (hs : 1 < s) (f : ModularHilbert) :
    (spatialOrbitIntegralOperator s hs f, spatialOrbitGradientOperator s hs f) ∈ closedGradient.graph := by
  obtain ⟨u, hu, hg⟩ := exists_form_spatialOrbitIntegralOperator s hs f
  rw [← hu, ← hg]
  exact u.property

/-- The genuine all-L² form-valued orbit integral operator. -/
def spatialOrbitFormOperator (s : ℝ) (hs : 1 < s) : ModularHilbert →L[ℂ] FormDomain :=
  (((WithLp.prodContinuousLinearEquiv 2 ℂ ModularHilbert GradientSpace).symm.toContinuousLinearMap).comp
    ((spatialOrbitIntegralOperator s hs).prod (spatialOrbitGradientOperator s hs))).codRestrict
      (Dirichlet.gradientGraph closedGradient) (spatialOrbit_value_gradient_mem_graph s hs)

@[simp] theorem formEmbedding_spatialOrbitFormOperator (s : ℝ) (hs : 1 < s) (f : ModularHilbert) :
    formEmbedding (spatialOrbitFormOperator s hs f) = spatialOrbitIntegralOperator s hs f := rfl

@[simp] theorem formGradient_spatialOrbitFormOperator (s : ℝ) (hs : 1 < s) (f : ModularHilbert) :
    formGradient (spatialOrbitFormOperator s hs f) = spatialOrbitGradientOperator s hs f := rfl

/-- Membership in the actual closed-gradient domain, with no source smoothness premise. -/
theorem spatialOrbitIntegralOperator_mem_closedGradient_domain (s : ℝ) (hs : 1 < s) (f : ModularHilbert) :
    spatialOrbitIntegralOperator s hs f ∈ closedGradient.domain := by
  simpa only [formEmbedding_spatialOrbitFormOperator] using
    Dirichlet.gradientEmbedding_mem_domain closedGradient (spatialOrbitFormOperator s hs f)

end GapFamily.Analytic.SpatialPoint
