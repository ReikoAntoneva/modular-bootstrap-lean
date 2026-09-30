import GapFamily.Analytic.Modular.Elliptic.ModularLocalEvaluation
import Mathlib.Topology.Order.DenselyOrdered

/-! # Graph-norm evaluation on a fixed interior complex rectangle -/

noncomputable section
namespace GapFamily.Analytic.ModularGradient

open Set Filter MeasureTheory Dirichlet
open scoped Topology

/-- The literal closed rectangle in real and imaginary coordinates. -/
def localEvaluationRectangle (a b c d : ℝ) : Set ℂ :=
  Complex.equivRealProdCLM ⁻¹' (Icc a b ×ˢ Icc c d)

@[simp] theorem mem_localEvaluationRectangle (a b c d : ℝ) (z : ℂ) :
    z ∈ localEvaluationRectangle a b c d ↔
      a ≤ z.re ∧ z.re ≤ b ∧ c ≤ z.im ∧ z.im ≤ d := by
  simp only [localEvaluationRectangle, mem_preimage, mem_prod, mem_Icc]
  tauto

theorem isCompact_localEvaluationRectangle (a b c d : ℝ) :
    IsCompact (localEvaluationRectangle a b c d) :=
  Complex.equivRealProdCLM.toHomeomorph.isCompact_preimage.mpr
    (isCompact_Icc.prod isCompact_Icc)

instance (a b c d : ℝ) : CompactSpace (localEvaluationRectangle a b c d) :=
  isCompact_iff_compactSpace.mp (isCompact_localEvaluationRectangle a b c d)

/-- A nondegenerate closed rectangle has no parts invisible to its interior. -/
theorem localEvaluationRectangle_regular {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    localEvaluationRectangle a b c d ⊆
      closure (interior (localEvaluationRectangle a b c d)) := by
  change Complex.equivRealProdCLM.toHomeomorph ⁻¹' (Icc a b ×ˢ Icc c d) ⊆
    closure (interior (Complex.equivRealProdCLM.toHomeomorph ⁻¹' (Icc a b ×ˢ Icc c d)))
  rw [← Homeomorph.preimage_interior, ← Homeomorph.preimage_closure,
    interior_prod_eq, interior_Icc, interior_Icc, closure_prod_eq,
    closure_Ioo hab.ne, closure_Ioo hcd.ne]

/-- The actual Laplacian graph's continuous representative on this fixed rectangle. -/
def laplacianRectangleRestriction (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    (hK : localEvaluationRectangle a b c d ⊆ modularInterior) :
    LaplacianGraphDomain →L[ℂ] C(localEvaluationRectangle a b c d, ℂ) :=
  laplacianLocalRestriction _ hK (localEvaluationRectangle_regular hab hcd)

theorem laplacianRectangleRestriction_ae (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    (hK : localEvaluationRectangle a b c d ⊆ modularInterior) (u : LaplacianGraphDomain) :
    localContinuousExtend (laplacianRectangleRestriction a b c d hab hcd hK u)
      =ᵐ[volume.restrict (localEvaluationRectangle a b c d)]
        (fun z => laplacianGraphCoordinate u z) :=
  laplacianLocalRestriction_ae _ hK (localEvaluationRectangle_regular hab hcd) u

/-- Point evaluation is a constructed complex continuous linear functional
on the actual complete operator graph domain. -/
def laplacianRectangleEvaluation (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    (hK : localEvaluationRectangle a b c d ⊆ modularInterior)
    (z : localEvaluationRectangle a b c d) : LaplacianGraphDomain →L[ℂ] ℂ :=
  (ContinuousMap.evalCLM ℂ z).comp (laplacianRectangleRestriction a b c d hab hcd hK)

/-- The constructed evaluation agrees with every genuine local continuous
representative of the same actual value at the specified point. -/
theorem laplacianRectangleEvaluation_eq_localRepresentative
    (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    (hK : localEvaluationRectangle a b c d ⊆ modularInterior)
    (z : localEvaluationRectangle a b c d) (u : LaplacianGraphDomain)
    {V : Set ℂ} (hV : IsOpen V) (hz : (z : ℂ) ∈ V) (hVU : V ⊆ modularInterior)
    {G : ℂ → ℂ} (hG : ContinuousOn G V)
    (hGae : G =ᵐ[volume.restrict V] (fun w => laplacianGraphCoordinate u w)) :
    laplacianRectangleEvaluation a b c d hab hcd hK z u = G z := by
  have hr : laplacianInteriorRepresentative u =ᵐ[volume.restrict V]
      (fun w => laplacianGraphCoordinate u w) :=
    ae_restrict_of_ae_restrict_of_subset hVU (laplacianInteriorRepresentative_ae u)
  exact Measure.eqOn_open_of_ae_eq (μ := volume) (hr.trans hGae.symm) hV
    ((laplacianInteriorRepresentative_continuousOn u).mono hVU) hG hz

/-- A finite uniform point-evaluation bound involving the literal modular
value and Laplacian norms, for every actual operator-domain vector. -/
theorem laplacianRectangleEvaluation_graph_bound
    (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    (hK : localEvaluationRectangle a b c d ⊆ modularInterior) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : laplacian.domain) (z : localEvaluationRectangle a b c d),
      ‖laplacianRectangleEvaluation a b c d hab hcd hK z (gradientLift laplacian u)‖^2 ≤
        C^2 * (‖(u : ModularHilbert)‖^2 + ‖laplacian u‖^2) := by
  obtain ⟨C, hC, hbound⟩ := laplacianLocalRestriction_bound
    (localEvaluationRectangle a b c d) hK (localEvaluationRectangle_regular hab hcd)
  refine ⟨C, hC, fun u z => ?_⟩
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC.le (norm_nonneg _))).mpr
    (hbound (gradientLift laplacian u) z)
  rw [mul_pow, gradientGraph_norm_sq, gradientEmbedding_lift, gradientValue_lift] at hs
  exact hs

end GapFamily.Analytic.ModularGradient
