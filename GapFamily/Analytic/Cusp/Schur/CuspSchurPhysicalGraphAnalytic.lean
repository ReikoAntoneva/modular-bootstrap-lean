import GapFamily.Analytic.Cusp.Schur.CuspSchurGlobalPhysical
import GapFamily.Analytic.Cusp.Schur.CuspSchurPhysicalAnalytic
import GapFamily.Analytic.Modular.ModularGraphAnalytic

noncomputable section

namespace GapFamily.Analytic.CuspSchurPhysicalGraphAnalytic

open Dirichlet ModularGradient CuspSchur CuspSchurGlobalPhysical

/-- The actual physical Schur response together with its genuine Laplacian value. -/
theorem actualSchurResolvent_pair_mem_graph_physical {κ : ℂ} (hκ : 0 < κ.re)
    (hhalf : κ ≠ (1 / 2 : ℂ)) (f : ModularHilbert) :
    (actualSchurResolvent ((1 / 4 : ℂ) - κ ^ 2) f,
      f + ((1 / 4 : ℂ) - κ ^ 2) • actualSchurResolvent ((1 / 4 : ℂ) - κ ^ 2) f)
        ∈ laplacian.graph := by
  have h := actualSchurResolvent_rightInverse_physical hκ hhalf f
  have heq := sub_eq_iff_eq_add.mp h
  rw [← heq]
  exact laplacian.mem_graph ⟨actualSchurResolvent ((1 / 4 : ℂ) - κ ^ 2) f,
    actualSchurResolvent_mem_domain_physical hκ hhalf f⟩

/-- The graph projection packages the literal Schur operator and the literal
identity-plus-parameter-times-resolvent operator in the actual closed graph. -/
def actualSchurGraphResolvent (κ : ℂ) : ModularHilbert →L[ℂ] LaplacianGraphDomain :=
  laplacianGraphOperator ModularHilbert
    (actualSchurResolvent ((1 / 4 : ℂ) - κ ^ 2),
      ContinuousLinearMap.id ℂ ModularHilbert +
        ((1 / 4 : ℂ) - κ ^ 2) • actualSchurResolvent ((1 / 4 : ℂ) - κ ^ 2))

theorem actualSchurGraphResolvent_analyticAt_of_analyticAt {κ : ℂ}
    (hS : AnalyticAt ℂ
      (fun k => actualSchurResolvent ((1 / 4 : ℂ) - k ^ 2)) κ) :
    AnalyticAt ℂ actualSchurGraphResolvent κ := by
  have hz : AnalyticAt ℂ (fun k : ℂ => (1 / 4 : ℂ) - k ^ 2) κ :=
    analyticAt_const.sub (analyticAt_id.pow 2)
  exact laplacianGraphOperator_analyticAt ModularHilbert hS
    (analyticAt_const.add (hz.smul hS))

/-- The actual full resolvent is analytic in the graph norm throughout the
physical half-plane except the constant eigenvalue pole. -/
theorem actualSchurGraphResolvent_analyticAt_physical {κ : ℂ} (hκ : 0 < κ.re)
    (hhalf : κ ≠ (1 / 2 : ℂ)) :
    AnalyticAt ℂ actualSchurGraphResolvent κ :=
  actualSchurGraphResolvent_analyticAt_of_analyticAt
    (CuspSchurPhysicalAnalytic.actualSchurResolvent_analyticAt_physical hκ hhalf)

theorem actualSchurGraphResolvent_analyticOnNhd_physical :
    AnalyticOnNhd ℂ actualSchurGraphResolvent {κ : ℂ | 0 < κ.re ∧ κ ≠ (1 / 2 : ℂ)} :=
  fun _ hκ => actualSchurGraphResolvent_analyticAt_physical hκ.1 hκ.2

theorem actualSchurGraphResolvent_embedding_physical {κ : ℂ} (hκ : 0 < κ.re)
    (hhalf : κ ≠ (1 / 2 : ℂ)) :
    (gradientEmbedding laplacian).comp (actualSchurGraphResolvent κ) =
      actualSchurResolvent ((1 / 4 : ℂ) - κ ^ 2) := by
  apply laplacianGraphOperator_embedding ModularHilbert
  exact actualSchurResolvent_pair_mem_graph_physical hκ hhalf

theorem actualSchurGraphResolvent_value_physical {κ : ℂ} (hκ : 0 < κ.re)
    (hhalf : κ ≠ (1 / 2 : ℂ)) :
    (gradientValue laplacian).comp (actualSchurGraphResolvent κ) =
      ContinuousLinearMap.id ℂ ModularHilbert +
        ((1 / 4 : ℂ) - κ ^ 2) • actualSchurResolvent ((1 / 4 : ℂ) - κ ^ 2) := by
  apply laplacianGraphOperator_value ModularHilbert
  exact actualSchurResolvent_pair_mem_graph_physical hκ hhalf

/-- At every physical parameter the packaged vector is the actual operator-domain
lift, with both coordinates fixed by the genuine resolvent equation. -/
theorem actualSchurGraphResolvent_eq_gradientLift_physical {κ : ℂ} (hκ : 0 < κ.re)
    (hhalf : κ ≠ (1 / 2 : ℂ)) (f : ModularHilbert) :
    actualSchurGraphResolvent κ f = gradientLift laplacian
      ⟨actualSchurResolvent ((1 / 4 : ℂ) - κ ^ 2) f,
        actualSchurResolvent_mem_domain_physical hκ hhalf f⟩ := by
  change laplacianGraphPairMap
    (actualSchurResolvent ((1 / 4 : ℂ) - κ ^ 2) f,
      f + ((1 / 4 : ℂ) - κ ^ 2) • actualSchurResolvent ((1 / 4 : ℂ) - κ ^ 2) f) = _
  rw [laplacianGraphPairMap_eq_of_mem
    (actualSchurResolvent_pair_mem_graph_physical hκ hhalf f)]
  apply Subtype.ext
  exact congrArg (WithLp.toLp 2) (Prod.ext rfl
    (sub_eq_iff_eq_add.mp (actualSchurResolvent_rightInverse_physical hκ hhalf f)).symm)

end GapFamily.Analytic.CuspSchurPhysicalGraphAnalytic
