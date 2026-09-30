import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.LinearPMap

/-! The identity principle for membership in a closed complex linear subspace. -/
set_option autoImplicit false

noncomputable section
namespace GapFamily.Analytic
open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Analytic continuation preserves closed-subspace membership from an actual
open parameter neighborhood through any preconnected analytic parameter set. -/
theorem analyticOnNhd_mem_closedSubmodule_of_eventually_mem
    (S : Submodule ℂ E) (hS : IsClosed (S : Set E))
    {f : ℂ → E} {U : Set ℂ} (hf : AnalyticOnNhd ℂ f U)
    (hU : IsPreconnected U) {z₀ : ℂ} (hz₀ : z₀ ∈ U)
    (hnear : ∀ᶠ z in 𝓝 z₀, f z ∈ S) :
    ∀ z ∈ U, f z ∈ S := by
  let : IsClosed (S : Set E) := hS
  have hq : AnalyticOnNhd ℂ (fun z => S.mkQL (f z)) U :=
    fun z hz => (S.mkQL.analyticAt _).comp (hf z hz)
  have hzero : (fun z => S.mkQL (f z)) =ᶠ[𝓝 z₀] 0 := by
    filter_upwards [hnear] with z hz
    simpa only [Submodule.mkQL_apply, Submodule.mkQ_apply, Pi.zero_apply] using
      (Submodule.Quotient.mk_eq_zero (p := S) (x := f z)).mpr hz
  have hall := hq.eqOn_zero_of_preconnected_of_eventuallyEq_zero hU hz₀ hzero
  intro z hz
  exact (Submodule.Quotient.mk_eq_zero (p := S) (x := f z)).mp (hall hz)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- An analytic value/operator-value pair stays in the actual closed operator graph. -/
theorem analyticOnNhd_mem_graph_of_eventually_mem
    (A : E →ₗ.[ℂ] F) (hA : A.IsClosed)
    {f : ℂ → E} {g : ℂ → F} {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (hU : IsPreconnected U) {z₀ : ℂ} (hz₀ : z₀ ∈ U)
    (hnear : ∀ᶠ z in 𝓝 z₀, (f z, g z) ∈ A.graph) :
    ∀ z ∈ U, (f z, g z) ∈ A.graph := by
  apply analyticOnNhd_mem_closedSubmodule_of_eventually_mem A.graph hA
    (f := fun z => (f z, g z)) ?_ hU hz₀ hnear
  exact fun z hz => (hf z hz).prod (hg z hz)

/-- The graph conclusion gives literal domain membership and the operator equation,
without assuming regularity of the continued vectors separately. -/
theorem analyticOnNhd_domain_apply_of_eventually_mem_graph
    (A : E →ₗ.[ℂ] F) (hA : A.IsClosed)
    {f : ℂ → E} {g : ℂ → F} {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (hU : IsPreconnected U) {z₀ : ℂ} (hz₀ : z₀ ∈ U)
    (hnear : ∀ᶠ z in 𝓝 z₀, (f z, g z) ∈ A.graph) :
    ∀ z ∈ U, ∃ hz : f z ∈ A.domain, A ⟨f z, hz⟩ = g z := by
  intro z hz
  obtain ⟨u, hu, hAu⟩ := A.mem_graph_iff.mp
    (analyticOnNhd_mem_graph_of_eventually_mem A hA hf hg hU hz₀ hnear z hz)
  change (u : E) = f z at hu
  change A u = g z at hAu
  refine ⟨hu ▸ u.property, ?_⟩
  convert hAu using 1
  congr 1
  exact Subtype.ext hu.symm

end GapFamily.Analytic
