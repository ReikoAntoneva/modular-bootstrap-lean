import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.UniformConvergence

open Filter
open scoped Topology

namespace GapFamily.Analytic.StrongOperatorDensity

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Strong convergence of a family of contractions to the identity extends from
any dense subset. No completeness or condition on the indexing filter is needed. -/
theorem tendsto_apply_of_dense_of_opNorm_le_one
    (A : ι → E →L[ℂ] E) (l : Filter ι) (S : Set E)
    (hnorm : ∀ i, ‖A i‖ ≤ 1) (hS : Dense S)
    (hconv : ∀ x ∈ S, Tendsto (fun i => A i x) l (𝓝 x)) (x : E) :
    Tendsto (fun i => A i x) l (𝓝 x) := by
  have hLip : ∀ i, LipschitzWith 1 (A i) := fun i =>
    ContinuousLinearMap.lipschitzWith_of_opNorm_le (by simpa using hnorm i)
  have hequi : Equicontinuous (fun i => (A i : E → E)) :=
    (LipschitzWith.uniformEquicontinuous (fun i => (A i : E → E)) 1 hLip).equicontinuous
  exact (hequi x).tendsto_of_mem_closure
    (f := fun y : E => y) (continuousAt_id.mono_left nhdsWithin_le_nhds) hconv (hS x)

end GapFamily.Analytic.StrongOperatorDensity
