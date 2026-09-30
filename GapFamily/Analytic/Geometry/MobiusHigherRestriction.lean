import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Complex.Basic

noncomputable section
namespace GapFamily.Analytic.MobiusHigher
open Filter Set
open scoped Topology

/-- Scalar restriction of the actual finite Taylor family identifies all real derivatives. -/
theorem iteratedFDeriv_real_eq_restrict_complex {f : ℂ → ℂ} {z : ℂ} (n : ℕ)
    (hf : ContDiffAt ℂ n f z) :
    iteratedFDeriv ℝ n f z = (iteratedFDeriv ℂ n f z).restrictScalars ℝ := by
  have hfu : ContDiffWithinAt ℂ n f univ z := hf.contDiffWithinAt
  rcases (contDiffWithinAt_nat.mp hfu) with ⟨u, hu, p, hp⟩
  have huz : u ∈ 𝓝 z := by simpa using hu
  obtain ⟨o, hou, hoo, hzo⟩ := mem_nhds_iff.mp huz
  have hc := (hp.mono hou).eq_iteratedFDerivWithin_of_uniqueDiffOn
    (m := n) le_rfl (hoo.uniqueDiffOn (𝕜 := ℂ)) hzo
  have hr := ((hp.mono hou).restrictScalars ℝ).eq_iteratedFDerivWithin_of_uniqueDiffOn
    (m := n) le_rfl (hoo.uniqueDiffOn (𝕜 := ℝ)) hzo
  rw [iteratedFDerivWithin_of_isOpen n hoo hzo] at hc hr
  rw [← hc, ← hr]
  rfl

/-- Real and complex operator norms agree for every existing complex derivative. -/
theorem norm_iteratedFDeriv_real_eq_complex {f : ℂ → ℂ} {z : ℂ} (n : ℕ)
    (hf : ContDiffAt ℂ n f z) :
    ‖iteratedFDeriv ℝ n f z‖ = ‖iteratedFDeriv ℂ n f z‖ := by
  rw [iteratedFDeriv_real_eq_restrict_complex n hf,
    ContinuousMultilinearMap.norm_restrictScalars]

/-- The actual real multilinear derivative has exactly the ordinary complex derivative norm. -/
theorem norm_iteratedFDeriv_real_eq_iteratedDeriv {f : ℂ → ℂ} {z : ℂ} (n : ℕ)
    (hf : ContDiffAt ℂ n f z) :
    ‖iteratedFDeriv ℝ n f z‖ = ‖iteratedDeriv n f z‖ := by
  rw [norm_iteratedFDeriv_real_eq_complex n hf, norm_iteratedFDeriv_eq_norm_iteratedDeriv]

/-- Analyticity supplies the same exact norm conversion at every finite order. -/
theorem norm_iteratedFDeriv_real_eq_iteratedDeriv_of_analyticAt {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (n : ℕ) :
    ‖iteratedFDeriv ℝ n f z‖ = ‖iteratedDeriv n f z‖ :=
  norm_iteratedFDeriv_real_eq_iteratedDeriv n hf.contDiffAt

end GapFamily.Analytic.MobiusHigher
