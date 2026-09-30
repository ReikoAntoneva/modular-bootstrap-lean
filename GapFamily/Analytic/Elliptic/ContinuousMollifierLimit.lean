import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

noncomputable section
namespace GapFamily.Analytic
open ContinuousLinearMap Filter MeasureTheory Set
open scoped Convolution Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {ι : Type*} {l : Filter ι} {φ : ι → ContDiffBump (0 : ℂ)}
variable {g : ℂ → E} {U : Set ℂ}

/-- Normalized shrinking bumps converge locally uniformly wherever the actual
measurable function is continuous on an open set. -/
theorem normed_bump_convolution_tendstoLocallyUniformlyOn
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0))
    (hg : AEStronglyMeasurable g volume) (hU : IsOpen U) (hc : ContinuousOn g U) :
    TendstoLocallyUniformlyOn
      (fun i y => ((φ i).normed volume ⋆[lsmul ℝ ℝ, volume] g) y) g l U := by
  rw [hU.tendstoLocallyUniformlyOn_iff_forall_tendsto]
  intro x hx
  have hcx : ContinuousAt g x := hc.continuousAt (hU.mem_nhds hx)
  have hleft : Tendsto (fun p : ι × ℂ => g p.2) (l ×ˢ 𝓝 x) (𝓝 (g x)) :=
    hcx.tendsto.comp tendsto_snd
  have hright : Tendsto
      (fun p : ι × ℂ => ((φ p.1).normed volume ⋆[lsmul ℝ ℝ, volume] g) p.2)
      (l ×ˢ 𝓝 x) (𝓝 (g x)) :=
    ContDiffBump.convolution_tendsto_right
      (φ := fun p : ι × ℂ => φ p.1) (g := fun _ : ι × ℂ => g)
      (k := Prod.snd) (μ := volume)
      (hφ.comp tendsto_fst) (Eventually.of_forall fun _ => hg)
      (hcx.tendsto.comp tendsto_snd) tendsto_snd
  exact (hleft.prodMk_nhds hright).mono_right (nhds_le_uniformity (g x))

/-- Pointwise convergence follows for every point of the open continuity set. -/
theorem normed_bump_convolution_tendsto_of_continuousOn
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0))
    (hg : AEStronglyMeasurable g volume) (hU : IsOpen U) (hc : ContinuousOn g U)
    {x : ℂ} (hx : x ∈ U) :
    Tendsto (fun i => ((φ i).normed volume ⋆[lsmul ℝ ℝ, volume] g) x) l (𝓝 (g x)) :=
  (normed_bump_convolution_tendstoLocallyUniformlyOn hφ hg hU hc).tendsto_at hx

end GapFamily.Analytic
