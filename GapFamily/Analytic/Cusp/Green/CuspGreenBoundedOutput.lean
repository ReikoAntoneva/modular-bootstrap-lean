import GapFamily.Analytic.Cusp.Green.CuspGreenCompactResponse
import GapFamily.Analytic.Cusp.Green.CuspGreenMixedOperator
import GapFamily.Analytic.Cusp.Green.CuspGreenCollarOutput
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

noncomputable section
namespace GapFamily.Analytic
open Set Filter MeasureTheory ModularGradient
open scoped Topology

/-- Actual finite-height Green output on ambient modular Hilbert sources. -/
def cuspGreenBoundedOutput (L T : ℝ) (κ : ℂ) : ModularHilbert →L[ℂ] ModularHilbert :=
  ((cuspGreenSourceEmbedding L).toContinuousLinearMap.comp
    (cuspGreenMixedL2Operator L T κ)).comp (cuspGreenSourceCoefficient T)

/-- The bounded output family is entire in the genuine operator norm. -/
theorem differentiable_cuspGreenBoundedOutput (L T : ℝ) :
    Differentiable ℂ (cuspGreenBoundedOutput L T) := by
  exact ((differentiable_const (cuspGreenSourceEmbedding L).toContinuousLinearMap).clm_comp
    (differentiable_cuspGreenMixedL2Operator L T)).clm_comp
      (differentiable_const (cuspGreenSourceCoefficient T))

theorem analyticAt_cuspGreenBoundedOutput (L T : ℝ) (κ : ℂ) :
    AnalyticAt ℂ (cuspGreenBoundedOutput L T) κ :=
  (differentiable_cuspGreenBoundedOutput L T).analyticAt κ

/-- The threshold limit concerns bounded local output, not a global form vector. -/
theorem cuspGreenBoundedOutput_tendsto_zero (L T : ℝ) :
    Tendsto (cuspGreenBoundedOutput L T) (𝓝 (0 : ℂ))
      (𝓝 (cuspGreenBoundedOutput L T 0)) :=
  (differentiable_cuspGreenBoundedOutput L T).continuous.tendsto 0

/-- At every complex parameter the bounded output is the literal clipped Green integral. -/
theorem cuspGreenBoundedOutput_ae {L : ℝ} (hL : 0 ≤ L) (T : ℝ) (κ : ℂ)
    (F : ModularHilbert) :
    cuspGreenBoundedOutput L T κ F =ᵐ[modularMeasure]
      fun τ : UpperHalfPlane => if 1 < τ.im ∧ τ.im ≤ Real.exp L then Real.sqrt τ.im •
        cuspGreenCollarResponse 0 T κ (cuspGreenSourceCoefficient T F) (Real.log τ.im) else 0 := by
  change cuspGreenSourceEmbedding L
    (ContinuousMap.toLp 2 (cuspGreenCollarMeasure 0 L) ℂ
      (cuspGreenMixedOperator L T κ (cuspGreenSourceCoefficient T F))) =ᵐ[_] _
  apply cuspGreenSourceEmbedding_toLp_ae L hL
  intro t
  exact cuspGreenMixedOperator_eq_response L T κ _ t

/-- In the physical half-plane this is exactly low-height projection of the
actual W-valued scalar response of every height-supported source. -/
theorem cuspGreenBoundedOutput_eq_physical {L T : ℝ} (hL : 0 ≤ L) (hT : 0 ≤ T)
    {κ : ℂ} (hκ : 0 < κ.re) (F : ModularHilbert)
    (hF : modularHighCut (Real.exp T) F = 0) :
    cuspGreenBoundedOutput L T κ F =
      modularLowCut (Real.exp L)
        (scalarCuspEmbedding (cuspScalarPencilSolution (1/4 - κ^2) F)) := by
  apply Lp.ext
  filter_upwards [cuspGreenBoundedOutput_ae hL T κ F,
    modularLowCut_ae (Real.exp L)
      (scalarCuspEmbedding (cuspScalarPencilSolution (1/4 - κ^2) F)),
    cuspScalarPencilSolution_greenCoefficient_ae hT hκ F hF] with τ hout hcut hphysical
  rw [hout, hcut]
  by_cases hτ : τ.im ≤ Real.exp L
  · rw [indicator_of_mem (show τ ∈ {τ : UpperHalfPlane | τ.im ≤ Real.exp L} from hτ), hphysical]
    simp only [hτ, and_true]
  · rw [indicator_of_notMem (show τ ∉ {τ : UpperHalfPlane | τ.im ≤ Real.exp L} from hτ)]
    simp only [hτ, and_false, ite_false]

/-- Both input and output are actual finite-height compressions on the ambient Hilbert space. -/
def cuspGreenLocalizedOutput (L T : ℝ) (κ : ℂ) : ModularHilbert →L[ℂ] ModularHilbert :=
  (cuspGreenBoundedOutput L T κ).comp (modularLowCut (Real.exp T))

theorem differentiable_cuspGreenLocalizedOutput (L T : ℝ) :
    Differentiable ℂ (cuspGreenLocalizedOutput L T) :=
  (differentiable_cuspGreenBoundedOutput L T).clm_comp
    (differentiable_const (modularLowCut (Real.exp T)))

theorem analyticAt_cuspGreenLocalizedOutput (L T : ℝ) (κ : ℂ) :
    AnalyticAt ℂ (cuspGreenLocalizedOutput L T) κ :=
  (differentiable_cuspGreenLocalizedOutput L T).analyticAt κ

/-- The entire bounded operator agrees with the genuine two-sided compression
of the physical scalar form solution, on every ambient L² source. -/
theorem cuspGreenLocalizedOutput_eq_physical {L T : ℝ} (hL : 0 ≤ L) (hT : 0 ≤ T)
    {κ : ℂ} (hκ : 0 < κ.re) :
    cuspGreenLocalizedOutput L T κ =
      ((modularLowCut (Real.exp L)).comp
        (scalarCuspEmbedding.comp (cuspScalarPencilSolution (1/4 - κ^2)))).comp
          (modularLowCut (Real.exp T)) := by
  apply ContinuousLinearMap.ext
  intro F
  exact cuspGreenBoundedOutput_eq_physical hL hT hκ
    (modularLowCut (Real.exp T) F) (modularHighCut_lowCut (Real.exp T) F)

/-- The threshold is still the ordinary integrable min-kernel in the finite output window. -/
theorem cuspGreenBoundedOutput_zero_ae {L : ℝ} (hL : 0 ≤ L) (T : ℝ)
    (F : ModularHilbert) :
    cuspGreenBoundedOutput L T 0 F =ᵐ[modularMeasure]
      fun τ : UpperHalfPlane => if 1 < τ.im ∧ τ.im ≤ Real.exp L then Real.sqrt τ.im •
        (∫ u : CuspGreenCollar 0 T,
          ((min (Real.log τ.im) (u : ℝ) : ℝ) : ℂ) *
            cuspGreenSourceCoefficient T F u ∂cuspGreenCollarMeasure 0 T) else 0 := by
  simpa only [cuspGreenCollarResponse, cuspGreen_zero, sub_zero] using
    cuspGreenBoundedOutput_ae hL T 0 F

end GapFamily.Analytic
