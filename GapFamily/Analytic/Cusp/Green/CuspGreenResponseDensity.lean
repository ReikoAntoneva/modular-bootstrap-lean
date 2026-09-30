import GapFamily.Analytic.Cusp.Green.CuspGreenOperatorTrace
import GapFamily.Analytic.Cusp.Profile.CuspProfileFormLimit
import Mathlib.Topology.Sequences

/-!
# Dense-source extension of the literal cusp Green representative

Every fixed observation is a bounded linear functional of the actual collar
L² source. An almost-everywhere convergent subsequence of an ambient L² limit
therefore identifies any continuous response operator from its values on a
dense source set. No differentiability of rough sources is required.
-/

noncomputable section

namespace GapFamily.Analytic

open Set Filter MeasureTheory ModularGradient
open scoped Topology

/-- Fixed real-position evaluation of the actual Green response is a bounded linear functional. -/
def cuspGreenCollarResponsePointOperator (a T t : ℝ) (κ : ℂ) :
    Lp ℂ 2 (cuspGreenCollarMeasure a T) →L[ℂ] ℂ :=
  let k : C(Unit × CuspGreenCollar a T, ℂ) :=
    ⟨fun p => cuspGreen a t p.2 κ,
      (cuspGreen_continuous_source a t κ).comp
        (continuous_subtype_val.comp continuous_snd)⟩
  (ContinuousMap.evalCLM ℂ ()).comp
    (compactKernelIntegralOperator (cuspGreenCollarMeasure a T) k)

@[simp] theorem cuspGreenCollarResponsePointOperator_apply (a T t : ℝ) (κ : ℂ)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure a T)) :
    cuspGreenCollarResponsePointOperator a T t κ f = cuspGreenCollarResponse a T κ f t := by
  unfold cuspGreenCollarResponsePointOperator
  rw [ContinuousLinearMap.comp_apply]
  change compactKernelIntegralOperator _ _ f () = _
  rw [compactKernelIntegralOperator_apply]
  rfl

/-- No source regularity is needed for pointwise source dependence of the actual integral. -/
theorem continuous_cuspGreenCollarResponse_source (a T t : ℝ) (κ : ℂ) :
    Continuous (fun f : Lp ℂ 2 (cuspGreenCollarMeasure a T) =>
      cuspGreenCollarResponse a T κ f t) := by
  have hfun : (fun f : Lp ℂ 2 (cuspGreenCollarMeasure a T) =>
      cuspGreenCollarResponse a T κ f t) = cuspGreenCollarResponsePointOperator a T t κ :=
    funext (fun f => (cuspGreenCollarResponsePointOperator_apply a T t κ f).symm)
  rw [hfun]
  exact (cuspGreenCollarResponsePointOperator a T t κ).continuous

/-- The literal physical response converges pointwise whenever its sources converge in collar L². -/
theorem cuspGreenCollarResponse_physical_tendsto {T : ℝ} (κ : ℂ)
    {f : ℕ → Lp ℂ 2 (cuspGreenCollarMeasure 0 T)}
    {g : Lp ℂ 2 (cuspGreenCollarMeasure 0 T)} (hfg : Tendsto f atTop (𝓝 g))
    (z : UpperHalfPlane) :
    Tendsto (fun n => if 1 < z.im then
      Real.sqrt z.im • cuspGreenCollarResponse 0 T κ (f n) (Real.log z.im) else 0) atTop
      (𝓝 (if 1 < z.im then
        Real.sqrt z.im • cuspGreenCollarResponse 0 T κ g (Real.log z.im) else 0)) := by
  by_cases hz : 1 < z.im
  · simp only [ite_eq_left hz]
    exact ((continuous_cuspGreenCollarResponse_source 0 T (Real.log z.im) κ).tendsto g
      |>.comp hfg).const_smul (Real.sqrt z.im)
  · simp only [ite_eq_right hz]
    exact tendsto_const_nhds

/-- An actual continuous ambient response operator has the literal Green representative on
every collar L² source once that identity is proved on a dense source subset. -/
theorem cuspGreenCollarResponse_ae_of_dense (T : ℝ) (κ : ℂ)
    (A : Lp ℂ 2 (cuspGreenCollarMeasure 0 T) →L[ℂ] ModularHilbert)
    {S : Set (Lp ℂ 2 (cuspGreenCollarMeasure 0 T))} (hS : Dense S)
    (hrep : ∀ f ∈ S, A f =ᵐ[modularMeasure]
      (fun z : UpperHalfPlane => if 1 < z.im then
        Real.sqrt z.im • cuspGreenCollarResponse 0 T κ f (Real.log z.im) else 0))
    (f : Lp ℂ 2 (cuspGreenCollarMeasure 0 T)) :
    A f =ᵐ[modularMeasure]
      (fun z : UpperHalfPlane => if 1 < z.im then
        Real.sqrt z.im • cuspGreenCollarResponse 0 T κ f (Real.log z.im) else 0) := by
  obtain ⟨fs, hfsS, hfs⟩ := mem_closure_iff_seq_limit.mp (hS f)
  exact cuspProfile_Lp_limit_ae ((A.continuous.tendsto f).comp hfs)
    (fun n => hrep (fs n) (hfsS n))
    (fun z => cuspGreenCollarResponse_physical_tendsto κ hfs z)


end GapFamily.Analytic
