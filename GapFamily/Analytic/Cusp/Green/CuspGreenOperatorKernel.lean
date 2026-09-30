import GapFamily.Analytic.Cusp.Green.CuspGreenAnalytic
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! Entire dependence of the actual Green kernel in the spatial uniform norm. -/
noncomputable section
namespace GapFamily.Analytic
open Filter Set
open scoped Topology

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- The actual Green kernel along two continuous compact position maps. -/
def cuspGreenContinuousKernel (t₀ : ℝ) (t u : C(X, ℝ)) (κ : ℂ) : C(X, ℂ) where
  toFun x := cuspGreen t₀ (t x) (u x) κ
  continuous_toFun := by
    by_cases hκ : κ = 0
    · subst κ
      simp only [cuspGreen_zero]
      fun_prop
    · simp_rw [cuspGreen_eq_quotient _ _ _ hκ]
      fun_prop

omit [CompactSpace X] in
@[simp] theorem cuspGreenContinuousKernel_apply (t₀ : ℝ) (t u : C(X, ℝ)) (κ : ℂ) (x : X) :
    cuspGreenContinuousKernel t₀ t u κ x = cuspGreen t₀ (t x) (u x) κ := rfl

/-- Evaluation commutes with the Banach-algebra exponential on continuous functions. -/
theorem continuousKernel_exp_apply (f : C(X, ℂ)) (x : X) :
    NormedSpace.exp f x = Complex.exp (f x) := by
  simpa only [Complex.exp_eq_exp_ℂ, ContinuousMap.evalAlgHom_apply] using
    NormedSpace.map_exp (ContinuousMap.evalAlgHom ℂ ℂ x)
      (ContinuousMap.evalCLM ℂ x).continuous f

/-- The two genuine exponential distances in the finite-integral Green formula. -/
def cuspGreenKernelNumerator (t₀ : ℝ) (t u : C(X, ℝ)) (κ : ℂ) : C(X, ℂ) :=
  NormedSpace.exp (κ • (⟨fun x => -((|t x - u x| : ℝ) : ℂ), by fun_prop⟩ : C(X, ℂ))) -
    NormedSpace.exp (κ • (⟨fun x => -((t x + u x - 2 * t₀ : ℝ) : ℂ), by fun_prop⟩ : C(X, ℂ)))

theorem cuspGreenKernelNumerator_apply (t₀ : ℝ) (t u : C(X, ℝ)) (κ : ℂ) (x : X) :
    cuspGreenKernelNumerator t₀ t u κ x =
      Complex.exp (-κ * ((|t x - u x| : ℝ) : ℂ)) -
        Complex.exp (-κ * ((t x + u x - 2 * t₀ : ℝ) : ℂ)) := by
  simp [cuspGreenKernelNumerator, continuousKernel_exp_apply, mul_neg, neg_mul]
  congr 1
  ring

/-- The numerator is entire in the actual uniform spatial norm. -/
theorem differentiable_cuspGreenKernelNumerator (t₀ : ℝ) (t u : C(X, ℝ)) :
    Differentiable ℂ (cuspGreenKernelNumerator t₀ t u) :=
  (differentiable_exp_smul_const ℂ _).sub
    (differentiable_exp_smul_const ℂ _)

/-- The actual uniform kernel is the removable divided difference of its genuine numerator. -/
theorem cuspGreenContinuousKernel_eq_dslope (t₀ : ℝ) (t u : C(X, ℝ)) (κ : ℂ) :
    cuspGreenContinuousKernel t₀ t u κ =
      (1 / 2 : ℂ) • dslope (cuspGreenKernelNumerator t₀ t u) 0 κ := by
  ext x
  have h := (ContinuousMap.evalCLM ℂ x).dslope_comp
    (cuspGreenKernelNumerator t₀ t u) 0 κ
    (fun _ => differentiable_cuspGreenKernelNumerator t₀ t u 0)
  have heq : ((ContinuousMap.evalCLM ℂ x) ∘ cuspGreenKernelNumerator t₀ t u) =
      (fun z : ℂ => Complex.exp (-z * ((|t x - u x| : ℝ) : ℂ)) -
        Complex.exp (-z * ((t x + u x - 2 * t₀ : ℝ) : ℂ))) := by
    funext z
    exact cuspGreenKernelNumerator_apply t₀ t u z x
  rw [heq] at h
  simp only [ContinuousMap.evalCLM_apply] at h
  change cuspGreen t₀ (t x) (u x) κ = (1 / 2 : ℂ) * _
  rw [← h, cuspGreen_eq_dslope]
  ring

/-- Entire continuation holds in the uniform spatial Banach space, including κ=0. -/
theorem differentiable_cuspGreenContinuousKernel (t₀ : ℝ) (t u : C(X, ℝ)) :
    Differentiable ℂ (cuspGreenContinuousKernel t₀ t u) := by
  have hs : Differentiable ℂ (dslope (cuspGreenKernelNumerator t₀ t u) 0) :=
    differentiableOn_univ.mp
      ((Complex.differentiableOn_dslope (s := univ) (c := 0) univ_mem).mpr
        (differentiable_cuspGreenKernelNumerator t₀ t u).differentiableOn)
  have heq : cuspGreenContinuousKernel t₀ t u =
      (fun κ => (1 / 2 : ℂ) • dslope (cuspGreenKernelNumerator t₀ t u) 0 κ) :=
    funext (cuspGreenContinuousKernel_eq_dslope t₀ t u)
  rw [heq]
  exact hs.const_smul (1 / 2 : ℂ)

end GapFamily.Analytic
