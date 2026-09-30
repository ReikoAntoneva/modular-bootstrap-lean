import GapFamily.Analytic.Cusp.Green.CuspGreen
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.Algebra.Support

/-!
# The actual half-line scalar Green integral

The source is an ordinary complex-valued continuous function with compact
support. The Green integral is over the actual half-line, not an unspecified
solution satisfying an assumed equation.
-/

noncomputable section

namespace GapFamily.Analytic

open MeasureTheory Set

/-- Integration of the actual scalar cusp kernel against an ordinary source. -/
def cuspGreenSolution (t₀ : ℝ) (κ : ℂ) (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ u : ℝ in Ioi t₀, cuspGreen t₀ t u κ * f u

/-- Continuity in the source position includes the kernel diagonal. -/
theorem cuspGreen_continuous_source (t₀ t : ℝ) (κ : ℂ) :
    Continuous (fun u : ℝ => cuspGreen t₀ t u κ) := by
  by_cases hκ : κ = 0
  · subst κ
    simp only [cuspGreen_zero]
    fun_prop
  · simp_rw [cuspGreen_eq_quotient t₀ t _ hκ]
    fun_prop

/-- Every continuous compact source produces a genuinely integrable kernel product. -/
theorem cuspGreenSolution_integrable (t₀ t : ℝ) (κ : ℂ) {f : ℝ → ℂ}
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    Integrable (fun u : ℝ => cuspGreen t₀ t u κ * f u) :=
  ((cuspGreen_continuous_source t₀ t κ).mul hf).integrable_of_hasCompactSupport
    hfc.mul_left

/-- Ordinary integrability on the physical half-line follows by restriction. -/
theorem cuspGreenSolution_integrableOn (t₀ t : ℝ) (κ : ℂ) {f : ℝ → ℂ}
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    IntegrableOn (fun u : ℝ => cuspGreen t₀ t u κ * f u) (Ioi t₀) :=
  (cuspGreenSolution_integrable t₀ t κ hf hfc).integrableOn

/-- The actual Green integral obeys its Dirichlet boundary value. -/
@[simp] theorem cuspGreenSolution_boundary (t₀ : ℝ) (κ : ℂ) (f : ℝ → ℂ) :
    cuspGreenSolution t₀ κ f t₀ = 0 := by
  unfold cuspGreenSolution
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro u hu
  rw [cuspGreen_boundary_left t₀ u hu.le, zero_mul]

/-- Cutting above the actual support changes no half-line integral. -/
theorem cuspGreenSolution_eq_interval (t₀ T t : ℝ) (hT : t₀ ≤ T) (κ : ℂ)
    {f : ℝ → ℂ} (hfT : ∀ u, T < u → f u = 0) :
    cuspGreenSolution t₀ κ f t =
      ∫ u : ℝ in t₀..T, cuspGreen t₀ t u κ * f u := by
  rw [intervalIntegral.integral_of_le hT]
  unfold cuspGreenSolution
  apply (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (show Ioc t₀ T ⊆ Ioi t₀ from fun _ hu => hu.1) ?_)
  intro u hu
  have huT : T < u := by
    have hn : ¬ (t₀ < u ∧ u ≤ T) := hu.2
    exact lt_of_not_ge (fun h => hn ⟨hu.1, h⟩)
  rw [hfT u huT, mul_zero]

/-- Compact support gives a cutoff above any requested position. -/
theorem exists_cuspSource_cutoff {f : ℝ → ℂ} (hfc : HasCompactSupport f) (L : ℝ) :
    ∃ T : ℝ, L < T ∧ ∀ u : ℝ, T < u → f u = 0 := by
  obtain ⟨B, hB⟩ := hfc.isCompact.bddAbove
  refine ⟨max B L + 1, by linarith [le_max_right B L], ?_⟩
  intro u hu
  by_contra hfu
  have hub : u ≤ B := hB (subset_tsupport f hfu)
  linarith [le_max_left B L]

end GapFamily.Analytic
