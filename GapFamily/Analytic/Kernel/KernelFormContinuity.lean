import GapFamily.Analytic.Elliptic.WeakKernelForm

/-!
# Controlled passage to limits in the weak kernel form

The form difference is an identity between actual, absolutely convergent
integrals. Its bound then follows from the proved weighted row estimates.
-/

namespace GapFamily.Analytic

open MeasureTheory Real
open scoped ComplexConjugate

/-- The difference of two actual pairings splits into two controlled error terms. -/
theorem weakKernelPairing_sub_eq {j J : ℤ}
    {K : ℝ × ℝ → ℂ} {f₁ f₂ g₁ g₂ : ℝ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hK : AEStronglyMeasurable K ((referenceMeasure j).prod (referenceMeasure J)))
    (hbound : ∀ᵐ p ∂(referenceMeasure j).prod (referenceMeasure J),
      ‖K p‖ ≤ C * (|(j : ℝ)| * |(J : ℝ)| + sqrt p.1 * sqrt p.2))
    (hf₁ : MemLp f₁ 2 (energySpaceMeasure j))
    (hf₂ : MemLp f₂ 2 (energySpaceMeasure j))
    (hg₁ : MemLp g₁ 2 (energySpaceMeasure J))
    (hg₂ : MemLp g₂ 2 (energySpaceMeasure J)) :
    weakKernelPairing j J K f₁ g₁ - weakKernelPairing j J K f₂ g₂ =
      weakKernelPairing j J K f₁ (g₁ - g₂) +
        weakKernelPairing j J K (f₁ - f₂) g₂ := by
  have h11 := (weakKernel_integrable_and_norm_bound hC hK hbound hf₁ hg₁).1
  have h22 := (weakKernel_integrable_and_norm_bound hC hK hbound hf₂ hg₂).1
  have h1d := (weakKernel_integrable_and_norm_bound hC hK hbound hf₁ (hg₁.sub hg₂)).1
  have hd2 := (weakKernel_integrable_and_norm_bound hC hK hbound (hf₁.sub hf₂) hg₂).1
  unfold weakKernelPairing
  rw [← integral_sub h11 h22, ← integral_add h1d hd2]
  apply integral_congr_ae
  filter_upwards with p
  simp only [weakKernelIntegrand, Pi.sub_apply, map_sub]
  ring

/-- The actual weak form is Lipschitz in each weighted `L²` input on bounded sets. -/
theorem weakKernelPairing_sub_norm_le {j J : ℤ}
    {K : ℝ × ℝ → ℂ} {f₁ f₂ g₁ g₂ : ℝ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hK : AEStronglyMeasurable K ((referenceMeasure j).prod (referenceMeasure J)))
    (hbound : ∀ᵐ p ∂(referenceMeasure j).prod (referenceMeasure J),
      ‖K p‖ ≤ C * (|(j : ℝ)| * |(J : ℝ)| + sqrt p.1 * sqrt p.2))
    (hf₁ : MemLp f₁ 2 (energySpaceMeasure j))
    (hf₂ : MemLp f₂ 2 (energySpaceMeasure j))
    (hg₁ : MemLp g₁ 2 (energySpaceMeasure J))
    (hg₂ : MemLp g₂ 2 (energySpaceMeasure J)) :
    ‖weakKernelPairing j J K f₁ g₁ - weakKernelPairing j J K f₂ g₂‖ ≤
      C * weakKernelMomentConstant j J *
        ((eLpNorm f₁ 2 (energySpaceMeasure j)).toReal *
          (eLpNorm (g₁ - g₂) 2 (energySpaceMeasure J)).toReal +
        (eLpNorm (f₁ - f₂) 2 (energySpaceMeasure j)).toReal *
          (eLpNorm g₂ 2 (energySpaceMeasure J)).toReal) := by
  rw [weakKernelPairing_sub_eq hC hK hbound hf₁ hf₂ hg₁ hg₂]
  calc
    ‖weakKernelPairing j J K f₁ (g₁ - g₂) +
        weakKernelPairing j J K (f₁ - f₂) g₂‖ ≤
      ‖weakKernelPairing j J K f₁ (g₁ - g₂)‖ +
        ‖weakKernelPairing j J K (f₁ - f₂) g₂‖ := norm_add_le _ _
    _ ≤ C * weakKernelMomentConstant j J *
        (eLpNorm f₁ 2 (energySpaceMeasure j)).toReal *
          (eLpNorm (g₁ - g₂) 2 (energySpaceMeasure J)).toReal +
      C * weakKernelMomentConstant j J *
        (eLpNorm (f₁ - f₂) 2 (energySpaceMeasure j)).toReal *
          (eLpNorm g₂ 2 (energySpaceMeasure J)).toReal :=
      add_le_add
        (weakKernel_integrable_and_norm_bound hC hK hbound hf₁ (hg₁.sub hg₂)).2
        (weakKernel_integrable_and_norm_bound hC hK hbound (hf₁.sub hf₂) hg₂).2
    _ = _ := by ring

/-- The proved difference bound applies unconditionally to the actual higher kernel. -/
theorem higherKernelPairing_sub_norm_le (j J : ℤ)
    {f₁ f₂ g₁ g₂ : ℝ → ℂ}
    (hf₁ : MemLp f₁ 2 (energySpaceMeasure j))
    (hf₂ : MemLp f₂ 2 (energySpaceMeasure j))
    (hg₁ : MemLp g₁ 2 (energySpaceMeasure J))
    (hg₂ : MemLp g₂ 2 (energySpaceMeasure J)) :
    ‖weakKernelPairing j J (fun p => higherKernel j J p.1 p.2) f₁ g₁ -
        weakKernelPairing j J (fun p => higherKernel j J p.1 p.2) f₂ g₂‖ ≤
      (64 * π ^ 2) * weakKernelMomentConstant j J *
        ((eLpNorm f₁ 2 (energySpaceMeasure j)).toReal *
          (eLpNorm (g₁ - g₂) 2 (energySpaceMeasure J)).toReal +
        (eLpNorm (f₁ - f₂) 2 (energySpaceMeasure j)).toReal *
          (eLpNorm g₂ 2 (energySpaceMeasure J)).toReal) := by
  exact weakKernelPairing_sub_norm_le (by positivity)
    (higherKernel_real_aestronglyMeasurable j J) (higherKernel_ae_weak_bound j J)
    hf₁ hf₂ hg₁ hg₂

end GapFamily.Analytic
