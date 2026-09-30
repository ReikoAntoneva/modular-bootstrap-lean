import GapFamily.Analytic.Modular.Geometry.ModularSeamEnergy
import Mathlib.MeasureTheory.Group.Integral

/-!
# Energy transport to actual closed modular tiles

Hyperbolic volume preservation transfers integrability as well as the value
of each integral. These are closed fundamental-domain tiles, so this argument
does not remove their seam points from a purported neighborhood cover.
-/

noncomputable section

namespace GapFamily.Analytic

open Set MeasureTheory UpperHalfPlane
open scoped MatrixGroups Pointwise

theorem measurePreserving_modularAction (γ : SL(2, ℤ)) :
    MeasurePreserving (fun τ : UpperHalfPlane => γ • τ) volume volume := by
  simpa only [ModularGroup.sl_moeb] using
    (measurePreserving_smul (γ : GL (Fin 2) ℝ) (volume : Measure UpperHalfPlane))

theorem measurableEmbedding_modularAction (γ : SL(2, ℤ)) :
    MeasurableEmbedding (fun τ : UpperHalfPlane => γ • τ) := by
  simpa only [ModularGroup.sl_moeb] using
    (measurableEmbedding_const_smul (α := UpperHalfPlane) (γ : GL (Fin 2) ℝ))

/-- Ordinary integrability transfers to a closed modular translate for every
invariant function. -/
theorem integrableOn_modular_translate_of_invariant {g : UpperHalfPlane → ℝ}
    (hg : Integrable g modularMeasure)
    (hinv : ∀ γ : SL(2, ℤ), ∀ τ : UpperHalfPlane, g (γ • τ) = g τ)
    (γ : SL(2, ℤ)) : IntegrableOn g (γ • ModularGroup.fd) volume := by
  have he := measurableEmbedding_modularAction γ
  have hm := (measurePreserving_modularAction γ).restrict_image_emb he ModularGroup.fd
  apply (hm.integrable_comp_emb he).mp
  simpa only [Function.comp_def, hinv γ, modularMeasure] using! hg

/-- The ordinary integral on every closed modular tile is exactly its value
on the actual chosen fundamental domain. -/
theorem integral_modular_translate_of_invariant (g : UpperHalfPlane → ℝ)
    (hinv : ∀ γ : SL(2, ℤ), ∀ τ : UpperHalfPlane, g (γ • τ) = g τ)
    (γ : SL(2, ℤ)) :
    (∫ τ in γ • ModularGroup.fd, g τ) = ∫ τ, g τ ∂modularMeasure := by
  rw [← Set.image_smul, (measurePreserving_modularAction γ).setIntegral_image_emb
    (measurableEmbedding_modularAction γ) g ModularGroup.fd]
  simp only [hinv γ, modularMeasure]

namespace ModularGradient

theorem integrable_valueEnergy (F : smoothCore) :
    Integrable (fun τ : UpperHalfPlane => ‖F.val τ‖ ^ 2) modularMeasure :=
  (memLp_two_iff_integrable_sq_norm F.property.2.2.1.aestronglyMeasurable).mp F.property.2.2.1

theorem integral_valueEnergy_eq_norm_sq (F : smoothCore) :
    (∫ τ : UpperHalfPlane, ‖F.val τ‖ ^ 2 ∂modularMeasure) = ‖value F‖ ^ 2 := by
  calc
    _ = ∫ τ : UpperHalfPlane, (inner ℂ (value F τ) (value F τ)).re ∂modularMeasure := by
      apply integral_congr_ae
      filter_upwards [value_ae F] with τ hτ
      rw [hτ]
      exact norm_sq_eq_re_inner (𝕜 := ℂ) _
    _ = (∫ τ : UpperHalfPlane, inner ℂ (value F τ) (value F τ) ∂modularMeasure).re :=
      Complex.reCLM.integral_comp_comm (L2.integrable_inner (𝕜 := ℂ) (value F) (value F))
    _ = _ := by
      rw [← L2.inner_def]
      exact (norm_sq_eq_re_inner (𝕜 := ℂ) (value F)).symm

theorem integrable_frameEnergy (F : smoothCore) :
    Integrable (frameEnergy F.val) modularMeasure :=
  ((memLp_two_iff_integrable_sq_norm F.property.2.2.2.1.aestronglyMeasurable).mp
    F.property.2.2.2.1).add
      ((memLp_two_iff_integrable_sq_norm F.property.2.2.2.2.aestronglyMeasurable).mp
        F.property.2.2.2.2)

theorem integral_componentEnergy_eq_norm_sq (F : smoothCore) (v : ℂ)
    (hmem : ∀ G : smoothCore, MemLp (directional G.val v) 2 modularMeasure) :
    (∫ τ : UpperHalfPlane, ‖directional F.val v τ‖ ^ 2 ∂modularMeasure) =
      ‖component v hmem F‖ ^ 2 := by
  calc
    _ = ∫ τ : UpperHalfPlane,
        (inner ℂ (component v hmem F τ) (component v hmem F τ)).re
        ∂modularMeasure := by
      apply integral_congr_ae
      filter_upwards [component_ae v hmem F] with τ hτ
      rw [hτ]
      exact norm_sq_eq_re_inner (𝕜 := ℂ) _
    _ = (∫ τ : UpperHalfPlane,
        inner ℂ (component v hmem F τ) (component v hmem F τ)
        ∂modularMeasure).re :=
      Complex.reCLM.integral_comp_comm (L2.integrable_inner (𝕜 := ℂ)
        (component v hmem F) (component v hmem F))
    _ = _ := by
      rw [← L2.inner_def]
      exact (norm_sq_eq_re_inner (𝕜 := ℂ) (component v hmem F)).symm

theorem integral_frameEnergy_eq_norm_sq (F : smoothCore) :
    (∫ τ : UpperHalfPlane, frameEnergy F.val τ ∂modularMeasure) =
      ‖coreGradient F‖ ^ 2 := by
  change (∫ τ : UpperHalfPlane,
    ‖directional F.val 1 τ‖ ^ 2 + ‖directional F.val Complex.I τ‖ ^ 2 ∂modularMeasure) = _
  rw [integral_add
    ((memLp_two_iff_integrable_sq_norm F.property.2.2.2.1.aestronglyMeasurable).mp
      F.property.2.2.2.1)
    ((memLp_two_iff_integrable_sq_norm F.property.2.2.2.2.aestronglyMeasurable).mp
      F.property.2.2.2.2)]
  rw [integral_componentEnergy_eq_norm_sq F 1 (fun G => G.property.2.2.2.1),
    integral_componentEnergy_eq_norm_sq F Complex.I (fun G => G.property.2.2.2.2)]
  exact (WithLp.prod_norm_sq_eq_of_L2 (coreGradient F)).symm

/-- Every translated closed tile has finite actual frame energy. -/
theorem integrableOn_frameEnergy_modular_translate (F : smoothCore) (γ : SL(2, ℤ)) :
    IntegrableOn (frameEnergy F.val) (γ • ModularGroup.fd) volume :=
  integrableOn_modular_translate_of_invariant (integrable_frameEnergy F)
    (frameEnergy_modularAction F) γ

/-- Each closed tile has exactly the same full gradient energy as the actual
modular Hilbert gradient. -/
theorem integral_frameEnergy_modular_translate (F : smoothCore) (γ : SL(2, ℤ)) :
    (∫ τ in γ • ModularGroup.fd, frameEnergy F.val τ) = ‖coreGradient F‖ ^ 2 := by
  rw [integral_modular_translate_of_invariant _ (frameEnergy_modularAction F),
    integral_frameEnergy_eq_norm_sq]

end ModularGradient
end GapFamily.Analytic
