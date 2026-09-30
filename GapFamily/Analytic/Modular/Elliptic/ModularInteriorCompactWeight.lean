import GapFamily.Analytic.Modular.ModularGradientCore
import GapFamily.Analytic.Elliptic.GradientLocalHyperbolic

/-!
# Exact local Euclidean energy transport

The actual inverse-square modular measure converts compact interior Euclidean
integrals to weighted modular integrals. Raw core norms are actual Hilbert norms.
-/

noncomputable section

namespace GapFamily.Analytic.ModularGradient

open Set MeasureTheory

theorem coordinate_integral_im_sq_mul (g : ℂ → ℝ) :
    (∫ z, z.im ^ 2 * g z ∂modularCoordinateMeasure) = ∫ z in modularInterior, g z := by
  rw [modularCoordinateMeasure, Dirichlet.localHyperbolicMeasure,
    integral_withDensity_eq_integral_toReal_smul
      (by fun_prop : Measurable (fun z : ℂ => ENNReal.ofReal (1 / z.im ^ 2)))
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_modularInterior] with z hz
  rw [ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
  have hn : z.im ≠ 0 := (im_pos_of_mem_modularInterior hz).ne'
  field_simp

theorem integral_eq_coordinate_weighted (g : ℂ → ℝ)
    (hs : ∀ z ∉ modularInterior, g z = 0) :
    (∫ z, g z) = ∫ z, z.im ^ 2 * g z ∂modularCoordinateMeasure := by
  rw [coordinate_integral_im_sq_mul]
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero hs).symm

theorem core_value_integral_norm_sq (F : smoothCore) :
    (∫ τ : UpperHalfPlane, ‖F.val τ‖ ^ 2 ∂modularMeasure) = ‖value F‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [value_ae F] with τ hτ
  simp only [hτ, real_inner_self_eq_norm_sq]

theorem core_component_integral_norm_sq (v : ℂ)
    (hmem : ∀ F : smoothCore, MemLp (directional F.val v) 2 modularMeasure) (F : smoothCore) :
    (∫ τ : UpperHalfPlane, ‖directional F.val v τ‖ ^ 2 ∂modularMeasure) =
      ‖component v hmem F‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [component_ae v hmem F] with τ hτ
  simp only [hτ, real_inner_self_eq_norm_sq]

theorem coordinate_core_value_integrable (F : smoothCore) :
    Integrable (fun z => ‖F.val z‖ ^ 2) modularCoordinateMeasure := by
  rw [integrable_modularCoordinate_iff]
  exact (memLp_two_iff_integrable_sq_norm F.property.2.2.1.aestronglyMeasurable).mp
    F.property.2.2.1

theorem coordinate_core_component_integrable (v : ℂ)
    (hmem : ∀ F : smoothCore, MemLp (directional F.val v) 2 modularMeasure) (F : smoothCore) :
    Integrable (fun z => ‖(z.im : ℂ) * fderiv ℝ F.val z v‖ ^ 2)
      modularCoordinateMeasure := by
  rw [integrable_modularCoordinate_iff]
  exact (memLp_two_iff_integrable_sq_norm (hmem F).aestronglyMeasurable).mp (hmem F)

theorem coordinate_core_value_integral (F : smoothCore) :
    (∫ z, ‖F.val z‖ ^ 2 ∂modularCoordinateMeasure) = ‖value F‖ ^ 2 := by
  rw [integral_modularCoordinate]
  exact core_value_integral_norm_sq F

theorem coordinate_core_component_integral (v : ℂ)
    (hmem : ∀ F : smoothCore, MemLp (directional F.val v) 2 modularMeasure) (F : smoothCore) :
    (∫ z, ‖(z.im : ℂ) * fderiv ℝ F.val z v‖ ^ 2 ∂modularCoordinateMeasure) =
      ‖component v hmem F‖ ^ 2 := by
  rw [integral_modularCoordinate]
  exact core_component_integral_norm_sq v hmem F

theorem coreGradient_norm_sq (F : smoothCore) :
    ‖coreGradient F‖ ^ 2 = ‖xComponent F‖ ^ 2 + ‖yComponent F‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 (coreGradient F)

end GapFamily.Analytic.ModularGradient
