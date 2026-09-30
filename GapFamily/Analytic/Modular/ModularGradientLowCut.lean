import GapFamily.Analytic.Modular.Geometry.ModularTruncatedIndicator
import GapFamily.Analytic.Modular.Geometry.ModularSeamMeasure

/-!
# Literal low-height truncation of the modular gradient

Both frame components are cut by the same actual height indicator. The Hilbert
norm on their product is therefore the integral of frame energy over that band.
-/

noncomputable section

namespace GapFamily.Analytic.ModularGradient

open Set MeasureTheory UpperHalfPlane

/-- Low-height truncation of both components in the actual gradient Hilbert space. -/
def gradientLowCut (H : ℝ) : GradientSpace →L[ℂ] GradientSpace :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ ModularHilbert ModularHilbert).symm.toContinuousLinearMap.comp
    (((modularLowCut H).prodMap (modularLowCut H)).comp
      (WithLp.prodContinuousLinearEquiv 2 ℂ ModularHilbert ModularHilbert).toContinuousLinearMap)

theorem gradientLowCut_apply (H : ℝ) (g : GradientSpace) :
    gradientLowCut H g = WithLp.toLp 2
      (modularLowCut H (WithLp.ofLp g).1, modularLowCut H (WithLp.ofLp g).2) := rfl

@[simp] theorem gradientLowCut_fst (H : ℝ) (g : GradientSpace) :
    (WithLp.ofLp (gradientLowCut H g)).1 = modularLowCut H (WithLp.ofLp g).1 := rfl

@[simp] theorem gradientLowCut_snd (H : ℝ) (g : GradientSpace) :
    (WithLp.ofLp (gradientLowCut H g)).2 = modularLowCut H (WithLp.ofLp g).2 := rfl

theorem norm_gradientLowCut_le (H : ℝ) (g : GradientSpace) :
    ‖gradientLowCut H g‖ ≤ ‖g‖ := by
  have hx := norm_modularLowCut_le H (WithLp.ofLp g).1
  have hy := norm_modularLowCut_le H (WithLp.ofLp g).2
  have hg := WithLp.prod_norm_sq_eq_of_L2 g
  have hc := WithLp.prod_norm_sq_eq_of_L2 (gradientLowCut H g)
  change ‖g‖ ^ 2 = ‖(WithLp.ofLp g).1‖ ^ 2 + ‖(WithLp.ofLp g).2‖ ^ 2 at hg
  change ‖gradientLowCut H g‖ ^ 2 =
    ‖modularLowCut H (WithLp.ofLp g).1‖ ^ 2 +
      ‖modularLowCut H (WithLp.ofLp g).2‖ ^ 2 at hc
  nlinarith [norm_nonneg g, norm_nonneg (gradientLowCut H g),
    norm_nonneg ((WithLp.ofLp g).1), norm_nonneg ((WithLp.ofLp g).2),
    norm_nonneg (modularLowCut H (WithLp.ofLp g).1),
    norm_nonneg (modularLowCut H (WithLp.ofLp g).2)]

theorem gradientLowCut_norm_le_one (H : ℝ) : ‖gradientLowCut H‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro g
  simpa only [one_mul] using norm_gradientLowCut_le H g

/-- The scalar low cut has exactly its ordinary restricted squared-norm integral. -/
theorem modularLowCut_norm_sq (H : ℝ) (f : ModularHilbert) :
    ‖modularLowCut H f‖ ^ 2 =
      ∫ τ in {τ : UpperHalfPlane | τ.im ≤ H}, ‖f τ‖ ^ 2 ∂modularMeasure := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  rw [← integral_indicator (measurableSet_lowCusp H)]
  apply integral_congr_ae
  filter_upwards [modularLowCut_ae H f] with τ hτ
  rw [hτ, real_inner_self_eq_norm_sq]
  by_cases ht : τ.im ≤ H <;> simp [ht]

theorem modularLowCut_component_norm_sq (H : ℝ) (v : ℂ)
    (hmem : ∀ F : smoothCore, MemLp (directional F.val v) 2 modularMeasure) (F : smoothCore) :
    ‖modularLowCut H (component v hmem F)‖ ^ 2 =
      ∫ τ in {τ : UpperHalfPlane | τ.im ≤ H},
        ‖directional F.val v τ‖ ^ 2 ∂modularMeasure := by
  rw [modularLowCut_norm_sq]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (component_ae v hmem F)] with τ hτ
  rw [hτ]

/-- The actual truncated gradient norm is the physical frame-energy integral. -/
theorem gradientLowCut_coreGradient_norm_sq (H : ℝ) (F : smoothCore) :
    ‖gradientLowCut H (coreGradient F)‖ ^ 2 =
      ∫ τ in {τ : UpperHalfPlane | τ.im ≤ H}, frameEnergy F.val τ ∂modularMeasure := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  change ‖modularLowCut H (xComponent F)‖ ^ 2 +
    ‖modularLowCut H (yComponent F)‖ ^ 2 = _
  unfold xComponent yComponent
  rw [modularLowCut_component_norm_sq H 1 (fun G => G.property.2.2.2.1),
    modularLowCut_component_norm_sq H Complex.I (fun G => G.property.2.2.2.2)]
  exact (integral_add
    ((memLp_two_iff_integrable_sq_norm F.property.2.2.2.1.aestronglyMeasurable).mp
      F.property.2.2.2.1).integrableOn
    ((memLp_two_iff_integrable_sq_norm F.property.2.2.2.2.aestronglyMeasurable).mp
      F.property.2.2.2.2).integrableOn).symm

end GapFamily.Analytic.ModularGradient
