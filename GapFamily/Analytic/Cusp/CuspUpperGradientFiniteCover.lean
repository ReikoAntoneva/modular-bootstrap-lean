import GapFamily.Analytic.Modular.Elliptic.ModularUpperCutoffGradient
import GapFamily.Analytic.Modular.Geometry.ModularSeamCompact
import GapFamily.Analytic.Modular.Geometry.ModularSeamCoordinateMeasure

/-!
# Finite-cover control of actual upper-cutoff gradient energy

The height-square factor in the hyperbolic frame energy cancels the area
density exactly. A supplied finite closed-tile cover therefore gives a
constant depending only on its cardinality and the cutoff amplitude.
-/

noncomputable section

namespace GapFamily.Analytic.CuspUpperGradientFiniteCover

open Set MeasureTheory UpperHalfPlane ModularGradient
open scoped ContDiff MatrixGroups

/-- Ordinary derivative energy is bounded by the cardinality of an actual
finite closed modular tile cover, with no height factor. -/
theorem euclideanEnergy_bound_of_finite_cover {K : Set ℂ}
    (hK : MeasurableSet K) (hKU : K ⊆ upperHalfPlaneSet)
    (Γ : Finset SL(2, ℤ))
    (hcover : UpperHalfPlane.coe ⁻¹' K ⊆ ⋃ γ ∈ Γ, (γ • ·) '' ModularGroup.fd)
    (F : smoothCore) :
    IntegrableOn (euclideanEnergy F.val) K volume ∧
      (∫ z in K, euclideanEnergy F.val z) ≤
        (Γ.card : ℝ) * ‖coreGradient F‖ ^ 2 := by
  obtain ⟨hi, hb⟩ := modular_integral_bound_of_finite_cover Γ hcover
    (frameEnergy F.val) (fun _ => add_nonneg (sq_nonneg _) (sq_nonneg _))
    (integrable_frameEnergy F) (frameEnergy_modularAction F)
  have heq : (fun τ : UpperHalfPlane => τ.im ^ 2 * euclideanEnergy F.val τ) =
      frameEnergy F.val := by
    funext τ
    exact (frameEnergy_eq_im_sq_mul F.val τ).symm
  refine ⟨(upperHalfPlane_integrableOn_im_sq_mul_iff hK hKU _).mp
    (by simpa only [heq] using hi), ?_⟩
  rw [← upperHalfPlane_setIntegral_im_sq_mul hK hKU, heq]
  simpa only [integral_frameEnergy_eq_norm_sq] using hb

private theorem cutoff_derivative_sq_le {χ : ℂ → ℂ} {A : ℝ} (hA : 0 ≤ A)
    (hb : ∀ z ∈ tsupport χ, ‖χ z‖ ≤ A) (F : smoothCore) (v : ℂ)
    {z : ℂ} (hz : z ∈ tsupport χ) :
    ‖χ z * fderiv ℝ F.val z v‖ ^ 2 ≤
      2 * A ^ 2 * ‖v‖ ^ 2 * euclideanEnergy F.val z := by
  have hd : ‖fderiv ℝ F.val z v‖ ≤
      (‖fderiv ℝ F.val z 1‖ + ‖fderiv ℝ F.val z Complex.I‖) * ‖v‖ :=
    ((fderiv ℝ F.val z).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (complex_real_opNorm_le _) (norm_nonneg _))
  have hm : ‖χ z * fderiv ℝ F.val z v‖ ≤
      A * ((‖fderiv ℝ F.val z 1‖ + ‖fderiv ℝ F.val z Complex.I‖) * ‖v‖) := by
    rw [norm_mul]
    exact mul_le_mul (hb z hz) hd (norm_nonneg _) hA
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hm 2
  have hn : 0 ≤ A ^ 2 * ‖v‖ ^ 2 *
      (‖fderiv ℝ F.val z 1‖ - ‖fderiv ℝ F.val z Complex.I‖) ^ 2 := by positivity
  unfold euclideanEnergy
  nlinarith only [hsq, hn]

/-- The literal smooth-core cutoff gradient obeys the supplied finite-cover
bound solely in terms of the actual modular gradient energy. -/
theorem upperCutoffGradientCoreMap_norm_sq_le_of_finite_cover {χ : ℂ → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet) {A : ℝ} (hA : 0 ≤ A)
    (hb : ∀ z ∈ tsupport χ, ‖χ z‖ ≤ A)
    (Γ : Finset SL(2, ℤ))
    (hcover : UpperHalfPlane.coe ⁻¹' tsupport χ ⊆
      ⋃ γ ∈ Γ, (γ • ·) '' ModularGroup.fd) (v : ℂ) (F : smoothCore) :
    ‖upperCutoffGradientCoreMap χ hχ hc hs v F‖ ^ 2 ≤
      2 * A ^ 2 * ‖v‖ ^ 2 * (Γ.card : ℝ) * ‖coreGradient F‖ ^ 2 := by
  obtain ⟨hint, hbound⟩ := euclideanEnergy_bound_of_finite_cover
    (isClosed_tsupport χ).measurableSet hs Γ hcover F
  rw [upperCutoffGradientCoreMap_norm_sq]
  calc
    _ = ∫ z in tsupport χ, ‖χ z * fderiv ℝ F.val z v‖ ^ 2 := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro z hz
      simp [image_eq_zero_of_notMem_tsupport hz]
    _ ≤ ∫ z in tsupport χ, 2 * A ^ 2 * ‖v‖ ^ 2 * euclideanEnergy F.val z := by
      apply integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun _ => sq_nonneg _) (hint.const_mul _)
      filter_upwards [ae_restrict_mem (isClosed_tsupport χ).measurableSet] with z hz
      exact cutoff_derivative_sq_le hA hb F v hz
    _ = (2 * A ^ 2 * ‖v‖ ^ 2) * ∫ z in tsupport χ, euclideanEnergy F.val z :=
      integral_const_mul _ _
    _ ≤ (2 * A ^ 2 * ‖v‖ ^ 2) * ((Γ.card : ℝ) * ‖coreGradient F‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = _ := by ring

/-- The same explicit bound holds on the completed form domain, by the
proved density of the actual smooth modular core. -/
theorem upperCutoffGradientOperator_norm_sq_le_of_finite_cover {χ : ℂ → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet) {A : ℝ} (hA : 0 ≤ A)
    (hb : ∀ z ∈ tsupport χ, ‖χ z‖ ≤ A)
    (Γ : Finset SL(2, ℤ))
    (hcover : UpperHalfPlane.coe ⁻¹' tsupport χ ⊆
      ⋃ γ ∈ Γ, (γ • ·) '' ModularGroup.fd) (v : ℂ) (u : FormDomain) :
    ‖upperCutoffGradientOperator χ hχ hc hs v u‖ ^ 2 ≤
      2 * A ^ 2 * ‖v‖ ^ 2 * (Γ.card : ℝ) * ‖formGradient u‖ ^ 2 := by
  refine coreForm_denseRange.induction_on (p := fun u : FormDomain =>
    ‖upperCutoffGradientOperator χ hχ hc hs v u‖ ^ 2 ≤
      2 * A ^ 2 * ‖v‖ ^ 2 * (Γ.card : ℝ) * ‖formGradient u‖ ^ 2) u ?_ ?_
  · exact isClosed_le (by fun_prop) (by fun_prop)
  · intro F
    simpa only [upperCutoffGradientOperator_coreForm, formGradient_coreForm] using
      upperCutoffGradientCoreMap_norm_sq_le_of_finite_cover hχ hc hs hA hb Γ hcover v F

end GapFamily.Analytic.CuspUpperGradientFiniteCover
