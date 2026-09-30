import GapFamily.Analytic.Modular.Geometry.ModularSeamTruncatedEnergy
import GapFamily.Analytic.Modular.ModularGradientLowCut
import GapFamily.Analytic.Modular.Elliptic.ModularUpperCutoffGradient

/-!
# Bounded-height control of actual upper-cutoff gradients

A compact upper chart is covered by finitely many translates of one truncated
fundamental domain. Invariance of the full frame energy and cancellation of
the hyperbolic area density therefore bound the ordinary cutoff gradient by
the actual two-component modular gradient below one finite height.
-/

noncomputable section
namespace GapFamily.Analytic.ModularGradient
open Set MeasureTheory UpperHalfPlane
open scoped ContDiff

/-- Ordinary derivative energy on a compact upper chart only uses a finite
height part of the actual modular frame gradient. -/
theorem exists_compact_euclideanEnergy_lowCut_bound {K : Set ℂ}
    (hK : IsCompact K) (hKU : K ⊆ upperHalfPlaneSet) :
    ∃ H : ℝ, 1 ≤ H ∧ ∃ N : ℕ, ∀ F : smoothCore,
      IntegrableOn (euclideanEnergy F.val) K volume ∧
      (∫ z in K, euclideanEnergy F.val z) ≤
        (N : ℝ) * ‖gradientLowCut H (coreGradient F)‖ ^ 2 := by
  obtain ⟨H, hH, N, hN⟩ := exists_compact_truncated_frameEnergy_bound
    (isCompact_coe_preimage_of_subset_upperHalfPlane hK hKU)
  refine ⟨H, hH, N, fun F => ?_⟩
  have heq : (fun τ : UpperHalfPlane => τ.im ^ 2 * euclideanEnergy F.val τ) =
      frameEnergy F.val := by
    funext τ
    exact (frameEnergy_eq_im_sq_mul F.val τ).symm
  have hi : IntegrableOn (fun τ : UpperHalfPlane =>
      τ.im ^ 2 * euclideanEnergy F.val τ) (UpperHalfPlane.coe ⁻¹' K) volume := by
    rw [heq]
    exact (hN F).1
  refine ⟨(upperHalfPlane_integrableOn_im_sq_mul_iff hK.measurableSet hKU _).mp hi, ?_⟩
  rw [← upperHalfPlane_setIntegral_im_sq_mul hK.measurableSet hKU, heq,
    gradientLowCut_coreGradient_norm_sq]
  exact (hN F).2

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

/-- One finite height works simultaneously for every derivative direction. -/
theorem exists_upperCutoffGradientCoreMap_lowCut_bound {χ : ℂ → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet) :
    ∃ H : ℝ, 1 ≤ H ∧ ∀ v : ℂ, ∃ B : ℝ, 0 < B ∧ ∀ F : smoothCore,
      ‖upperCutoffGradientCoreMap χ hχ hc hs v F‖ ≤
        B * ‖gradientLowCut H (coreGradient F)‖ := by
  obtain ⟨A, hA, hb⟩ := exists_upperCutoff_coefficient_bound hχ hc
  obtain ⟨H, hH, N, hlocal⟩ := exists_compact_euclideanEnergy_lowCut_bound hc hs
  refine ⟨H, hH, fun v => ?_⟩
  let D : ℝ := 2 * A ^ 2 * ‖v‖ ^ 2 * (N : ℝ)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hDb : D ≤ (D + 1) ^ 2 := by nlinarith [sq_nonneg D]
  refine ⟨D + 1, by positivity, fun F => ?_⟩
  obtain ⟨hint, hbound⟩ := hlocal F
  have hI : (∫ z : ℂ, ‖χ z * fderiv ℝ F.val z v‖ ^ 2) ≤
      D * ‖gradientLowCut H (coreGradient F)‖ ^ 2 := by
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
        exact cutoff_derivative_sq_le hA.le (fun z hz => (hb z hz).1) F v hz
      _ = (2 * A ^ 2 * ‖v‖ ^ 2) * ∫ z in tsupport χ, euclideanEnergy F.val z :=
        integral_const_mul _ _
      _ ≤ (2 * A ^ 2 * ‖v‖ ^ 2) *
          ((N : ℝ) * ‖gradientLowCut H (coreGradient F)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = D * ‖gradientLowCut H (coreGradient F)‖ ^ 2 := by dsimp [D]; ring
  have hsq : ‖upperCutoffGradientCoreMap χ hχ hc hs v F‖ ^ 2 ≤
      ((D + 1) * ‖gradientLowCut H (coreGradient F)‖) ^ 2 := by
    rw [upperCutoffGradientCoreMap_norm_sq]
    calc
      _ ≤ D * ‖gradientLowCut H (coreGradient F)‖ ^ 2 := hI
      _ ≤ (D + 1) ^ 2 * ‖gradientLowCut H (coreGradient F)‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hDb (sq_nonneg _)
      _ = _ := by ring
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsq

/-- The bounded-height estimate passes to every element of the actual closed
form domain, using its proved smooth-core density. -/
theorem exists_upperCutoffGradientOperator_lowCut_bound {χ : ℂ → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet) :
    ∃ H : ℝ, 1 ≤ H ∧ ∀ v : ℂ, ∃ B : ℝ, 0 < B ∧ ∀ u : FormDomain,
      ‖upperCutoffGradientOperator χ hχ hc hs v u‖ ≤
        B * ‖gradientLowCut H (formGradient u)‖ := by
  obtain ⟨H, hH, hbound⟩ := exists_upperCutoffGradientCoreMap_lowCut_bound hχ hc hs
  refine ⟨H, hH, fun v => ?_⟩
  obtain ⟨B, hB, hb⟩ := hbound v
  refine ⟨B, hB, fun u => ?_⟩
  refine coreForm_denseRange.induction_on (p := fun u : FormDomain =>
    ‖upperCutoffGradientOperator χ hχ hc hs v u‖ ≤
      B * ‖gradientLowCut H (formGradient u)‖) u ?_ ?_
  · exact isClosed_le (upperCutoffGradientOperator χ hχ hc hs v).continuous.norm
      (continuous_const.mul ((gradientLowCut H).continuous.comp formGradient.continuous).norm)
  · intro F
    simpa only [upperCutoffGradientOperator_coreForm, formGradient_coreForm] using hb F

end GapFamily.Analytic.ModularGradient
