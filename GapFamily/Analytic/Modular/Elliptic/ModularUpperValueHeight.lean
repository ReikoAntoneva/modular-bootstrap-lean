import GapFamily.Analytic.Modular.Elliptic.ModularUpperHilbertValue
import GapFamily.Analytic.Modular.Geometry.ModularSeamTruncatedEnergy
import GapFamily.Analytic.Modular.ModularGradientLowCut

/-!
# Finite-height dependence of actual upper cutoff values

A compact ordinary upper-half-plane cutoff sees only a finite-height portion
of the modular value. The estimate uses the actual finite cover by truncated
modular tiles and then extends from smooth values by their proved density.
-/

noncomputable section

namespace GapFamily.Analytic.ModularGradient

open Set MeasureTheory UpperHalfPlane
open scoped ContDiff

/-- The low-height mass of an actual smooth value is its restricted ordinary integral. -/
theorem modularLowCut_value_norm_sq (H : ℝ) (F : smoothCore) :
    ‖modularLowCut H (value F)‖ ^ 2 =
      ∫ τ in {τ : UpperHalfPlane | τ.im ≤ H}, ‖F.val τ‖ ^ 2 ∂modularMeasure := by
  rw [modularLowCut_norm_sq]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (value_ae F)] with τ hτ
  rw [hτ]

/-- One truncated modular mass controls the height-weighted mass on a compact
upper-half-plane set, including compact sets crossing modular seams. -/
theorem exists_compact_truncated_weightedValueEnergy_bound
    {K : Set UpperHalfPlane} (hK : IsCompact K) :
    ∃ H : ℝ, 1 ≤ H ∧ ∃ C : ℝ, 0 < C ∧ ∀ F : smoothCore,
      IntegrableOn (fun τ : UpperHalfPlane => τ.im ^ 2 * ‖F.val τ‖ ^ 2) K volume ∧
      (∫ τ in K, τ.im ^ 2 * ‖F.val τ‖ ^ 2) ≤ C * ‖modularLowCut H (value F)‖ ^ 2 := by
  obtain ⟨H, hH, N, hN⟩ := exists_modular_compact_truncated_integral_bound hK
  obtain ⟨B₀, hB₀⟩ := hK.exists_bound_of_continuousOn
    (UpperHalfPlane.continuous_im.pow 2).continuousOn
  let B : ℝ := max 1 B₀
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hy (τ : UpperHalfPlane) (hτ : τ ∈ K) : τ.im ^ 2 ≤ B :=
    (le_abs_self _).trans ((hB₀ τ hτ).trans (le_max_right _ _))
  refine ⟨H, hH, B * ((N : ℝ) + 1), by positivity, fun F => ?_⟩
  have hmass := hN (fun τ => ‖F.val τ‖ ^ 2) (fun τ => sq_nonneg _)
    (integrable_valueEnergy F) (fun γ τ => by rw [F.property.2.1 γ τ])
  rw [← modularLowCut_value_norm_sq] at hmass
  have hc : Continuous (fun τ : UpperHalfPlane => τ.im ^ 2 * ‖F.val τ‖ ^ 2) :=
    (UpperHalfPlane.continuous_im.pow 2).mul
      ((F.property.1.continuousOn.norm.pow 2).comp_continuous
        UpperHalfPlane.continuous_coe (fun τ => τ.im_pos))
  have hi : IntegrableOn (fun τ : UpperHalfPlane => τ.im ^ 2 * ‖F.val τ‖ ^ 2)
      K volume := hc.continuousOn.integrableOn_compact hK
  have hscaled : IntegrableOn (fun τ : UpperHalfPlane => B * ‖F.val τ‖ ^ 2)
      K volume := hmass.1.const_mul B
  have hmono : (∫ τ in K, τ.im ^ 2 * ‖F.val τ‖ ^ 2) ≤
      ∫ τ in K, B * ‖F.val τ‖ ^ 2 := by
    apply integral_mono_ae hi hscaled
    filter_upwards [ae_restrict_mem hK.measurableSet] with τ hτ
    exact mul_le_mul_of_nonneg_right (hy τ hτ) (sq_nonneg _)
  rw [integral_const_mul] at hmono
  refine ⟨hi, hmono.trans ?_⟩
  calc
    _ ≤ B * ((N : ℝ) * ‖modularLowCut H (value F)‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hmass.2 hB.le
    _ ≤ _ := by nlinarith [mul_nonneg hB.le (sq_nonneg ‖modularLowCut H (value F)‖)]

/-- Compact ordinary area mass depends only on a finite-height modular mass. -/
theorem exists_compact_truncated_euclideanValueEnergy_bound {K : Set ℂ}
    (hK : IsCompact K) (hKU : K ⊆ upperHalfPlaneSet) :
    ∃ H : ℝ, 1 ≤ H ∧ ∃ C : ℝ, 0 < C ∧ ∀ F : smoothCore,
      IntegrableOn (fun z : ℂ => ‖F.val z‖ ^ 2) K volume ∧
      (∫ z in K, ‖F.val z‖ ^ 2) ≤ C * ‖modularLowCut H (value F)‖ ^ 2 := by
  obtain ⟨H, hH, C, hC, hF⟩ := exists_compact_truncated_weightedValueEnergy_bound
    (isCompact_coe_preimage_of_subset_upperHalfPlane hK hKU)
  refine ⟨H, hH, C, hC, fun F => ?_⟩
  have hupper : ∀ z ∈ K, 0 < z.im := fun z hz => hKU hz
  refine ⟨(upperHalfPlane_integrableOn_im_sq_mul_iff hK.measurableSet hupper _).mp (hF F).1,
    ?_⟩
  rw [← upperHalfPlane_setIntegral_im_sq_mul hK.measurableSet hupper]
  exact (hF F).2

/-- One low-height modular norm controls the cutoff on every smooth core value. -/
theorem exists_upperCutoffValueOperator_lowCut_bound {χ : ℂ → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet) :
    ∃ H : ℝ, 1 ≤ H ∧ ∃ B : ℝ, 0 < B ∧ ∀ F : smoothCore,
      ‖upperCutoffValueOperator χ hχ hc hs (coreForm F)‖ ≤
        B * ‖modularLowCut H (value F)‖ := by
  obtain ⟨A, hA, hb⟩ := exists_upperCutoff_coefficient_bound hχ hc
  obtain ⟨H, hH, C, hC, hlocal⟩ := exists_compact_truncated_euclideanValueEnergy_bound hc hs
  let B : ℝ := A * (C + 1)
  have hB : 0 < B := by dsimp [B]; positivity
  have hcoef : A ^ 2 * C ≤ B ^ 2 := by
    calc
      _ ≤ A ^ 2 * (C + 1) ^ 2 :=
        mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg C]) (sq_nonneg A)
      _ = _ := by dsimp [B]; ring
  refine ⟨H, hH, B, hB, fun F => ?_⟩
  obtain ⟨hi, hbound⟩ := hlocal F
  have hsq : ‖upperCutoffValueOperator χ hχ hc hs (coreForm F)‖ ^ 2 ≤
      (B * ‖modularLowCut H (value F)‖) ^ 2 := by
    calc
      _ = ∫ z in tsupport χ, ‖χ z * F.val z‖ ^ 2 :=
        upperCutoffValueOperator_coreForm_norm_sq χ hχ hc hs F
      _ ≤ ∫ z in tsupport χ, A ^ 2 * ‖F.val z‖ ^ 2 := by
        apply integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun _ => sq_nonneg _) (hi.const_mul _)
        filter_upwards [ae_restrict_mem (isClosed_tsupport χ).measurableSet] with z hz
        rw [norm_mul, mul_pow]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (norm_nonneg _) (hb z hz).1 2) (sq_nonneg _)
      _ = A ^ 2 * ∫ z in tsupport χ, ‖F.val z‖ ^ 2 := integral_const_mul _ _
      _ ≤ A ^ 2 * (C * ‖modularLowCut H (value F)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hbound (sq_nonneg A)
      _ ≤ (B * ‖modularLowCut H (value F)‖) ^ 2 := by
        rw [← mul_assoc, mul_pow]
        exact mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hB.le (norm_nonneg _))).mp hsq

/-- The same localized bound holds for every actual modular Hilbert value. -/
theorem exists_upperCutoffHilbertValueOperator_lowCut_bound {χ : ℂ → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet) :
    ∃ H : ℝ, 1 ≤ H ∧ ∃ B : ℝ, 0 < B ∧ ∀ f : ModularHilbert,
      ‖upperCutoffHilbertValueOperator χ hχ hc hs f‖ ≤ B * ‖modularLowCut H f‖ := by
  obtain ⟨H, hH, B, hB, hbound⟩ := exists_upperCutoffValueOperator_lowCut_bound hχ hc hs
  refine ⟨H, hH, B, hB, fun f => ?_⟩
  have hd : DenseRange value := by
    simpa only [DenseRange, LinearMap.coe_range] using value_dense_range
  refine hd.induction_on (p := fun f : ModularHilbert =>
    ‖upperCutoffHilbertValueOperator χ hχ hc hs f‖ ≤ B * ‖modularLowCut H f‖) f ?_ ?_
  · exact isClosed_le (upperCutoffHilbertValueOperator χ hχ hc hs).continuous.norm
      (continuous_const.mul (modularLowCut H).continuous.norm)
  · intro F
    rw [upperCutoffHilbertValueOperator_value]
    exact hbound F

/-- Compact upper cutoff values are unchanged when their modular input is
first restricted below one finite logarithmic height. -/
theorem exists_upperCutoffHilbertValueOperator_lowCut {χ : ℂ → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet) :
    ∃ L : ℝ, 0 ≤ L ∧
      (upperCutoffHilbertValueOperator χ hχ hc hs).comp (modularLowCut (Real.exp L)) =
        upperCutoffHilbertValueOperator χ hχ hc hs := by
  obtain ⟨H, hH, B, hB, hbound⟩ := exists_upperCutoffHilbertValueOperator_lowCut_bound hχ hc hs
  refine ⟨Real.log H, Real.log_nonneg hH, ?_⟩
  rw [Real.exp_log (lt_of_lt_of_le zero_lt_one hH)]
  apply ContinuousLinearMap.ext
  intro f
  have hz : upperCutoffHilbertValueOperator χ hχ hc hs (f - modularLowCut H f) = 0 := by
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    simpa only [map_sub, modularLowCut_idempotent, sub_self, norm_zero, mul_zero]
      using hbound (f - modularLowCut H f)
  rw [map_sub, sub_eq_zero] at hz
  exact hz.symm

end GapFamily.Analytic.ModularGradient
