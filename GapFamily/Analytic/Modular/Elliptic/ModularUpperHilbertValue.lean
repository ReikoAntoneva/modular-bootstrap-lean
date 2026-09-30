import GapFamily.Analytic.Modular.Elliptic.ModularUpperCutoffValue
import GapFamily.Analytic.Modular.Geometry.ModularSeamCoordinate
import GapFamily.Analytic.Modular.Periodization.ModularPeriodizationDensity

/-! The ordinary upper cutoff value is bounded by the actual modular value norm alone. -/

noncomputable section

namespace GapFamily.Analytic

open Set MeasureTheory UpperHalfPlane ModularGradient

/-- Compact height weights preserve the value estimate in the modular Hilbert norm. -/
theorem exists_compact_weightedValueEnergy_bound {K : Set UpperHalfPlane}
    (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ F : smoothCore,
      IntegrableOn (fun τ : UpperHalfPlane => τ.im ^ 2 * ‖F.val τ‖ ^ 2) K volume ∧
      (∫ τ in K, τ.im ^ 2 * ‖F.val τ‖ ^ 2) ≤ C * ‖value F‖ ^ 2 := by
  obtain ⟨N, hN⟩ := exists_compact_valueEnergy_bound hK
  obtain ⟨B₀, hB₀⟩ := hK.exists_bound_of_continuousOn
    (UpperHalfPlane.continuous_im.pow 2).continuousOn
  let B : ℝ := max 1 B₀
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hy (τ : UpperHalfPlane) (hτ : τ ∈ K) : τ.im ^ 2 ≤ B :=
    (le_abs_self _).trans ((hB₀ τ hτ).trans (le_max_right _ _))
  refine ⟨B * ((N : ℝ) + 1), by positivity, fun F => ?_⟩
  have hc : Continuous (fun τ : UpperHalfPlane => τ.im ^ 2 * ‖F.val τ‖ ^ 2) :=
    (UpperHalfPlane.continuous_im.pow 2).mul
      ((F.property.1.continuousOn.norm.pow 2).comp_continuous
        UpperHalfPlane.continuous_coe (fun τ => τ.im_pos))
  have hi : IntegrableOn (fun τ : UpperHalfPlane => τ.im ^ 2 * ‖F.val τ‖ ^ 2)
      K volume := hc.continuousOn.integrableOn_compact hK
  have hscaled : IntegrableOn (fun τ : UpperHalfPlane => B * ‖F.val τ‖ ^ 2)
      K volume := (hN F).1.const_mul B
  have hmono : (∫ τ in K, τ.im ^ 2 * ‖F.val τ‖ ^ 2) ≤
      ∫ τ in K, B * ‖F.val τ‖ ^ 2 := by
    apply integral_mono_ae hi hscaled
    filter_upwards [ae_restrict_mem hK.measurableSet] with τ hτ
    exact mul_le_mul_of_nonneg_right (hy τ hτ) (sq_nonneg _)
  rw [integral_const_mul] at hmono
  refine ⟨hi, hmono.trans ?_⟩
  calc
    _ ≤ B * ((N : ℝ) * ‖value F‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (hN F).2 hB.le
    _ ≤ _ := by nlinarith [mul_nonneg hB.le (sq_nonneg ‖value F‖)]

/-- Compact ordinary area mass is controlled by the actual modular Hilbert norm,
including compact regions crossing fundamental-domain seams. -/
theorem exists_compact_euclideanValueEnergy_bound {K : Set ℂ}
    (hK : IsCompact K) (hKU : K ⊆ upperHalfPlaneSet) :
    ∃ C : ℝ, 0 < C ∧ ∀ F : smoothCore,
      IntegrableOn (fun z : ℂ => ‖F.val z‖ ^ 2) K volume ∧
      (∫ z in K, ‖F.val z‖ ^ 2) ≤ C * ‖value F‖ ^ 2 := by
  obtain ⟨C, hC, hF⟩ := exists_compact_weightedValueEnergy_bound
    (isCompact_coe_preimage_of_subset_upperHalfPlane hK hKU)
  refine ⟨C, hC, fun F => ?_⟩
  have hupper : ∀ z ∈ K, 0 < z.im := fun z hz => hKU hz
  refine ⟨(upperHalfPlane_integrableOn_im_sq_mul_iff hK.measurableSet hupper _).mp (hF F).1,
    ?_⟩
  rw [← upperHalfPlane_setIntegral_im_sq_mul hK.measurableSet hupper]
  exact (hF F).2

end GapFamily.Analytic

namespace GapFamily.Analytic.ModularGradient

open Set MeasureTheory UpperHalfPlane
open scoped ContDiff

/-- The global ordinary cutoff norm is its literal compact-support integral. -/
theorem upperCutoffValueOperator_coreForm_norm_sq
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet) (F : smoothCore) :
    ‖upperCutoffValueOperator χ hχ hc hs (coreForm F)‖ ^ 2 =
      ∫ z in tsupport χ, ‖χ z * F.val z‖ ^ 2 := by
  let : CompactSpace (tsupport χ) := isCompact_iff_compactSpace.mp hc
  change ‖LocalSobolev.zeroExtension (tsupport χ)
    (upperCutoffOperator χ hχ hc hs (tsupport χ) (coreForm F))‖ ^ 2 = _
  rw [(LocalSobolev.zeroExtension (tsupport χ)).norm_map, upperCutoffOperator_coreForm]
  exact upperCutoffCoreMap_norm_sq χ hχ hs (tsupport χ) F

/-- Cutoff multiplication is bounded by the actual modular mass norm, without
any gradient norm in the bound. -/
theorem exists_upperCutoffValueOperator_value_bound {χ : ℂ → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet) :
    ∃ B : ℝ, 0 < B ∧ ∀ F : smoothCore,
      ‖upperCutoffValueOperator χ hχ hc hs (coreForm F)‖ ≤ B * ‖value F‖ := by
  obtain ⟨A, hA, hb⟩ := exists_upperCutoff_coefficient_bound hχ hc
  obtain ⟨C, hC, hlocal⟩ := GapFamily.Analytic.exists_compact_euclideanValueEnergy_bound hc hs
  let B : ℝ := A * (C + 1)
  have hB : 0 < B := by dsimp [B]; positivity
  have hcoef : A ^ 2 * C ≤ B ^ 2 := by
    calc
      _ ≤ A ^ 2 * (C + 1) ^ 2 :=
        mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg C]) (sq_nonneg A)
      _ = _ := by dsimp [B]; ring
  refine ⟨B, hB, fun F => ?_⟩
  obtain ⟨hi, hbound⟩ := hlocal F
  have hsq : ‖upperCutoffValueOperator χ hχ hc hs (coreForm F)‖ ^ 2 ≤
      (B * ‖value F‖) ^ 2 := by
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
      _ ≤ A ^ 2 * (C * ‖value F‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hbound (sq_nonneg A)
      _ ≤ (B * ‖value F‖) ^ 2 := by
        rw [← mul_assoc, mul_pow]
        exact mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hB.le (norm_nonneg _))).mp hsq

/-- The actual compact upper cutoff value extends from modular values to all
of the modular Hilbert space, using the proved mass-only bound. -/
def upperCutoffHilbertValueOperator (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ upperHalfPlaneSet) :
    ModularHilbert →L[ℂ] Lp ℂ 2 (volume : Measure ℂ) :=
  ((upperCutoffValueOperator χ hχ hc hs).toLinearMap.comp coreForm).extendOfNorm value

/-- The Hilbert extension agrees with the existing form cutoff on every core. -/
theorem upperCutoffHilbertValueOperator_value (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ upperHalfPlaneSet) (F : smoothCore) :
    upperCutoffHilbertValueOperator χ hχ hc hs (value F) =
      upperCutoffValueOperator χ hχ hc hs (coreForm F) := by
  have hd : DenseRange value := by
    simpa only [DenseRange, LinearMap.coe_range] using value_dense_range
  obtain ⟨B, _, hB⟩ := exists_upperCutoffValueOperator_value_bound hχ hc hs
  exact LinearMap.extendOfNorm_eq hd ⟨B, hB⟩ F

/-- Literal ordinary-coordinate cutoff multiplication on actual smooth values. -/
theorem upperCutoffHilbertValueOperator_value_ae (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ upperHalfPlaneSet) (F : smoothCore) :
    upperCutoffHilbertValueOperator χ hχ hc hs (value F) =ᵐ[(volume : Measure ℂ)]
      fun z => χ z * F.val z := by
  rw [upperCutoffHilbertValueOperator_value]
  exact upperCutoffValueOperator_coreForm_ae χ hχ hc hs F

/-- The Hilbert-space lift and the form-domain cutoff are the same ordinary
local value whenever the input lies in the actual form domain. -/
theorem upperCutoffHilbertValueOperator_formEmbedding
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet) (u : FormDomain) :
    upperCutoffHilbertValueOperator χ hχ hc hs (formEmbedding u) =
      upperCutoffValueOperator χ hχ hc hs u := by
  refine coreForm_denseRange.induction_on (p := fun u : FormDomain =>
    upperCutoffHilbertValueOperator χ hχ hc hs (formEmbedding u) =
      upperCutoffValueOperator χ hχ hc hs u) u ?_ ?_
  · exact isClosed_eq
      ((upperCutoffHilbertValueOperator χ hχ hc hs).continuous.comp formEmbedding.continuous)
      (upperCutoffValueOperator χ hχ hc hs).continuous
  · intro F
    rw [formEmbedding_coreForm, upperCutoffHilbertValueOperator_value]

end GapFamily.Analytic.ModularGradient
