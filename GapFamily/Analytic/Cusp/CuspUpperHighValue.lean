import GapFamily.Analytic.Cusp.CuspThreeTileCover
import GapFamily.Analytic.Cusp.CuspHighTileIntegral
import GapFamily.Analytic.Modular.Elliptic.ModularUpperValueHeight
import GapFamily.Analytic.Cusp.MeanZero.CuspMeanZeroFormTruncation

noncomputable section
namespace GapFamily.Analytic.CuspUpperHighValue
open Set MeasureTheory UpperHalfPlane ModularGradient
open CuspThreeTileCover CuspHighTileIntegral
open scoped ContDiff MatrixGroups Pointwise

/-- The literal high projection has its genuine restricted squared-mass integral. -/
theorem modularHighCut_norm_sq (H : ℝ) (f : ModularHilbert) :
    ‖modularHighCut H f‖ ^ 2 =
      ∫ τ in {τ : UpperHalfPlane | H < τ.im}, ‖f τ‖ ^ 2 ∂modularMeasure := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  rw [← integral_indicator (measurableSet_highCusp H)]
  apply integral_congr_ae
  filter_upwards [modularHighCut_ae H f] with τ hτ
  rw [hτ, real_inner_self_eq_norm_sq]
  by_cases ht : H < τ.im <;> simp [ht]

theorem modularHighCut_value_norm_sq (H : ℝ) (F : smoothCore) :
    ‖modularHighCut H (value F)‖ ^ 2 =
      ∫ τ in {τ : UpperHalfPlane | H < τ.im}, ‖F.val τ‖ ^ 2 ∂modularMeasure := by
  rw [modularHighCut_norm_sq]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (value_ae F)] with τ hτ
  rw [hτ]

/-- Exact restriction of the reference measure to the high closed fundamental piece. -/
theorem integral_high_fd (H : ℝ) (g : UpperHalfPlane → ℝ) :
    (∫ τ in {τ : UpperHalfPlane | τ ∈ ModularGroup.fd ∧ H < τ.im}, g τ) =
      ∫ τ in {τ : UpperHalfPlane | H < τ.im}, g τ ∂modularMeasure := by
  rw [modularMeasure, Measure.restrict_restrict (measurableSet_highCusp H)]
  have hset : {τ : UpperHalfPlane | τ ∈ ModularGroup.fd ∧ H < τ.im} =
      {τ : UpperHalfPlane | H < τ.im} ∩ ModularGroup.fd := by
    ext τ
    exact and_comm
  rw [hset]

/-- The same three genuine translation tiles control all high-cusp local masses. -/
theorem high_value_mass (H : ℝ) (hH : 1 ≤ H) {K : Set UpperHalfPlane}
    (hK : K ⊆ {τ : UpperHalfPlane | |τ.re| ≤ 1 ∧ H < τ.im}) (F : smoothCore) :
    IntegrableOn (fun τ : UpperHalfPlane => ‖F.val τ‖ ^ 2) K volume ∧
      (∫ τ in K, ‖F.val τ‖ ^ 2) ≤ 3 * ‖modularHighCut H (value F)‖ ^ 2 := by
  have hcover := hK.trans (cuspThreeTiles_cover H hH)
  have h := modular_integral_bound_of_finite_subtile_cover
    (S := {τ : UpperHalfPlane | τ ∈ ModularGroup.fd ∧ H < τ.im})
    (fun _ hτ => hτ.1) cuspThreeTiles hcover (fun τ => ‖F.val τ‖ ^ 2)
    (fun _ => sq_nonneg _) (integrable_valueEnergy F)
    (fun γ τ => by rw [F.property.2.1 γ τ])
  rw [integral_high_fd, ← modularHighCut_value_norm_sq] at h
  refine ⟨h.1, h.2.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast cuspThreeTiles_card_le) (sq_nonneg _)

/-- The actual smooth-core cutoff norm depends only on the genuine high-height mass.
The constant is explicit and uniform over the height and the cutoff. -/
theorem upperCutoffValueOperator_core_high_norm_sq_le
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet) (H : ℝ) (hH : 1 ≤ H)
    (hwindow : ∀ z ∈ tsupport χ, |z.re| ≤ 1 ∧ H < z.im)
    (B : ℝ) (_hB : 0 ≤ B) (hb : ∀ z ∈ tsupport χ, z.im * ‖χ z‖ ≤ B)
    (F : smoothCore) :
    ‖upperCutoffValueOperator χ hχ hc hs (coreForm F)‖ ^ 2 ≤
      3 * B ^ 2 * ‖modularHighCut H (value F)‖ ^ 2 := by
  have hm := high_value_mass H hH
    (K := UpperHalfPlane.coe ⁻¹' tsupport χ) (fun τ hτ => hwindow τ hτ) F
  rw [upperCutoffValueOperator_coreForm_norm_sq,
    ← upperHalfPlane_setIntegral_im_sq_mul (isClosed_tsupport χ).measurableSet
      (fun z hz => hs hz)]
  calc
    _ ≤ ∫ τ in UpperHalfPlane.coe ⁻¹' tsupport χ, B ^ 2 * ‖F.val τ‖ ^ 2 := by
      apply integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun τ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
        (hm.1.const_mul _)
      filter_upwards [ae_restrict_mem ((isClosed_tsupport χ).measurableSet.preimage
        UpperHalfPlane.continuous_coe.measurable)] with τ hτ
      rw [norm_mul, mul_pow]
      have hh := pow_le_pow_left₀ (mul_nonneg τ.im_pos.le (norm_nonneg _)) (hb τ hτ) 2
      rw [mul_pow] at hh
      nlinarith [mul_le_mul_of_nonneg_right hh (sq_nonneg ‖F.val τ‖)]
    _ = B ^ 2 * ∫ τ in UpperHalfPlane.coe ⁻¹' tsupport χ, ‖F.val τ‖ ^ 2 :=
      integral_const_mul _ _
    _ ≤ B ^ 2 * (3 * ‖modularHighCut H (value F)‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hm.2 (sq_nonneg B)
    _ = _ := by ring

/-- The explicit high-mass estimate extends to every actual modular Hilbert vector. -/
theorem upperCutoffHilbertValueOperator_high_norm_sq_le
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet) (H : ℝ) (hH : 1 ≤ H)
    (hwindow : ∀ z ∈ tsupport χ, |z.re| ≤ 1 ∧ H < z.im)
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ z ∈ tsupport χ, z.im * ‖χ z‖ ≤ B)
    (f : ModularHilbert) :
    ‖upperCutoffHilbertValueOperator χ hχ hc hs f‖ ^ 2 ≤
      3 * B ^ 2 * ‖modularHighCut H f‖ ^ 2 := by
  have hd : DenseRange value := by
    simpa only [DenseRange, LinearMap.coe_range] using value_dense_range
  refine hd.induction_on (p := fun f : ModularHilbert =>
    ‖upperCutoffHilbertValueOperator χ hχ hc hs f‖ ^ 2 ≤
      3 * B ^ 2 * ‖modularHighCut H f‖ ^ 2) f ?_ ?_
  · exact isClosed_le ((upperCutoffHilbertValueOperator χ hχ hc hs).continuous.norm.pow 2)
      (continuous_const.mul ((modularHighCut H).continuous.norm.pow 2))
  · intro F
    rw [upperCutoffHilbertValueOperator_value]
    exact upperCutoffValueOperator_core_high_norm_sq_le χ hχ hc hs H hH hwindow B hB hb F

end GapFamily.Analytic.CuspUpperHighValue
