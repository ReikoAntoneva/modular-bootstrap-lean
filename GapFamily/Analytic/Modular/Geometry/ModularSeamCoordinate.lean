import GapFamily.Analytic.Modular.Geometry.ModularSeamCompact
import GapFamily.Analytic.Modular.Geometry.ModularSeamCoordinateMeasure

/-!
# Ordinary compact coordinate energy across modular seams

Compact height bounds and exact hyperbolic density cancellation transfer the
closed-tile graph-energy estimate to ordinary area in complex coordinates.
-/

noncomputable section

namespace GapFamily.Analytic.ModularGradient

open Set MeasureTheory UpperHalfPlane

/-- Actual ordinary value plus the two Euclidean derivative energies. -/
def euclideanGraphEnergy (F : ℂ → ℂ) (z : ℂ) : ℝ :=
  ‖F z‖ ^ 2 + euclideanEnergy F z

theorem continuousOn_euclideanGraphEnergy (F : smoothCore) :
    ContinuousOn (euclideanGraphEnergy F.val) upperHalfPlaneSet := by
  have hD (v : ℂ) : ContinuousOn (fun z => fderiv ℝ F.val z v) upperHalfPlaneSet :=
    (F.property.1.continuousOn_fderiv_of_isOpen isOpen_upperHalfPlaneSet (by simp)).clm_apply
      continuousOn_const
  exact (F.property.1.continuousOn.norm.pow 2).add
    (((hD 1).norm.pow 2).add ((hD Complex.I).norm.pow 2))

/-- The weighted ordinary energy on each compact hyperbolic chart has a
uniform bound in the actual modular graph norm. -/
theorem exists_compact_weightedGraphEnergy_bound {K : Set UpperHalfPlane} (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ F : smoothCore,
      IntegrableOn (fun τ : UpperHalfPlane => τ.im ^ 2 * euclideanGraphEnergy F.val τ) K volume ∧
      (∫ τ in K, τ.im ^ 2 * euclideanGraphEnergy F.val τ) ≤
        C * (‖value F‖ ^ 2 + ‖coreGradient F‖ ^ 2) := by
  obtain ⟨N, hN⟩ := exists_compact_graphEnergy_bound hK
  obtain ⟨B₀, hB₀⟩ := hK.exists_bound_of_continuousOn
    (UpperHalfPlane.continuous_im.pow 2).continuousOn
  let B : ℝ := max 1 B₀
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hy (τ : UpperHalfPlane) (hτ : τ ∈ K) : τ.im ^ 2 ≤ B :=
    (le_abs_self _).trans ((hB₀ τ hτ).trans (le_max_right _ _))
  refine ⟨B * ((N : ℝ) + 1), by positivity, fun F => ?_⟩
  have hc : Continuous (fun τ : UpperHalfPlane => τ.im ^ 2 * euclideanGraphEnergy F.val τ) :=
    (UpperHalfPlane.continuous_im.pow 2).mul
      ((continuousOn_euclideanGraphEnergy F).comp_continuous UpperHalfPlane.continuous_coe
        (fun τ => τ.im_pos))
  have hi : IntegrableOn (fun τ : UpperHalfPlane => τ.im ^ 2 * euclideanGraphEnergy F.val τ)
      K volume := hc.continuousOn.integrableOn_compact hK
  have hscaled : IntegrableOn (fun τ : UpperHalfPlane =>
      B * (‖F.val τ‖ ^ 2 + frameEnergy F.val τ)) K volume :=
    (hN F).1.const_mul B
  have hpoint (τ : UpperHalfPlane) (hτ : τ ∈ K) :
      τ.im ^ 2 * euclideanGraphEnergy F.val τ ≤
        B * (‖F.val τ‖ ^ 2 + frameEnergy F.val τ) := by
    have hframe : 0 ≤ frameEnergy F.val τ := add_nonneg (sq_nonneg _) (sq_nonneg _)
    calc
      _ = τ.im ^ 2 * ‖F.val τ‖ ^ 2 + frameEnergy F.val τ := by
        rw [frameEnergy_eq_im_sq_mul]
        dsimp [euclideanGraphEnergy]
        ring
      _ ≤ B * ‖F.val τ‖ ^ 2 + B * frameEnergy F.val τ :=
        add_le_add (mul_le_mul_of_nonneg_right (hy τ hτ) (sq_nonneg _))
          (by nlinarith [mul_le_mul_of_nonneg_right (le_max_left 1 B₀) hframe])
      _ = _ := by ring
  have hmono : (∫ τ in K, τ.im ^ 2 * euclideanGraphEnergy F.val τ) ≤
      ∫ τ in K, B * (‖F.val τ‖ ^ 2 + frameEnergy F.val τ) := by
    apply integral_mono_ae hi hscaled
    filter_upwards [ae_restrict_mem hK.measurableSet] with τ hτ
    exact hpoint τ hτ
  rw [integral_const_mul] at hmono
  refine ⟨hi, hmono.trans ?_⟩
  have hgraph : 0 ≤ ‖value F‖ ^ 2 + ‖coreGradient F‖ ^ 2 :=
    add_nonneg (sq_nonneg _) (sq_nonneg _)
  calc
    _ ≤ B * ((N : ℝ) * (‖value F‖ ^ 2 + ‖coreGradient F‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left (hN F).2 hB.le
    _ ≤ _ := by nlinarith [mul_nonneg hB.le hgraph]

/-- A compact complex set lying above the real axis has compact preimage in
the actual upper half-plane, without any fundamental-domain restriction. -/
theorem isCompact_coe_preimage_of_subset_upperHalfPlane {K : Set ℂ}
    (hK : IsCompact K) (hKU : K ⊆ upperHalfPlaneSet) :
    IsCompact (UpperHalfPlane.coe ⁻¹' K) := by
  apply UpperHalfPlane.isEmbedding_coe.isCompact_iff.mpr
  rw [image_preimage_eq_inter_range, inter_eq_left.mpr]
  · exact hK
  · intro z hz
    exact ⟨⟨z, hKU hz⟩, rfl⟩

/-- Actual ordinary area integrability and a uniform compact chart bound for
the full Euclidean graph energy, including compact sets crossing modular seams. -/
theorem exists_compact_euclideanGraphEnergy_bound {K : Set ℂ}
    (hK : IsCompact K) (hKU : K ⊆ upperHalfPlaneSet) :
    ∃ C : ℝ, 0 < C ∧ ∀ F : smoothCore,
      IntegrableOn (euclideanGraphEnergy F.val) K volume ∧
      (∫ z in K, euclideanGraphEnergy F.val z) ≤
        C * (‖value F‖ ^ 2 + ‖coreGradient F‖ ^ 2) := by
  obtain ⟨C, hC, hF⟩ := exists_compact_weightedGraphEnergy_bound
    (isCompact_coe_preimage_of_subset_upperHalfPlane hK hKU)
  refine ⟨C, hC, fun F => ?_⟩
  have hupper : ∀ z ∈ K, 0 < z.im := fun z hz => hKU hz
  refine ⟨(upperHalfPlane_integrableOn_im_sq_mul_iff hK.measurableSet hupper _).mp (hF F).1, ?_⟩
  rw [← upperHalfPlane_setIntegral_im_sq_mul hK.measurableSet hupper]
  exact (hF F).2

/-- Explicit coordinate form of the compact ordinary value and derivative
bound used by smooth cutoff maps into Euclidean `L²`. -/
theorem exists_compact_euclidean_graphEnergy_bound {K : Set ℂ}
    (hK : IsCompact K) (hKU : K ⊆ upperHalfPlaneSet) :
    ∃ C : ℝ, 0 < C ∧ ∀ F : smoothCore,
      IntegrableOn (fun z => ‖F.val z‖ ^ 2 + ‖fderiv ℝ F.val z 1‖ ^ 2 +
        ‖fderiv ℝ F.val z Complex.I‖ ^ 2) K volume ∧
      (∫ z in K, ‖F.val z‖ ^ 2 + ‖fderiv ℝ F.val z 1‖ ^ 2 +
        ‖fderiv ℝ F.val z Complex.I‖ ^ 2) ≤
        C * (‖value F‖ ^ 2 + ‖coreGradient F‖ ^ 2) := by
  obtain ⟨C, hC, hF⟩ := exists_compact_euclideanGraphEnergy_bound hK hKU
  refine ⟨C, hC, fun F => ?_⟩
  have heq : euclideanGraphEnergy F.val = fun z =>
      ‖F.val z‖ ^ 2 + ‖fderiv ℝ F.val z 1‖ ^ 2 + ‖fderiv ℝ F.val z Complex.I‖ ^ 2 := by
    funext z
    simp only [euclideanGraphEnergy, euclideanEnergy, add_assoc]
  simpa only [heq] using hF F

end GapFamily.Analytic.ModularGradient
