import GapFamily.Analytic.Modular.Elliptic.ModularInteriorCompactUpperOperator
import GapFamily.Analytic.Modular.Geometry.ModularTruncatedTransportZero

/-!
# Global ordinary value of the actual upper-half-plane cutoff

This is the existing compact-target cutoff operator, followed by its existing
isometric extension by zero from the topological support of the cutoff.
-/

noncomputable section
namespace GapFamily.Analytic.ModularGradient
open Set MeasureTheory UpperHalfPlane
open scoped ContDiff

/-- The actual upper cutoff value, represented in global ordinary Euclidean L². -/
def upperCutoffValueOperator (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ upperHalfPlaneSet) :
    FormDomain →L[ℂ] Lp ℂ 2 (volume : Measure ℂ) := by
  let : CompactSpace (tsupport χ) := isCompact_iff_compactSpace.mp hc
  exact (LocalSobolev.zeroExtension (tsupport χ)).toContinuousLinearMap.comp
    (upperCutoffOperator χ hχ hc hs (tsupport χ))

/-- Agreement with the literal smooth-core value on the full Euclidean plane. -/
theorem upperCutoffValueOperator_coreForm_ae (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ upperHalfPlaneSet) (F : smoothCore) :
    upperCutoffValueOperator χ hχ hc hs (coreForm F) =ᵐ[(volume : Measure ℂ)]
      fun z => χ z * F.val z := by
  let : CompactSpace (tsupport χ) := isCompact_iff_compactSpace.mp hc
  change LocalSobolev.zeroExtension (tsupport χ)
    (upperCutoffOperator χ hχ hc hs (tsupport χ) (coreForm F)) =ᵐ[volume] _
  rw [upperCutoffOperator_coreForm]
  change LocalSobolev.zeroExtension (tsupport χ)
    (LocalSobolev.restrictedLp (tsupport χ) (fun z => χ z * F.val z)
      (upperCutoff_contDiff hχ hs F).continuous) =ᵐ[volume] _
  have h := LocalSobolev.zeroExtension_restrictedLp_ae (tsupport χ)
    (fun z => χ z * F.val z) (upperCutoff_contDiff hχ hs F).continuous
  filter_upwards [h] with z hz
  rw [hz]
  by_cases hzχ : z ∈ tsupport χ
  · simp [hzχ]
  · simp [hzχ, image_eq_zero_of_notMem_tsupport hzχ]

theorem exists_upperCutoffValueOperator_bound {χ : ℂ → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet) :
    ∃ B : ℝ, 0 < B ∧ ‖upperCutoffValueOperator χ hχ hc hs‖ ≤ B := by
  let : CompactSpace (tsupport χ) := isCompact_iff_compactSpace.mp hc
  obtain ⟨B, hB, hb⟩ := exists_upperCutoffOperator_bound hχ hc hs (tsupport χ)
  refine ⟨B, hB, ?_⟩
  apply ContinuousLinearMap.opNorm_le_bound _ hB.le
  intro u
  change ‖LocalSobolev.zeroExtension (tsupport χ)
    (upperCutoffOperator χ hχ hc hs (tsupport χ) u)‖ ≤ B * ‖u‖
  rw [(LocalSobolev.zeroExtension (tsupport χ)).norm_map]
  exact ((upperCutoffOperator χ hχ hc hs (tsupport χ)).le_opNorm u).trans
    (mul_le_mul_of_nonneg_right hb (norm_nonneg _))

/-- The derivative of a cutoff is again a globally smooth compact upper-half-plane cutoff. -/
theorem contDiff_upperCutoffDerivative {χ : ℂ → ℂ} (hχ : ContDiff ℝ ∞ χ) (v : ℂ) :
    ContDiff ℝ ∞ (fun z => fderiv ℝ χ z v) :=
  (hχ.fderiv_right (by simp)).clm_apply contDiff_const

def upperCutoffDerivativeValueOperator (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ upperHalfPlaneSet) (v : ℂ) :
    FormDomain →L[ℂ] Lp ℂ 2 (volume : Measure ℂ) :=
  upperCutoffValueOperator (fun z => fderiv ℝ χ z v) (contDiff_upperCutoffDerivative hχ v)
    (hc.fderiv_apply ℝ v) ((tsupport_fderiv_apply_subset ℝ v).trans hs)

theorem upperCutoffDerivativeValueOperator_coreForm_ae (χ : ℂ → ℂ)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet) (v : ℂ) (F : smoothCore) :
    upperCutoffDerivativeValueOperator χ hχ hc hs v (coreForm F) =ᵐ[(volume : Measure ℂ)]
      fun z => fderiv ℝ χ z v * F.val z :=
  upperCutoffValueOperator_coreForm_ae _ _ _ _ F

end GapFamily.Analytic.ModularGradient
