import GapFamily.Analytic.Modular.Elliptic.ModularUpperCompactEvaluation
import GapFamily.Analytic.Modular.Geometry.ModularCutoffMultiplier
import GapFamily.Analytic.Modular.Geometry.ModularTruncatedTransportWeight

/-!
The actual compact graph representative agrees with its original modular
Hilbert value almost everywhere. Bounded coordinate transport and density
of the actual smooth values identify the cutoff lift with multiplication.
The compact observation set may cross the fundamental-domain seams.
-/

noncomputable section

namespace GapFamily.Analytic.ModularGradient

open Set Filter MeasureTheory Dirichlet UpperHalfPlane
open scoped Topology ContDiff ENNReal

variable (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
  (hsχ : tsupport χ ⊆ upperHalfPlaneSet)

/-- Ordinary-coordinate cutoff extension retains the literal modular value
for every source in the actual modular Hilbert space. -/
theorem upperCutoffHilbertValueOperator_modular_ae
    (f : ModularHilbert) :
    (fun τ : UpperHalfPlane => upperCutoffHilbertValueOperator χ hχ hcχ hsχ f τ)
      =ᵐ[modularMeasure] (fun τ : UpperHalfPlane => χ τ * f τ) := by
  let R := modularCoordinateFromVolume
  have hR (g : Lp ℂ 2 (volume : Measure ℂ)) :
      R g =ᵐ[modularCoordinateMeasure] g :=
    modularCoordinateFromVolume_ae g
  have hQ (g : Lp ℂ 2 (volume : Measure ℂ)) :
      modularCoordinateEquiv (R g) =ᵐ[modularMeasure]
        (fun τ : UpperHalfPlane => g τ) :=
    (modularCoordinateEquiv_apply_ae (R g)).trans
      ((ae_modularCoordinate_iff _).mp (hR g))
  have hd : DenseRange value := by
    simpa only [DenseRange, LinearMap.coe_range] using value_dense_range
  have heq : modularCoordinateEquiv (R (upperCutoffHilbertValueOperator χ hχ hcχ hsχ f)) =
      modularCutoffMultiplier χ hχ.continuous hcχ f := by
    refine hd.induction_on f ?_ ?_
    · exact isClosed_eq
        (modularCoordinateEquiv.continuous.comp
          (R.continuous.comp (upperCutoffHilbertValueOperator χ hχ hcχ hsχ).continuous))
        (modularCutoffMultiplier χ hχ.continuous hcχ).continuous
    · intro F
      apply Lp.ext
      have hcore :
          (fun τ : UpperHalfPlane =>
            upperCutoffHilbertValueOperator χ hχ hcχ hsχ (value F) τ)
            =ᵐ[modularMeasure] (fun τ : UpperHalfPlane => χ τ * F.val τ) :=
        (ae_modularCoordinate_iff _).mp
          (modularCoordinateMeasure_absolutelyContinuous_volume.ae_eq
            (upperCutoffHilbertValueOperator_value_ae χ hχ hcχ hsχ F))
      filter_upwards [hQ (upperCutoffHilbertValueOperator χ hχ hcχ hsχ (value F)),
        modularCutoffMultiplier_ae χ hχ.continuous hcχ (value F),
        hcore, value_ae F] with τ hQτ hmτ hcτ hvτ
      rw [hQτ, hmτ, hcτ, hvτ]
  have hm := modularCutoffMultiplier_ae χ hχ.continuous hcχ f
  rw [← heq] at hm
  exact (hQ (upperCutoffHilbertValueOperator χ hχ hcχ hsχ f)).symm.trans hm

/-- Compact graph evaluation represents the same modular Hilbert value,
including when the compact observation set crosses a modular seam. -/
theorem laplacianUpperCompactRestriction_modular_ae
    (U : Set ℂ) (hU : IsOpen U) (hχU : EqOn χ (fun _ => 1) U)
    (K : Set ℂ) [CompactSpace K] (hKU : K ⊆ U) (u : LaplacianGraphDomain) :
    ∀ᵐ τ : UpperHalfPlane ∂modularMeasure, (τ : ℂ) ∈ K →
      localContinuousExtend
          (laplacianUpperCompactRestriction χ hχ hcχ hsχ U hU hχU K hKU u) τ =
        gradientEmbedding laplacian u τ := by
  have hK : MeasurableSet K := (isCompact_iff_compactSpace.mpr inferInstance).measurableSet
  have hrep : ∀ᵐ z ∂(volume : Measure ℂ), z ∈ K →
      localContinuousExtend
          (laplacianUpperCompactRestriction χ hχ hcχ hsχ U hU hχU K hKU u) z =
        laplacianUpperGraphValue χ hχ hcχ hsχ u z :=
    (ae_restrict_iff' hK).mp
      (laplacianUpperCompactRestriction_ae χ hχ hcχ hsχ U hU hχU K hKU u)
  have hrepmod := (ae_modularCoordinate_iff _).mp
    (modularCoordinateMeasure_absolutelyContinuous_volume.ae_le hrep)
  filter_upwards [hrepmod,
    upperCutoffHilbertValueOperator_modular_ae χ hχ hcχ hsχ
      (gradientEmbedding laplacian u)] with τ hr hv
  intro hτ
  rw [hr hτ]
  change upperCutoffHilbertValueOperator χ hχ hcχ hsχ
    (gradientEmbedding laplacian u) τ = _
  rw [hv, hχU (hKU hτ), one_mul]

/-- Direct Laplacian-domain version of the actual-value identity. -/
theorem laplacianUpperCompactRestriction_lift_modular_ae
    (U : Set ℂ) (hU : IsOpen U) (hχU : EqOn χ (fun _ => 1) U)
    (K : Set ℂ) [CompactSpace K] (hKU : K ⊆ U) (u : laplacian.domain) :
    ∀ᵐ τ : UpperHalfPlane ∂modularMeasure, (τ : ℂ) ∈ K →
      localContinuousExtend
          (laplacianUpperCompactRestriction χ hχ hcχ hsχ U hU hχU K hKU
            (gradientLift laplacian u)) τ =
        (u : ModularHilbert) τ := by
  simpa only [gradientEmbedding_lift] using
    laplacianUpperCompactRestriction_modular_ae χ hχ hcχ hsχ U hU hχU K hKU
      (gradientLift laplacian u)

/-- Equivalent restricted-measure form for ordinary modular integrals. -/
theorem laplacianUpperCompactRestriction_lift_modular_restrict_ae
    (U : Set ℂ) (hU : IsOpen U) (hχU : EqOn χ (fun _ => 1) U)
    (K : Set ℂ) [CompactSpace K] (hKU : K ⊆ U) (u : laplacian.domain) :
    (fun τ : UpperHalfPlane => localContinuousExtend
          (laplacianUpperCompactRestriction χ hχ hcχ hsχ U hU hχU K hKU
            (gradientLift laplacian u)) τ)
      =ᵐ[modularMeasure.restrict (UpperHalfPlane.coe ⁻¹' K)] (u : ModularHilbert) := by
  apply (ae_restrict_iff'
    (UpperHalfPlane.measurable_coe
      (isCompact_iff_compactSpace.mpr inferInstance).measurableSet)).mpr
  exact laplacianUpperCompactRestriction_lift_modular_ae χ hχ hcχ hsχ U hU hχU K hKU u

end GapFamily.Analytic.ModularGradient
