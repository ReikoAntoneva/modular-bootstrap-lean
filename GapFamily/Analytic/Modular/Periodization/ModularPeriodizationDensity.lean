import GapFamily.Analytic.Modular.Periodization.ModularPeriodization
import GapFamily.Analytic.Modular.Periodization.ModularPeriodizationLp
import GapFamily.Analytic.Modular.ModularGradientClosed
import GapFamily.Analytic.Elliptic.GradientLocalDensity

/-!
# Density of the smooth automorphic gradient core
Interior smooth tests are periodized over the actual modular action. Their exact agreement in the domain transfers the actual value and gradient integrability. Coordinate test density then proves density in the ambient modular Hilbert space.
-/
noncomputable section
namespace GapFamily.Analytic
open Set Filter MeasureTheory UpperHalfPlane
open scoped ContDiff MatrixGroups

theorem modularPeriodization_ae {φ : ℂ → ℂ}
    (hs : tsupport φ ⊆ modularInterior) :
    (fun τ : UpperHalfPlane => modularPeriodization φ τ) =ᵐ[modularMeasure]
      (fun τ : UpperHalfPlane => φ τ) := by
  filter_upwards [ae_mem_fdo] with τ hτ
  exact modularPeriodization_eq_on_fd hs (ModularGroup.fdo_subset_fd hτ)

namespace ModularGradient

theorem modularPeriodization_directional_ae {φ : ℂ → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ modularInterior) (v : ℂ) :
    directional (modularPeriodization φ) v =ᵐ[modularMeasure] directional φ v := by
  exact modularDirectional_ae_eq
    ((contDiffOn_modularPeriodization hφ hc hs).continuousOn.mono
      (fun _ hz => im_pos_of_mem_modularInterior hz))
    hφ.continuous.continuousOn (modularPeriodization_ae hs) v

theorem modularPeriodization_mem_smoothCore {φ : ℂ → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ modularInterior) : modularPeriodization φ ∈ smoothCore := by
  refine ⟨contDiffOn_modularPeriodization hφ hc hs,
    modularPeriodization_invariant φ, ?_, ?_, ?_⟩
  · exact (memLp_congr_ae (modularPeriodization_ae hs)).mpr
      (memLp_test_value φ hφ.continuous hc)
  · exact (memLp_congr_ae (modularPeriodization_directional_ae hφ hc hs 1)).mpr
      (memLp_test_directional φ hφ hc 1)
  · exact (memLp_congr_ae (modularPeriodization_directional_ae hφ hc hs Complex.I)).mpr
      (memLp_test_directional φ hφ hc Complex.I)

/-- A genuine invariant core element built from a compact interior test. -/
def periodizedCore (φ : ℂ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ modularInterior) : smoothCore :=
  ⟨modularPeriodization φ, modularPeriodization_mem_smoothCore hφ hc hs⟩

theorem value_periodizedCore_ae (φ : ℂ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ modularInterior) :
    value (periodizedCore φ hφ hc hs) =ᵐ[modularMeasure]
      (fun τ : UpperHalfPlane => φ τ) :=
  (value_ae (periodizedCore φ hφ hc hs)).trans (modularPeriodization_ae hs)

/-- Every real interior smooth test is the value class of an actual automorphic core function. -/
theorem coordinate_test_mem_value_range (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ modularInterior) :
    modularCoordinateEquiv (localRealTestL2 modularCoordinateMeasure φ hφ hc) ∈ value.range := by
  have hφC : ContDiff ℝ ∞ (fun z => (φ z : ℂ)) := Complex.ofRealCLM.contDiff.comp hφ
  have hcC : HasCompactSupport (fun z => (φ z : ℂ)) := hc.comp_left Complex.ofReal_zero
  have hsC : tsupport (fun z => (φ z : ℂ)) ⊆ modularInterior := by
    exact (tsupport_comp_subset Complex.ofReal_zero φ).trans hs
  refine ⟨periodizedCore (fun z => (φ z : ℂ)) hφC hcC hsC, ?_⟩
  apply Lp.ext
  have htest := (ae_modularCoordinate_iff (fun z =>
    localRealTestL2 modularCoordinateMeasure φ hφ hc z = (φ z : ℂ))).mp
      (localRealTestL2_ae (μ := modularCoordinateMeasure) φ hφ hc)
  filter_upwards [value_periodizedCore_ae (fun z => (φ z : ℂ)) hφC hcC hsC,
    modularCoordinateEquiv_apply_ae (localRealTestL2 modularCoordinateMeasure φ hφ hc),
    htest] with τ hvalue hmap htest
  exact hvalue.trans (hmap.trans htest).symm

/-- The actual finite-energy smooth automorphic core is dense in the modular Hilbert space. -/
theorem value_dense_range : Dense (value.range : Set ModularHilbert) := by
  let W : Submodule ℂ ModularCoordinateHilbert :=
    value.range.comap modularCoordinateEquiv.toLinearEquiv.toLinearMap
  have hspan : localTestSpan modularCoordinateMeasure modularInterior ≤ W := by
    apply Submodule.span_le.mpr
    rintro f ⟨φ, hφ, hc, hs, rfl⟩
    exact coordinate_test_mem_value_range φ hφ hc hs
  have hdense := modularCoordinateEquiv.surjective.denseRange.dense_image
    modularCoordinateEquiv.continuous
    (localTestSpan_dense (μ := modularCoordinateMeasure) isOpen_modularInterior
      ae_mem_modularInterior)
  apply hdense.mono
  rintro f ⟨g, hg, rfl⟩
  exact hspan hg

/-- Density is proved for the literal quotient-defined gradient domain. -/
theorem gradient_dense_domain : Dense (gradient.domain : Set ModularHilbert) := value_dense_range

/-- Closing the graph preserves the now-proved dense actual domain. -/
theorem closedGradient_dense_domain : Dense (closedGradient.domain : Set ModularHilbert) :=
  gradient_dense_domain.mono gradient_le_closedGradient.1

end ModularGradient
end GapFamily.Analytic
