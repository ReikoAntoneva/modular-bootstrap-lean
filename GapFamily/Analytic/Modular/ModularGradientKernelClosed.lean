import GapFamily.Analytic.Modular.ModularGradientKernelGeometry
import GapFamily.Analytic.Modular.ModularGradientDistribution
import GapFamily.Analytic.Elliptic.WeakGradientConstant

/-!
# Kernel of the actual closed modular gradient

The graph-closed gradient has exactly the constant channel as its kernel. The
reverse inclusion uses its actual Euclidean distributional derivatives,
local integrability, and weak constancy on the connected modular interior.
-/

noncomputable section

namespace GapFamily.Analytic.ModularGradient

open Set MeasureTheory
open scoped ContDiff

theorem coordinateDx_ae_eq_zero_of_closedGradient_eq_zero
    (u : closedGradient.domain) (hu : closedGradient u = 0) :
    coordinateDx u =ᵐ[volume.restrict modularInterior] 0 := by
  apply (ae_modularCoordinate_iff_restrict _).mp
  have hx : (WithLp.ofLp (closedGradient u)).1 = 0 := by rw [hu]; rfl
  filter_upwards [Lp.coeFn_zero (E := ℂ) (p := 2) (μ := modularCoordinateMeasure)]
    with z hz
  simp only [coordinateDx, hx, map_zero, hz, zero_div, Pi.zero_apply]

theorem coordinateDy_ae_eq_zero_of_closedGradient_eq_zero
    (u : closedGradient.domain) (hu : closedGradient u = 0) :
    coordinateDy u =ᵐ[volume.restrict modularInterior] 0 := by
  apply (ae_modularCoordinate_iff_restrict _).mp
  have hy : (WithLp.ofLp (closedGradient u)).2 = 0 := by rw [hu]; rfl
  filter_upwards [Lp.coeFn_zero (E := ℂ) (p := 2) (μ := modularCoordinateMeasure)]
    with z hz
  simp only [coordinateDy, hy, map_zero, hz, zero_div, Pi.zero_apply]

theorem coordinateValue_test_x_eq_zero_of_closedGradient_eq_zero
    (u : closedGradient.domain) (hu : closedGradient u = 0)
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ modularInterior) :
    (∫ z in modularInterior, (fderiv ℝ φ z 1 : ℂ) * coordinateValue u z) = 0 := by
  have h := coordinateDx_weak_identity u φ hφ hc hs
  have hzero : (∫ z in modularInterior, (φ z : ℂ) * coordinateDx u z) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [coordinateDx_ae_eq_zero_of_closedGradient_eq_zero u hu] with z hz
    simp only [hz, Pi.zero_apply, mul_zero]
  rw [hzero, eq_comm, neg_eq_zero] at h
  exact h

theorem coordinateValue_test_y_eq_zero_of_closedGradient_eq_zero
    (u : closedGradient.domain) (hu : closedGradient u = 0)
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ modularInterior) :
    (∫ z in modularInterior, (fderiv ℝ φ z Complex.I : ℂ) * coordinateValue u z) = 0 := by
  have h := coordinateDy_weak_identity u φ hφ hc hs
  have hzero : (∫ z in modularInterior, (φ z : ℂ) * coordinateDy u z) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [coordinateDy_ae_eq_zero_of_closedGradient_eq_zero u hu] with z hz
    simp only [hz, Pi.zero_apply, mul_zero]
  rw [hzero, eq_comm, neg_eq_zero] at h
  exact h

/-- A constant Euclidean coordinate representative is the same actual modular
`L²` constant vector under the constructed coordinate isometry. -/
theorem eq_smul_modularConstant_of_coordinateValue_ae_eq_const
    (u : closedGradient.domain) {c : ℂ}
    (hc : coordinateValue u =ᵐ[volume.restrict modularInterior] fun _ => c) :
    (u : ModularHilbert) = c • modularConstant := by
  have hcoord : coordinateValue u =ᵐ[modularCoordinateMeasure] fun _ => c :=
    (ae_modularCoordinate_iff_restrict _).mpr hc
  have hmod : (fun τ : UpperHalfPlane => coordinateValue u τ) =ᵐ[modularMeasure]
      fun _ => c := (ae_modularCoordinate_iff _).mp hcoord
  have hvalue : (u : ModularHilbert) =ᵐ[modularMeasure]
      fun τ : UpperHalfPlane => coordinateValue u τ := by
    simpa only [coordinateValue, LinearIsometryEquiv.apply_symm_apply] using
      modularCoordinateEquiv_apply_ae (coordinateValue u)
  apply Lp.ext
  filter_upwards [hvalue, hmod, Lp.coeFn_smul c modularConstant, modularConstant_ae]
    with τ hτ hcτ hs h1
  rw [hτ, hcτ, hs]
  simp [h1]

/-- A vector with zero actual closed gradient has an almost-everywhere constant
representative for ordinary area on the modular interior. -/
theorem coordinateValue_ae_eq_const_of_closedGradient_eq_zero
    (u : closedGradient.domain) (hu : closedGradient u = 0) :
    ∃ c : ℂ, coordinateValue u =ᵐ[volume.restrict modularInterior] fun _ => c := by
  exact exists_ae_eq_const_of_integral_basis_fderiv_mul_eq_zero
    isOpen_modularInterior isConnected_modularInterior (coordinateValue_locallyIntegrableOn u)
    (coordinateValue_test_x_eq_zero_of_closedGradient_eq_zero u hu)
    (coordinateValue_test_y_eq_zero_of_closedGradient_eq_zero u hu)

/-- Zero gradient in the actual closed domain forces membership in the
constructed one-dimensional constant channel. -/
theorem mem_constantSpace_of_closedGradient_eq_zero
    (u : closedGradient.domain) (hu : closedGradient u = 0) :
    (u : ModularHilbert) ∈ modularConstantSpace := by
  obtain ⟨c, hc⟩ := coordinateValue_ae_eq_const_of_closedGradient_eq_zero u hu
  rw [eq_smul_modularConstant_of_coordinateValue_ae_eq_const u hc]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self modularConstant)

/-- The graph-closed modular gradient has precisely the actual constant kernel. -/
theorem closedGradient_kernel_eq_constantSpace :
    closedGradient.ker = modularConstantSpace := by
  apply le_antisymm ?_ constantSpace_le_closedGradient_kernel
  intro f hf
  obtain ⟨u, rfl, hu⟩ := LinearPMap.mem_ker_iff.mp hf
  exact mem_constantSpace_of_closedGradient_eq_zero u hu

end GapFamily.Analytic.ModularGradient
