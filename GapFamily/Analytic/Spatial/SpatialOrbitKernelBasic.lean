import GapFamily.Analytic.Spatial.SpatialPointKernelComplexIntegrable
import GapFamily.Analytic.Spatial.SpatialIntegrableSeries
import GapFamily.Analytic.Modular.Periodization.ModularPeriodization
import GapFamily.Analytic.Modular.Geometry.ModularTileIntegral

/-!
The literal spatial orbit kernel uses the existing half-weighted full matrix
periodization: the prescribed effective group is PSL(2,Z), not SL(2,Z).
This module establishes actual L1 convergence and unfolding. Everywhere
and locally normal convergence are separate subsequent conclusions.
-/

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open MeasureTheory UpperHalfPlane Matrix Filter
open scoped MatrixGroups

private theorem modularGroup_countable_spatial : Countable SL(2, ℤ) := by
  have : Countable (Matrix (Fin 2) (Fin 2) ℤ) := by
    change Countable (Fin 2 → Fin 2 → ℤ)
    infer_instance
  change Countable {A : Matrix (Fin 2) (Fin 2) ℤ // A.det = 1}
  infer_instance

/-- The fixed one-half matrix weight removes exactly the central plus/minus pair. -/
def spatialOrbitKernel (s : ℂ) (z w : UpperHalfPlane) : ℂ :=
  modularPeriodization (fun v : ℂ => pointKernel s v w) z

theorem spatialOrbitKernel_eq_half_tsum_left (s : ℂ) (z w : UpperHalfPlane) :
    spatialOrbitKernel s z w =
      (1 / 2 : ℂ) * ∑' γ : SL(2, ℤ), pointKernel s (γ • z : UpperHalfPlane) w :=
  modularPeriodization_coe _ z

theorem pointKernel_modular_move (s : ℂ) (γ : SL(2, ℤ)) (z w : UpperHalfPlane) :
    pointKernel s (γ • z : UpperHalfPlane) w =
      pointKernel s z (γ⁻¹ • w : UpperHalfPlane) := by
  simpa only [inv_smul_smul] using
    (pointKernel_modular_smul s γ⁻¹ (γ • z) w).symm

/-- This is the literal source expression, with the matrix central pair removed. -/
theorem spatialOrbitKernel_eq_half_tsum_right (s : ℂ) (z w : UpperHalfPlane) :
    spatialOrbitKernel s z w =
      (1 / 2 : ℂ) * ∑' γ : SL(2, ℤ), pointKernel s z (γ • w : UpperHalfPlane) := by
  rw [spatialOrbitKernel_eq_half_tsum_left]
  congr 1
  simp_rw [pointKernel_modular_move]
  exact (Equiv.inv (SL(2, ℤ))).tsum_eq
    (fun γ : SL(2, ℤ) => pointKernel s z (γ • w : UpperHalfPlane))

theorem spatialOrbitKernel_modular_left (s : ℂ) (δ : SL(2, ℤ))
    (z w : UpperHalfPlane) :
    spatialOrbitKernel s (δ • z) w = spatialOrbitKernel s z w :=
  modularPeriodization_invariant _ δ z

theorem spatialOrbitKernel_symm (s : ℂ) (z w : UpperHalfPlane) :
    spatialOrbitKernel s z w = spatialOrbitKernel s w z := by
  rw [spatialOrbitKernel_eq_half_tsum_left, spatialOrbitKernel_eq_half_tsum_right]
  congr 1
  exact tsum_congr (fun γ => pointKernel_symm s (γ • z : UpperHalfPlane) w)

theorem spatialOrbitKernel_modular_right (s : ℂ) (δ : SL(2, ℤ))
    (z w : UpperHalfPlane) :
    spatialOrbitKernel s z (δ • w) = spatialOrbitKernel s z w := by
  rw [spatialOrbitKernel_symm, spatialOrbitKernel_modular_left, spatialOrbitKernel_symm]

theorem ae_summable_norm_spatialOrbit_left (s : ℂ) (hs : 1 < s.re) (w : UpperHalfPlane) :
    ∀ᵐ z : UpperHalfPlane ∂modularMeasure,
      Summable (fun γ : SL(2, ℤ) => ‖pointKernel s (γ • z : UpperHalfPlane) w‖) := by
  let : Countable SL(2, ℤ) := modularGroup_countable_spatial
  have hi := integrable_pointKernel_complex s hs w
  have hfi : ∀ γ : SL(2, ℤ), Integrable
      (fun z : UpperHalfPlane => pointKernel s (γ • z : UpperHalfPlane) w) modularMeasure :=
    fun γ => integrable_modularAction_of_integrable
      (f := fun z : UpperHalfPlane => pointKernel s z w) hi γ
  have hsum : Summable (fun γ : SL(2, ℤ) =>
      ∫ z : UpperHalfPlane, ‖pointKernel s (γ • z : UpperHalfPlane) w‖ ∂modularMeasure) :=
    summable_integral_norm_modularAction (f := fun z : UpperHalfPlane => pointKernel s z w) hi
  exact ae_summable_norm_of_summable_integral_norm hfi hsum

theorem ae_summable_norm_spatialOrbit_right (s : ℂ) (hs : 1 < s.re) (w : UpperHalfPlane) :
    ∀ᵐ z : UpperHalfPlane ∂modularMeasure,
      Summable (fun γ : SL(2, ℤ) => ‖pointKernel s z (γ • w : UpperHalfPlane)‖) := by
  filter_upwards [ae_summable_norm_spatialOrbit_left s hs w] with z hz
  apply (Equiv.inv (SL(2, ℤ))).summable_iff.mp
  change Summable (fun γ : SL(2, ℤ) => ‖pointKernel s z (γ⁻¹ • w : UpperHalfPlane)‖)
  simpa only [pointKernel_modular_move] using hz

/-- The defining scalar sum is genuinely integrable on the modular region. -/
theorem integrable_spatialOrbitKernel (s : ℂ) (hs : 1 < s.re) (w : UpperHalfPlane) :
    Integrable (fun z : UpperHalfPlane => spatialOrbitKernel s z w) modularMeasure := by
  let : Countable SL(2, ℤ) := modularGroup_countable_spatial
  have hi := integrable_pointKernel_complex s hs w
  have hfi : ∀ γ : SL(2, ℤ), Integrable
      (fun z : UpperHalfPlane => pointKernel s (γ • z : UpperHalfPlane) w) modularMeasure :=
    fun γ => integrable_modularAction_of_integrable
      (f := fun z : UpperHalfPlane => pointKernel s z w) hi γ
  have hsum : Summable (fun γ : SL(2, ℤ) =>
      ∫ z : UpperHalfPlane, ‖pointKernel s (γ • z : UpperHalfPlane) w‖ ∂modularMeasure) :=
    summable_integral_norm_modularAction (f := fun z : UpperHalfPlane => pointKernel s z w) hi
  have h := (integrable_tsum_of_summable_integral_norm hfi hsum).const_mul (1 / 2 : ℂ)
  simpa only [spatialOrbitKernel_eq_half_tsum_left] using h

/-- The central pair is counted by the existing tile theorem and canceled by
the fixed half-weight; the resulting actual modular mass is pi/(s-1). -/
theorem integral_spatialOrbitKernel (s : ℝ) (hs : 1 < s) (w : UpperHalfPlane) :
    (∫ z : UpperHalfPlane, spatialOrbitKernel (s : ℂ) z w ∂modularMeasure) =
      (Real.pi / (s - 1) : ℝ) := by
  simp only [spatialOrbitKernel_eq_half_tsum_left]
  rw [integral_const_mul,
    integral_modularAction_tsum_eq_two_mul (integrable_pointKernel s hs w),
    integral_pointKernel s hs w]
  ring

end GapFamily.Analytic.SpatialPoint
