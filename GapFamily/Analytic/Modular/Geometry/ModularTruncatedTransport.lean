import GapFamily.Analytic.Modular.Geometry.ModularTruncatedTransportBasic
import GapFamily.Analytic.Modular.Geometry.ModularTruncatedTransportWeight
import GapFamily.Analytic.Modular.Geometry.ModularTruncatedTransportZero

/-!
# Actual transport of a compact Euclidean restriction to the modular Hilbert space

Extend from the closed truncated-domain subtype by zero, apply the actual
bounded inverse-square density, and use the existing coordinate unitary.
The resulting complex-linear map has norm at most two and agrees with the
literal low-height indicator on restrictions of ambient continuous functions.
-/

noncomputable section

namespace GapFamily.Analytic.ModularGradient

open Set MeasureTheory UpperHalfPlane

/-- A concrete bounded transport, with no assumed change-of-measure record. -/
def modularTruncatedTransport (H : ℝ) : ModularTruncatedSource H →L[ℂ] ModularHilbert :=
  modularCoordinateEquiv.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (modularCoordinateFromVolume.comp
      (LocalSobolev.zeroExtension (modularTruncatedTarget H)).toContinuousLinearMap)

theorem modularTruncatedTransport_norm_le_two (H : ℝ) :
    ‖modularTruncatedTransport H‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  change ‖modularCoordinateEquiv
      (modularCoordinateFromVolume (LocalSobolev.zeroExtension (modularTruncatedTarget H) f))‖ ≤
    2 * ‖f‖
  rw [modularCoordinateEquiv.norm_map]
  calc
    _ ≤ ‖modularCoordinateFromVolume‖ *
        ‖LocalSobolev.zeroExtension (modularTruncatedTarget H) f‖ :=
      modularCoordinateFromVolume.le_opNorm _
    _ ≤ 2 * ‖LocalSobolev.zeroExtension (modularTruncatedTarget H) f‖ :=
      mul_le_mul_of_nonneg_right modularCoordinateFromVolume_norm_le_two (norm_nonneg _)
    _ = _ := by rw [LinearIsometry.norm_map]

/-- The transported vector retains the literal extension-by-zero representative. -/
theorem modularTruncatedTransport_ae (H : ℝ) (f : ModularTruncatedSource H) :
    modularTruncatedTransport H f =ᵐ[modularMeasure]
      fun τ : UpperHalfPlane => LocalSobolev.zeroExtendFun (modularTruncatedTarget H) f τ := by
  have hzero := LocalSobolev.zeroExtension_ae (modularTruncatedTarget H) f
  have hcoord := (modularCoordinateFromVolume_ae
      (LocalSobolev.zeroExtension (modularTruncatedTarget H) f)).trans
    (modularCoordinateMeasure_absolutelyContinuous_volume.ae_le hzero)
  have hmod := (ae_modularCoordinate_iff _).mp hcoord
  exact (modularCoordinateEquiv_apply_ae _).trans hmod

/-- On a continuous ambient function the actual transport is exactly its
low-height modular restriction, including the cutoff boundary. -/
theorem modularTruncatedTransport_restrictedLp_ae (H : ℝ) (f : ℂ → ℂ) (hf : Continuous f) :
    modularTruncatedTransport H (LocalSobolev.restrictedLp (modularTruncatedTarget H) f hf)
      =ᵐ[modularMeasure]
        {τ : UpperHalfPlane | τ.im ≤ H}.indicator (fun τ => f τ) := by
  have hzero := LocalSobolev.zeroExtension_restrictedLp_ae (modularTruncatedTarget H) f hf
  have hcoord := (modularCoordinateFromVolume_ae
      (LocalSobolev.zeroExtension (modularTruncatedTarget H)
        (LocalSobolev.restrictedLp (modularTruncatedTarget H) f hf))).trans
    (modularCoordinateMeasure_absolutelyContinuous_volume.ae_le hzero)
  have hmod := (ae_modularCoordinate_iff _).mp hcoord
  have hout := modularCoordinateEquiv_apply_ae
    (modularCoordinateFromVolume (LocalSobolev.zeroExtension (modularTruncatedTarget H)
      (LocalSobolev.restrictedLp (modularTruncatedTarget H) f hf)))
  filter_upwards [hout, hmod, ae_mem_fdo] with τ hτ heq hfd
  change (modularCoordinateEquiv
    (modularCoordinateFromVolume (LocalSobolev.zeroExtension (modularTruncatedTarget H)
      (LocalSobolev.restrictedLp (modularTruncatedTarget H) f hf)))) τ = _
  rw [hτ, heq]
  have hclosed := ModularGroup.fdo_subset_fd hfd
  by_cases hh : τ.im ≤ H
  · rw [indicator_of_mem ((coe_mem_modularTruncatedTarget_iff H τ).mpr ⟨hclosed, hh⟩)]
    simp [hh]
  · rw [indicator_of_notMem (fun ht => hh ((coe_mem_modularTruncatedTarget_iff H τ).mp ht).2)]
    simp [hh]

end GapFamily.Analytic.ModularGradient
