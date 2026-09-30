import GapFamily.Analytic.Modular.Geometry.ModularCoordinate

/-!
# Bounded transport from ordinary area to actual modular measure

The chosen fundamental domain has height greater than one half. Its literal
inverse-square coordinate density is bounded by four, so ordinary Euclidean
`L²` maps continuously to the actual modular coordinate `L²` space.
-/

noncomputable section

namespace GapFamily.Analytic

open Set MeasureTheory UpperHalfPlane
open scoped ENNReal

theorem modularCoordinateMeasure_le_four_volume :
    modularCoordinateMeasure ≤ (4 : ℝ≥0∞) • (volume : Measure ℂ) := by
  have hpoint : (fun z : ℂ => ENNReal.ofReal (1 / z.im ^ 2)) ≤ᵐ[volume.restrict modularInterior]
      fun _ => (4 : ℝ≥0∞) := by
    filter_upwards [ae_restrict_mem measurableSet_modularInterior] with z hz
    obtain ⟨τ, hτ, rfl⟩ := hz
    have hy := one_half_lt_im_of_mem_fd (ModularGroup.fdo_subset_fd hτ)
    have hweight : 1 / τ.im ^ 2 ≤ 4 := by
      rw [div_le_iff₀ (sq_pos_of_pos τ.im_pos)]
      nlinarith
    exact (ENNReal.ofReal_le_ofReal hweight).trans (by norm_num)
  calc
    _ ≤ (volume.restrict modularInterior).withDensity (fun _ => (4 : ℝ≥0∞)) :=
      withDensity_mono hpoint
    _ = (4 : ℝ≥0∞) • volume.restrict modularInterior := withDensity_const _
    _ ≤ _ := by gcongr; exact Measure.restrict_le_self

theorem modularCoordinateMeasure_absolutelyContinuous_volume :
    modularCoordinateMeasure ≪ (volume : Measure ℂ) :=
  Measure.absolutelyContinuous_of_le_smul modularCoordinateMeasure_le_four_volume

private def modularCoordinateFromVolumeReal :
    Lp ℂ 2 (volume : Measure ℂ) →L[ℝ] ModularCoordinateHilbert :=
  Lp.LpToLpOfMeasureLeSMul (c := 4) (by norm_num) modularCoordinateMeasure_le_four_volume

private theorem modularCoordinateFromVolumeReal_ae (f : Lp ℂ 2 (volume : Measure ℂ)) :
    modularCoordinateFromVolumeReal f =ᵐ[modularCoordinateMeasure] f :=
  Lp.coeFn_LpToLpOfMeasureLeSMul _ _ _

/-- The concrete change of measure is complex linear and preserves the same
representative almost everywhere for the modular coordinate measure. -/
def modularCoordinateFromVolume :
    Lp ℂ 2 (volume : Measure ℂ) →L[ℂ] ModularCoordinateHilbert where
  toFun := modularCoordinateFromVolumeReal
  map_add' := map_add _
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [modularCoordinateFromVolumeReal_ae (c • f),
      modularCoordinateMeasure_absolutelyContinuous_volume.ae_le (Lp.coeFn_smul c f),
      Lp.coeFn_smul c (modularCoordinateFromVolumeReal f),
      modularCoordinateFromVolumeReal_ae f] with z hcf hs hout hf
    simp only [RingHom.id_apply, hcf, hs, hout, Pi.smul_apply, hf]
  cont := modularCoordinateFromVolumeReal.continuous

theorem modularCoordinateFromVolume_ae (f : Lp ℂ 2 (volume : Measure ℂ)) :
    modularCoordinateFromVolume f =ᵐ[modularCoordinateMeasure] f :=
  modularCoordinateFromVolumeReal_ae f

theorem modularCoordinateFromVolume_norm_le_two : ‖modularCoordinateFromVolume‖ ≤ 2 := by
  have hr : ‖modularCoordinateFromVolumeReal‖ ≤ 2 := by
    have h := Lp.norm_LpToLpOfMeasureLeSMul_le (E := ℂ) (p := 2) (c := 4)
      (by norm_num) modularCoordinateMeasure_le_four_volume
    norm_num only [ENNReal.toReal_ofNat, ENNReal.toReal_div, ENNReal.toReal_one] at h
    exact h
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  exact (modularCoordinateFromVolumeReal.le_opNorm f).trans
    (mul_le_mul_of_nonneg_right hr (norm_nonneg f))

end GapFamily.Analytic
