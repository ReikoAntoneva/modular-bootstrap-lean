import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.Tactic

/-!
# Coordinates for the continuous BTZ reference

The lightcone variables are `u = E + J` and `v = E - J`.  This module records the
literal Lebesgue Jacobian, independently of any choice of reference density.
-/

noncomputable section

open MeasureTheory Set Module
open scoped ENNReal

namespace BTZEntropy

/-- The positive lightcone-coordinate quadrant. -/
def lightconeQuadrant : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioi 0

/-- The open physical energy-spin cone. -/
def energySpinCone : Set (ℝ × ℝ) := {p | |p.2| < p.1}

/-- The inverse of `(E,J) ↦ (E+J,E-J)`. -/
def lightconeLinearEquiv : (ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ) where
  toFun p := ((p.1 + p.2) / 2, (p.1 - p.2) / 2)
  invFun p := (p.1 + p.2, p.1 - p.2)
  left_inv p := by ext <;> dsimp <;> ring
  right_inv p := by ext <;> dsimp <;> ring
  map_add' p q := by ext <;> dsimp <;> ring
  map_smul' r p := by ext <;> dsimp <;> ring

/-- The lightcone change of variables as a continuous linear equivalence. -/
def lightconeEquiv : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
  lightconeLinearEquiv.toContinuousLinearEquiv

@[simp] theorem lightconeEquiv_apply (p : ℝ × ℝ) :
    lightconeEquiv p = ((p.1 + p.2) / 2, (p.1 - p.2) / 2) := rfl

@[simp] theorem lightconeEquiv_symm_apply (p : ℝ × ℝ) :
    lightconeEquiv.symm p = (p.1 + p.2, p.1 - p.2) := rfl

theorem lightconeLinearEquiv_det :
    LinearMap.det lightconeLinearEquiv.toLinearMap = -(1 / 2 : ℝ) := by
  rw [← LinearMap.det_toMatrix (Basis.finTwoProd ℝ), Matrix.det_fin_two]
  norm_num [LinearMap.toMatrix_apply, Basis.coe_finTwoProd_repr,
    lightconeLinearEquiv]

theorem lightconeEquiv_preimage_cone :
    lightconeEquiv ⁻¹' energySpinCone = lightconeQuadrant := by
  ext p
  simp only [mem_preimage, energySpinCone, mem_ofPred_eq, lightconeEquiv_apply,
    lightconeQuadrant, mem_prod, mem_Ioi, abs_lt]
  constructor
  · rintro ⟨h₁, h₂⟩
    constructor <;> linarith
  · rintro ⟨h₁, h₂⟩
    constructor <;> linarith

theorem lightconeEquiv_image_quadrant :
    lightconeEquiv '' lightconeQuadrant = energySpinCone := by
  rw [← lightconeEquiv_preimage_cone]
  exact Set.image_preimage_eq _ lightconeEquiv.surjective

/-- The inverse Jacobian is exactly two. -/
theorem map_lightcone_volume :
    Measure.map lightconeEquiv (volume : Measure (ℝ × ℝ)) =
      (2 : ℝ≥0∞) • volume := by
  let : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]
    infer_instance
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (ℝ × ℝ))
    (f := lightconeLinearEquiv.toLinearMap)
    (by rw [lightconeLinearEquiv_det]; norm_num)
  simpa [lightconeLinearEquiv_det, lightconeEquiv] using h

/-- Lebesgue measure in `(u,v)` pushes forward to twice Lebesgue measure in `(E,J)`. -/
theorem map_lightconeQuadrant :
    Measure.map lightconeEquiv (volume.restrict lightconeQuadrant) =
      (2 : ℝ≥0∞) • volume.restrict energySpinCone := by
  have h := lightconeEquiv.toHomeomorph.toMeasurableEquiv.restrict_map
    (volume : Measure (ℝ × ℝ)) energySpinCone
  change (Measure.map lightconeEquiv volume).restrict energySpinCone =
    Measure.map lightconeEquiv (volume.restrict (lightconeEquiv ⁻¹' energySpinCone)) at h
  rw [lightconeEquiv_preimage_cone, map_lightcone_volume, Measure.restrict_smul] at h
  exact h.symm

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ F] in
/-- Integrability is unchanged by the lightcone substitution. -/
theorem integrable_lightconeQuadrant_iff (f : (ℝ × ℝ) → F) :
    Integrable (fun p => f (lightconeEquiv p)) (volume.restrict lightconeQuadrant) ↔
      Integrable f (volume.restrict energySpinCone) := by
  have h := integrable_map_equiv (μ := volume.restrict lightconeQuadrant)
    lightconeEquiv.toHomeomorph.toMeasurableEquiv f
  change Integrable f (Measure.map lightconeEquiv (volume.restrict lightconeQuadrant)) ↔
    Integrable (fun p => f (lightconeEquiv p)) (volume.restrict lightconeQuadrant) at h
  rw [map_lightconeQuadrant, integrable_smul_measure (by norm_num) (by norm_num)] at h
  exact h.symm

/-- The coordinate integral identity, valid also when the Bochner integral is undefined. -/
theorem integral_lightconeQuadrant (f : (ℝ × ℝ) → F) :
    (∫ p in lightconeQuadrant, f (lightconeEquiv p)) =
      (2 : ℝ) • ∫ p in energySpinCone, f p := by
  have h := integral_map_equiv (μ := volume.restrict lightconeQuadrant)
    lightconeEquiv.toHomeomorph.toMeasurableEquiv f
  change (∫ p, f p ∂Measure.map lightconeEquiv (volume.restrict lightconeQuadrant)) =
    (∫ p in lightconeQuadrant, f (lightconeEquiv p)) at h
  rw [map_lightconeQuadrant, integral_smul_measure] at h
  simpa using h.symm

/-- The Jacobian form used to integrate the continuous density over the cone. -/
theorem integral_energySpinCone (f : (ℝ × ℝ) → F) :
    (∫ p in energySpinCone, f p) =
      (1 / 2 : ℝ) • ∫ p in lightconeQuadrant, f (lightconeEquiv p) := by
  rw [integral_lightconeQuadrant, smul_smul]
  norm_num

end BTZEntropy
