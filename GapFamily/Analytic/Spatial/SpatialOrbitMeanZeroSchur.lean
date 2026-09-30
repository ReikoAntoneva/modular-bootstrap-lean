import GapFamily.Analytic.Spatial.SpatialOrbitMeanZeroContinuation
import GapFamily.Analytic.Cusp.Schur.CuspSchurGlobalPhysical

/-! Identification of the positive recurrence branch with the actual full
Schur resolvent after removing precisely its constant spatial channel. -/

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open ModularProjected ModularMeanZeroResolvent

/-- The exact constant spectral contribution to the continued operator is
`π/(s-1)` times the genuine constant projection. Its integral kernel therefore
has coefficient `3/(s-1)`. -/
theorem spatialOrbitMeanZeroContinuation_eq_fullResolvent_sub_constant
    (s : ℝ) (hs : 1 / 2 < s) (hne : s ≠ 1) :
    spatialOrbitMeanZeroContinuation s hs =
      (s : ℂ) ^ 2 • (fullResolvent ((s * (1 - s) : ℝ) : ℂ) *
        spatialOrbitIntegralOperator (s + 1) (by linarith)) -
      (((Real.pi / (s - 1) : ℝ) : ℂ) • modularConstantProjection) := by
  have hs0 : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have hs1 : (s : ℂ) - 1 ≠ 0 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub]
    exact Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr hne)
  have h1s : 1 - (s : ℂ) ≠ 0 := sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp hs1))
  have hc : (s : ℂ) ^ 2 * (((s * (1 - s) : ℝ) : ℂ))⁻¹ *
      ((Real.pi / s : ℝ) : ℂ) = -((Real.pi / (s - 1) : ℝ) : ℂ) := by
    push_cast
    field_simp [hs0, hs1, h1s]
    <;> ring
  apply ContinuousLinearMap.ext
  intro f
  change (s : ℂ) ^ 2 • meanZeroResolvent (s * (1 - s))
      (spatialOrbitIntegralOperator (s + 1) (by linarith) f) =
    (s : ℂ) ^ 2 • fullResolvent ((s * (1 - s) : ℝ) : ℂ)
      (spatialOrbitIntegralOperator (s + 1) (by linarith) f) -
    ((Real.pi / (s - 1) : ℝ) : ℂ) • modularConstantProjection f
  have hPA := congrArg (fun A : ModularHilbert →L[ℂ] ModularHilbert => A f)
    (constantProjection_comp_spatialOrbitIntegralOperator (s + 1) (by linarith))
  change modularConstantProjection (spatialOrbitIntegralOperator (s + 1) (by linarith) f) =
    ((Real.pi / (s + 1 - 1) : ℝ) : ℂ) • modularConstantProjection f at hPA
  simp only [add_sub_cancel_right] at hPA
  rw [fullResolvent_apply, hPA, smul_sub, smul_smul, smul_smul, hc]
  change (s : ℂ) ^ 2 • meanZeroResolvent (s * (1 - s))
      (spatialOrbitIntegralOperator (s + 1) (by linarith) f) =
    (s : ℂ) ^ 2 • meanZeroResolvent (s * (1 - s))
      (spatialOrbitIntegralOperator (s + 1) (by linarith) f) -
    (-((Real.pi / (s - 1) : ℝ) : ℂ)) • modularConstantProjection f -
    ((Real.pi / (s - 1) : ℝ) : ℂ) • modularConstantProjection f
  module


/-- On the full real physical branch above one half, away from the constant
pole at one, the proved positive operator is the actual Schur response with
its exact constant correction. -/
theorem spatialOrbitMeanZeroContinuation_eq_actualSchur_sub_constant
    (s : ℝ) (hs : 1 / 2 < s) (hne : s ≠ 1) :
    spatialOrbitMeanZeroContinuation s hs =
      (s : ℂ) ^ 2 • (CuspSchur.actualSchurResolvent
          ((s * (1 - s) : ℝ) : ℂ) *
        spatialOrbitIntegralOperator (s + 1) (by linarith)) -
      (((Real.pi / (s - 1) : ℝ) : ℂ) • modularConstantProjection) := by
  have hp : 0 < ((s : ℂ) - (1 / 2 : ℂ)).re := by
    norm_num [Complex.sub_re]
    linarith
  have hh : (s : ℂ) - (1 / 2 : ℂ) ≠ (1 / 2 : ℂ) := by
    intro he
    have he' := congrArg Complex.re he
    norm_num [Complex.sub_re] at he'
    exact hne (by linarith)
  have hpar : (1 / 4 : ℂ) - ((s : ℂ) - 1 / 2) ^ 2 =
      ((s * (1 - s) : ℝ) : ℂ) := by
    push_cast
    ring
  have heq := CuspSchurGlobalPhysical.fullResolvent_eq_actualSchurResolvent_physical hp hh
  rw [hpar] at heq
  rw [spatialOrbitMeanZeroContinuation_eq_fullResolvent_sub_constant s hs hne, heq]

end GapFamily.Analytic.SpatialPoint
