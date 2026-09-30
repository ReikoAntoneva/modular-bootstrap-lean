import GapFamily.Analytic.Spatial.SpatialOrbitPointLaplacian
import GapFamily.Analytic.Cusp.Schur.CuspSchurGlobalPhysical

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open Set Filter MeasureTheory UpperHalfPlane ModularGradient
open scoped ContDiff MatrixGroups

/-- The actual point-source row is the actual Schur resolvent of its literal
shifted source throughout the original complex convergence half-plane. -/
theorem actualSchurResolvent_spatialOrbitPointSource (s : ℂ) (hs : 1 < s.re) (w : UpperHalfPlane) :
    CuspSchur.actualSchurResolvent (s * (1 - s))
      (s ^ 2 • spatialOrbitPointSource (s + 1) w) = spatialOrbitPointSource s w := by
  obtain ⟨hdom, hA⟩ := exists_spatialOrbitPoint_laplacian s hs w
  have hp : 0 < (s - (1 / 2 : ℂ)).re := by
    norm_num [Complex.sub_re]
    linarith
  have hh : s - (1 / 2 : ℂ) ≠ (1 / 2 : ℂ) := by
    intro he
    have he' : s = 1 := by linear_combination he
    rw [he'] at hs
    norm_num at hs
  have he : (1 / 4 : ℂ) - (s - 1 / 2) ^ 2 = s * (1 - s) := by ring
  have hr := CuspSchurGlobalPhysical.actualSchurResolvent_leftInverse_physical hp hh
    ⟨spatialOrbitPointSource s w, hdom⟩
  change CuspSchur.actualSchurResolvent ((1 / 4 : ℂ) - (s - 1 / 2) ^ 2)
    (laplacian ⟨spatialOrbitPointSource s w, hdom⟩ -
      ((1 / 4 : ℂ) - (s - 1 / 2) ^ 2) • spatialOrbitPointSource s w) = _ at hr
  rw [he, hA, add_sub_cancel_left] at hr
  exact hr

/-- The already constructed height-weighted source unweights to the same actual row vector. -/
theorem cuspWeightedInput_spatialOrbitWeightedSource_eq_pointSource
    (α : ℝ) (hα : 0 ≤ α) (hhalf : α < 1 / 2)
    (s : ℂ) (hs : 1 < s.re) (w : UpperHalfPlane) :
    cuspWeightedInput α hα (spatialOrbitWeightedSource α hα hhalf s w) = spatialOrbitPointSource s w :=
  Lp.ext ((cuspWeightedInput_spatialOrbitWeightedSource_ae α hα hhalf s hs w).trans
    (spatialOrbitPointSource_ae s hs w).symm)

/-- Literal weighted-source formulation used by the compact analytic evaluator. -/
theorem actualSchurResolvent_spatialOrbitWeightedSource
    (α : ℝ) (hα : 0 ≤ α) (hhalf : α < 1 / 2)
    (s : ℂ) (hs : 1 < s.re) (w : UpperHalfPlane) :
    CuspSchur.actualSchurResolvent (s * (1 - s))
      (cuspWeightedInput α hα (s ^ 2 • spatialOrbitWeightedSource α hα hhalf (s + 1) w)) =
        spatialOrbitPointSource s w := by
  have hs1 : 1 < (s + 1).re := by simp only [Complex.add_re, Complex.one_re]; linarith
  rw [map_smul, cuspWeightedInput_spatialOrbitWeightedSource_eq_pointSource α hα hhalf (s + 1) hs1 w]
  exact actualSchurResolvent_spatialOrbitPointSource s hs w

end GapFamily.Analytic.SpatialPoint
