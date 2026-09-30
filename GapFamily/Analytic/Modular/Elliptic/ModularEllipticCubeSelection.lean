import Homogenization.Sobolev.Foundations.Cutoff.Cube
import Mathlib.Algebra.Order.Archimedean.Basic

noncomputable section

open scoped Topology
open Homogenization

namespace GapFamily.Analytic.ModularElliptic

/-- Every origin-centered triadic cube has center zero. -/
@[simp] theorem cubeCenter_originCube {d : ℕ} (m : ℤ) :
    cubeCenter (originCube d m) = 0 := by
  ext i
  simp [cubeCenter, originCube]

/-- The origin lies in every positive concentric open subcube. -/
theorem zero_mem_scaledOpenCubeSet_originCube {d : ℕ} (m : ℤ) {ρ : ℝ}
    (hρ : 0 < ρ) :
    (0 : Vec d) ∈ scaledOpenCubeSet (originCube d m) ρ := by
  intro i
  simpa using mul_pos hρ (cubeRadius_pos (originCube d m))

/-- Closed origin-centered triadic cubes can be chosen inside any neighborhood
of zero. The ambient norm is the ordinary finite-product supremum norm used by
the frozen `Homogenization.Vec` API. -/
theorem exists_originCube_closed_subset_of_mem_nhds {d : ℕ} {W : Set (Vec d)}
    (hW : W ∈ 𝓝 (0 : Vec d)) :
    ∃ m : ℤ, scaledClosedCubeSet (originCube d m) 1 ⊆ W := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hW
  obtain ⟨m, hm, _⟩ := exists_mem_Ioc_zpow hε (show (1 : ℝ) < 3 by norm_num)
  refine ⟨m, ?_⟩
  have hrad : cubeRadius (originCube d m) < ε := by
    dsimp [cubeRadius]
    have hpow := zpow_pos (show (0 : ℝ) < 3 by norm_num) m
    linarith
  intro x hx
  apply hball
  have hdist := scaledClosedCubeSet_subset_metricClosedBall
    (originCube d m) (show (0 : ℝ) ≤ 1 by norm_num) hx
  simp only [cubeCenter_originCube, one_mul, Metric.mem_closedBall] at hdist
  exact hdist.trans_lt hrad

/-- A neighborhood of zero contains a closed triadic cube centered at zero,
whose half-sized open cube still contains zero. -/
theorem exists_centered_cube_closed_subset {d : ℕ} {W : Set (Vec d)}
    (hW : IsOpen W) (hzero : (0 : Vec d) ∈ W) :
    ∃ Q : TriadicCube d, cubeCenter Q = 0 ∧
      scaledClosedCubeSet Q 1 ⊆ W ∧
      (0 : Vec d) ∈ scaledOpenCubeSet Q (1 / 2) := by
  obtain ⟨m, hm⟩ := exists_originCube_closed_subset_of_mem_nhds (hW.mem_nhds hzero)
  exact ⟨originCube d m, cubeCenter_originCube m, hm,
    zero_mem_scaledOpenCubeSet_originCube m (by norm_num)⟩

end GapFamily.Analytic.ModularElliptic
