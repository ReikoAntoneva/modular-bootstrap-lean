import GapFamily.Analytic.Spatial.SpatialOrbitRowIntegrable
import GapFamily.Analytic.Modular.ModularMeasureSupport

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open Set Filter MeasureTheory UpperHalfPlane
open scoped Topology MatrixGroups

/-- Absolute values of the actual complex orbit sum are dominated by any smaller
real exponent in the genuine convergence half-plane. -/
theorem spatialOrbitKernel_norm_le_real_exponent {σ : ℝ} (hσ : 1 < σ)
    {s : ℂ} (hσs : σ ≤ s.re) (z w : UpperHalfPlane) :
    ‖spatialOrbitKernel s z w‖ ≤ ‖spatialOrbitKernel (σ : ℂ) z w‖ := by
  have hs : 1 < s.re := hσ.trans_le hσs
  rw [spatialOrbitKernel_eq_half_tsum_right, norm_mul,
    norm_spatialOrbitKernel_eq_half_tsum_norm σ hσ]
  norm_num only [norm_div, norm_one, Complex.norm_ofNat]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact (norm_tsum_le_tsum_norm (summable_norm_spatialOrbit s hs z w)).trans
    ((summable_norm_spatialOrbit s hs z w).tsum_le_tsum
      (fun γ => pointKernel_norm_le_real_exponent hσs z (γ • w))
      (summable_norm_spatialOrbit_real σ hσ z w))

/-- The positive real kernel has the same local comparison in its source point. -/
theorem spatialOrbitKernel_norm_local_comparison_right (σ : ℝ) (hσ : 1 < σ)
    (z w w' : UpperHalfPlane) (hd : ‖(w' : ℂ) - (w : ℂ)‖ ≤ w.im / 2) :
    ‖spatialOrbitKernel (σ : ℂ) z w'‖ ≤ (8 : ℝ)^σ * ‖spatialOrbitKernel (σ : ℂ) z w‖ ∧
      ‖spatialOrbitKernel (σ : ℂ) z w‖ ≤ (8 : ℝ)^σ * ‖spatialOrbitKernel (σ : ℂ) z w'‖ := by
  simpa only [spatialOrbitKernel_symm (σ : ℂ) z] using
    spatialOrbitKernel_norm_local_comparison σ hσ w w' z hd

/-- At a source in the closed fundamental domain, positive local modular mass
and the exact row mass give a finite bound uniform over every target point. -/
theorem exists_spatialOrbitKernel_bound_of_mem_fd (σ : ℝ) (hσ : 1 < σ)
    (w : UpperHalfPlane) (hw : w ∈ ModularGroup.fd) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : UpperHalfPlane,
      ‖spatialOrbitKernel (σ : ℂ) z w‖ ≤ C := by
  let B : Set UpperHalfPlane := {w' | ‖(w' : ℂ) - (w : ℂ)‖ < w.im / 2}
  have hB : IsOpen B := isOpen_lt
    (UpperHalfPlane.continuous_coe.sub continuous_const).norm continuous_const
  have hwB : w ∈ B := by simpa [B] using half_pos w.im_pos
  have hwS : w ∈ modularMeasure.support := by rwa [modularMeasure_support]
  have hmass : 0 < modularMeasure B :=
    (Measure.mem_support_iff_forall w).mp hwS B (hB.mem_nhds hwB)
  have hm : 0 < modularMeasure.real B :=
    ENNReal.toReal_pos hmass.ne' (measure_ne_top modularMeasure B)
  let C : ℝ := (8 : ℝ)^σ * (Real.pi / (σ - 1)) / modularMeasure.real B
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro z
  have hi := integrable_norm_spatialOrbitKernel_column σ hσ z
  have hle : modularMeasure.real B * ‖spatialOrbitKernel (σ : ℂ) z w‖ ≤
      (8 : ℝ)^σ * ∫ w' in B, ‖spatialOrbitKernel (σ : ℂ) z w'‖ ∂modularMeasure := by
    have h := integral_mono_ae
      (integrable_const (‖spatialOrbitKernel (σ : ℂ) z w‖))
      (hi.restrict.const_mul ((8 : ℝ)^σ))
      (by
        filter_upwards [ae_restrict_mem hB.measurableSet] with w' hw'
        exact (spatialOrbitKernel_norm_local_comparison_right σ hσ z w w' hw'.le).2)
    simpa only [integral_const, Measure.real, Measure.restrict_apply_univ,
      smul_eq_mul, integral_const_mul] using h
  have hmass_le : (∫ w' in B, ‖spatialOrbitKernel (σ : ℂ) z w'‖ ∂modularMeasure) ≤
      Real.pi / (σ - 1) := by
    rw [← integral_norm_spatialOrbitKernel_column σ hσ z]
    exact setIntegral_le_integral hi (Eventually.of_forall (fun _ => norm_nonneg _))
  apply (le_div_iff₀ hm).mpr
  rw [mul_comm]
  exact hle.trans (mul_le_mul_of_nonneg_left hmass_le (Real.rpow_nonneg (by norm_num) _))

/-- Modular reduction transports the actual bound to every source in the upper half-plane. -/
theorem exists_spatialOrbitKernel_bound (σ : ℝ) (hσ : 1 < σ) (w : UpperHalfPlane) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : UpperHalfPlane,
      ‖spatialOrbitKernel (σ : ℂ) z w‖ ≤ C := by
  obtain ⟨γ, hγ⟩ := ModularGroup.exists_smul_mem_fd w
  obtain ⟨C, hC, hb⟩ := exists_spatialOrbitKernel_bound_of_mem_fd σ hσ (γ • w) hγ
  exact ⟨C, hC, fun z => by simpa only [spatialOrbitKernel_modular_right] using hb z⟩

/-- A single bound works for every target, nearby sources, and the entire closed
exponent half-plane Re(s) ≥ σ > 1. -/
theorem exists_spatialOrbitKernel_locally_uniform_bound (σ : ℝ) (hσ : 1 < σ)
    (w : UpperHalfPlane) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : ℂ) (w' z : UpperHalfPlane),
      σ ≤ s.re → ‖(w' : ℂ) - (w : ℂ)‖ ≤ w.im / 2 →
      ‖spatialOrbitKernel s z w'‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := exists_spatialOrbitKernel_bound σ hσ w
  refine ⟨(8 : ℝ)^σ * C, mul_nonneg (Real.rpow_nonneg (by norm_num) _) hC, ?_⟩
  intro s w' z hs hw
  exact (spatialOrbitKernel_norm_le_real_exponent hσ hs z w').trans
    (((spatialOrbitKernel_norm_local_comparison_right σ hσ z w w' hw).1).trans
      (mul_le_mul_of_nonneg_left (hb z) (Real.rpow_nonneg (by norm_num) _)))

end GapFamily.Analytic.SpatialPoint
