import GapFamily.Analytic.Modular.Geometry.ModularCoordinate
import Mathlib.Analysis.Convex.PathConnected

/-!
# Connectivity of the actual open modular region

The region is star-convex about `2i`, even though it is not convex. This is the
geometric input needed to pass from local weak constancy to a global constant.
-/

namespace GapFamily.Analytic

open Set Complex

/-- Coordinate characterization retaining the strict circle and side boundaries. -/
theorem mem_modularInterior_iff {z : ℂ} :
    z ∈ modularInterior ↔ 0 < z.im ∧ 1 < Complex.normSq z ∧ |z.re| < 1 / 2 := by
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    exact ⟨τ.im_pos, hτ⟩
  · rintro ⟨hz, hnorm, hre⟩
    exact ⟨⟨z, hz⟩, ⟨hnorm, hre⟩, rfl⟩

theorem two_I_mem_modularInterior : (2 * I : ℂ) ∈ modularInterior := by
  rw [mem_modularInterior_iff]
  norm_num [Complex.normSq_apply]

/-- Every straight segment from `2i` stays inside the genuine open fundamental region. -/
theorem starConvex_modularInterior : StarConvex ℝ (2 * I : ℂ) modularInterior := by
  intro z hz a b ha hb hab
  have hhalf : 1 / 2 < z.im := by
    obtain ⟨τ, hτ, rfl⟩ := hz
    exact one_half_lt_im_of_mem_fd (ModularGroup.fdo_subset_fd hτ)
  rcases mem_modularInterior_iff.mp hz with ⟨hy, hnorm, hx⟩
  rw [mem_modularInterior_iff]
  norm_num [Complex.normSq_apply, Complex.real_smul]
  constructor
  · nlinarith
  constructor
  · by_cases ha0 : a = 0
    · have hb1 : b = 1 := by linarith
      simpa [ha0, hb1, Complex.normSq_apply] using hnorm
    · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      have hnorm' : 1 < z.re ^ 2 + z.im ^ 2 := by
        simpa [Complex.normSq_apply, pow_two] using hnorm
      have h1 := mul_le_mul_of_nonneg_left hnorm'.le (sq_nonneg b)
      have h2 := mul_le_mul_of_nonneg_left hhalf.le (mul_nonneg ha hb)
      nlinarith [sq_pos_of_pos hap, sq_nonneg (a + b - 1)]
  · rw [abs_of_nonneg hb]
    have hb1 : b ≤ 1 := by linarith
    exact (mul_le_mul_of_nonneg_right hb1 (abs_nonneg z.re)).trans_lt (by simpa using hx)

theorem isPathConnected_modularInterior : IsPathConnected modularInterior :=
  starConvex_modularInterior.isPathConnected two_I_mem_modularInterior

theorem isConnected_modularInterior : IsConnected modularInterior :=
  isPathConnected_modularInterior.isConnected

end GapFamily.Analytic
