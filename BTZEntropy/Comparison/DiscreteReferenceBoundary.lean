import BTZEntropy.Comparison.ReferenceTestBoundary
import BTZEntropy.Comparison.DiscreteReferenceSubexponential

/-!
# The fixed boundary band is negligible

The leading reference begins at the fixed tail layer, whereas the actual
tail begins at the selected initial fronts. Their difference stays in one
fixed energy band. Including every descendant does not change its square
root exponential growth in charge.
-/

noncomputable section

open Set Filter Real
open GapFamily GapFamily.Analytic BTZEntropy.Construction

namespace BTZEntropy.Comparison

def fixedFamilyBoundaryPacket {B : ℝ} {g : FixedFamilyGeometry B} {a : ℝ} {δ : ℝ}
    (φ : SmoothKernel) (d : FixedFamilyDatum g a δ) (E : ℝ)
    (F : Finset (ℕ × ℕ)) : ℝ :=
  frontBoundaryTest (shift (gapFamilyCharge a)) g.start d.initialState.front
    (primaryDescendantTest φ E F)

theorem fixedFamilyBoundaryPacket_nonneg {B : ℝ} {g : FixedFamilyGeometry B}
    {a : ℝ} {δ : ℝ} (φ : SmoothKernel) (d : FixedFamilyDatum g a δ)
    (E : ℝ) (F : Finset (ℕ × ℕ)) : 0 ≤ fixedFamilyBoundaryPacket φ d E F :=
  frontBoundaryTest_nonneg (by linarith [d.charge_large]) _ _
    (fun e _ => primaryDescendantTest_nonneg φ E F e)

/-- One bound covers all actual initial fronts and all finite descendant
packets, independently of the selected nodes and marker position. -/
theorem fixedFamilyBoundaryPacket_uniform_sqrt_bound {B : ℝ}
    (g : FixedFamilyGeometry B) (φ : SmoothKernel) (V : ℝ) :
    ∃ A D : ℝ, 0 ≤ A ∧ 0 ≤ D ∧ ∀ (a : ℝ) (δ : ℝ)
      (d : FixedFamilyDatum g a δ) (F : Finset (ℕ × ℕ)) (x : ℝ), x ≤ V →
      fixedFamilyBoundaryPacket φ d (x * gapFamilyCharge a) F ≤
        A * exp (D * sqrt (gapFamilyCharge a)) := by
  obtain ⟨R, H, hR, hH, hsupport, hφ⟩ := exists_kernel_upper_bound φ
  let D₀ : ℝ := max 0 V + R + 1 / 12 + 4
  let D : ℝ := D₀ + 4 * π * sqrt (g.upper + 1)
  have hD₀ : 0 ≤ D₀ := by dsimp [D₀]; positivity
  refine ⟨6 * H * (g.upper + 2) ^ 2, D, by positivity, by dsimp [D]; positivity, ?_⟩
  intro a δ d F x hx
  have hc : 1 ≤ gapFamilyCharge a := by
    have h := d.charge_large
    unfold shift at h
    linarith
  have hac : shift (gapFamilyCharge a) ≤ gapFamilyCharge a := by
    unfold shift
    linarith
  have ha : 0 ≤ shift (gapFamilyCharge a) := by linarith [d.charge_large]
  have hu : 0 ≤ g.upper + 1 := by linarith [g.upper_nonneg]
  have hroot : sqrt (shift (gapFamilyCharge a) * (g.upper + 1)) ≤
      sqrt (gapFamilyCharge a) * sqrt (g.upper + 1) := by
    rw [sqrt_mul ha]
    exact mul_le_mul_of_nonneg_right (sqrt_le_sqrt hac) (sqrt_nonneg _)
  have hbound := fixedFamily_frontBoundaryTest_le_exp d
    (show 0 ≤ H * exp (D₀ * sqrt (gapFamilyCharge a)) by positivity)
    (primaryDescendantTest φ (x * gapFamilyCharge a) F)
    (continuous_primaryDescendantTest φ (x * gapFamilyCharge a) F) (by
      intro e he
      have he0 : 0 ≤ e := (Nat.cast_nonneg g.start).trans he.1.le
      exact primaryDescendantTest_le_sqrt φ F he0 hc
        (hx.trans (le_max_right _ _)) hR hH hsupport hφ)
  change fixedFamilyBoundaryPacket φ d (x * gapFamilyCharge a) F ≤ _ at hbound
  apply hbound.trans
  calc
    _ ≤ 6 * (H * exp (D₀ * sqrt (gapFamilyCharge a))) * (g.upper + 2) ^ 2 *
        exp (4 * π * (sqrt (gapFamilyCharge a) * sqrt (g.upper + 1))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact exp_le_exp.mpr (mul_le_mul_of_nonneg_left hroot (by positivity))
    _ = _ := by
      have heq : D * sqrt (gapFamilyCharge a) =
          D₀ * sqrt (gapFamilyCharge a) +
            4 * π * (sqrt (gapFamilyCharge a) * sqrt (g.upper + 1)) := by
        dsimp only [D]
        ring
      rw [heq, exp_add]
      ring

/-- The boundary subtraction is uniformly negligible at every inverse
power of the saddle count scale. -/
theorem fixedFamilyBoundaryPacket_eventually_saddle_scale {B : ℝ}
    (g : FixedFamilyGeometry B) (φ : SmoothKernel) {L U : ℝ}
    (hL : 0 < L) (P : ℕ) :
    ∀ᶠ a : ℝ in atTop, ∀ (δ : ℝ) (d : FixedFamilyDatum g a δ)
      (F : Finset (ℕ × ℕ)) (x : ℝ), x ∈ Icc L U →
      fixedFamilyBoundaryPacket φ d (x * gapFamilyCharge a) F ≤
        exp (2 * π * gapFamilyCharge a * sqrt (x / 3)) /
          (sqrt (gapFamilyCharge a) * gapFamilyCharge a ^ P) := by
  obtain ⟨A, D, hA, _, hbound⟩ := fixedFamilyBoundaryPacket_uniform_sqrt_bound g φ U
  filter_upwards [subexponential_eventually_gapFamily_le (D := D) hL hA P]
    with a hscale δ d F x hx
  exact (hbound a δ d F x hx.2).trans (hscale x hx.1)

end BTZEntropy.Comparison
