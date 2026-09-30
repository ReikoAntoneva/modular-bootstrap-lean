import GapFamily.Analytic.Poincare.PoincareAnalytic
import GapFamily.Analytic.Modular.ModularHilbert
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
namespace GapFamily.Analytic.PoincareWeak
open Set MeasureTheory

/-- A genuine summable bound for the literal compactly tested cusp terms. -/
theorem exists_test_term_majorant (J : ℤ) {s : ℂ} (hs : 1 < s.re)
    (ψ : ℂ → ℂ) (hc : HasCompactSupport ψ)
    (hψU : tsupport ψ ⊆ UpperHalfPlane.upperHalfPlaneSet) :
    ∃ u : CuspCoset → ℝ, Summable u ∧ (∀ q, 0 ≤ u q) ∧
      ∀ (q : CuspCoset) (z : ℂ),
        ‖star (ψ z) * complexPoincareTerm 0 J s (UpperHalfPlane.ofComplex z) q‖ ≤
          ‖ψ z‖ * u q := by
  have hcont : ContinuousOn UpperHalfPlane.ofComplex (tsupport ψ) := by
    apply UpperHalfPlane.ofComplex.continuousOn.mono
    intro z hz
    simpa [UpperHalfPlane.ofComplex, UpperHalfPlane.range_coe] using hψU hz
  have hK : IsCompact (UpperHalfPlane.ofComplex '' tsupport ψ) :=
    hc.isCompact.image_of_continuousOn hcont
  obtain ⟨M, hM, u, hu, hu0, hub⟩ := exists_cusp_height_compact_majorant hK hs
  refine ⟨u, hu, hu0, ?_⟩
  intro q z
  by_cases hz : z ∈ tsupport ψ
  · rw [norm_mul, norm_star, complexPoincareTerm_out, norm_complexPointSeed]
    simp only [Complex.zero_re, mul_zero, zero_mul, Real.exp_zero, mul_one]
    exact mul_le_mul_of_nonneg_left
      (hub q (UpperHalfPlane.ofComplex z) (mem_image_of_mem _ hz)).2 (norm_nonneg _)
  · have hzero := image_eq_zero_of_notMem_tsupport hz
    simp [hzero]

end GapFamily.Analytic.PoincareWeak
