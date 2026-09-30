import GapFamily.Analytic.Cusp.Profile.CuspProfileCore
import GapFamily.Analytic.Cusp.Fourier.CuspAverageTrace

/-!
# Vanishing boundary trace of compact scalar cusp profiles

Every point of the width-one horizontal segment at height one belongs to the
closed modular domain. The genuine scalar lift therefore equals its literal
profile there, and the support condition makes that profile value zero.
-/

namespace GapFamily.Analytic

open Set MeasureTheory UpperHalfPlane ModularGradient
open scoped ContDiff

/-- The actual completed-form cusp-average trace vanishes on every compact
scalar cusp profile supported strictly above height one. -/
@[simp] theorem cuspAverageTrace_cuspProfileCore (b : ℝ → ℂ)
    (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b)
    (hs : tsupport b ⊆ Ioi (1 : ℝ)) :
    cuspAverageTrace (coreForm (cuspProfileCore b hb hc hs)) = 0 := by
  have hb1 : b 1 = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => (lt_irrefl (1 : ℝ)) (hs h))
  rw [cuspAverageTrace_core, cuspHorizontalAverage]
  calc
    (∫ x in (-1 / 2 : ℝ)..(1 / 2),
      cuspHorizontalSlice (cuspProfileCore b hb hc hs).val 1 x) =
        ∫ _x in (-1 / 2 : ℝ)..(1 / 2), (0 : ℂ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 1 / 2)] at hx
      let τ : UpperHalfPlane := ⟨Complex.mk x 1, zero_lt_one⟩
      have hfd : τ ∈ ModularGroup.fd := by
        constructor
        · change 1 ≤ Complex.normSq (Complex.mk x 1)
          simp only [Complex.normSq_apply]
          nlinarith [sq_nonneg x]
        · change |x| ≤ 1 / 2
          exact abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
      exact (cuspProfileCore_eq_on_fd b hb hc hs (τ := τ) hfd).trans hb1
    _ = 0 := by simp

end GapFamily.Analytic
