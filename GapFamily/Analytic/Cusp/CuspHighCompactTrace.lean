import GapFamily.Analytic.Modular.Periodization.ModularPeriodizationPairing
import GapFamily.Analytic.Cusp.CuspOrbitHeight
import GapFamily.Analytic.Cusp.Fourier.CuspAverageTrace

/-!
# Zero cusp boundary trace of arbitrary compact high-cusp tests

Every translate of a fundamental-domain point at height at most one remains
below height one. A test supported strictly above that height therefore has
zero periodization there, and its actual completed-form boundary trace vanishes.
-/

noncomputable section
set_option maxHeartbeats 200000
namespace GapFamily.Analytic.CuspHighCompactTrace
open Set MeasureTheory UpperHalfPlane ModularGradient
open scoped ContDiff MatrixGroups

/-- No smoothness or summability premise is needed when every actual summand is zero. -/
theorem modularPeriodization_eq_zero_of_high_support {ψ : ℂ → ℂ}
    (hs : tsupport ψ ⊆ {z : ℂ | 1 < z.im}) {τ : UpperHalfPlane}
    (hτ : τ ∈ ModularGroup.fd) (hh : τ.im ≤ 1) :
    modularPeriodization ψ τ = 0 := by
  rw [modularPeriodization_coe]
  have hz (γ : SL(2, ℤ)) : ψ (γ • τ : UpperHalfPlane) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    exact (not_lt_of_ge ((modular_smul_im_le_of_mem_fd γ hτ).trans hh)) (hs hmem)
  simp only [hz, tsum_zero, mul_zero]

/-- The actual completed-form boundary trace vanishes for every compact high-cusp test. -/
theorem cuspAverageTrace_periodizedUpperCore_of_high_support
    (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ upperHalfPlaneSet)
    (hhigh : tsupport ψ ⊆ {z : ℂ | 1 < z.im}) :
    cuspAverageTrace (coreForm (periodizedUpperCore ψ hψ hc hs)) = 0 := by
  rw [cuspAverageTrace_core]
  change cuspHorizontalAverage (modularPeriodization ψ) 1 = 0
  rw [cuspHorizontalAverage]
  change (∫ x in (-1 / 2 : ℝ)..(1 / 2), modularPeriodization ψ (Complex.mk x 1)) = 0
  apply intervalIntegral.integral_zero_ae
  filter_upwards with x
  intro hx
  rw [uIoc_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 1 / 2)] at hx
  let τ : UpperHalfPlane := ⟨Complex.mk x 1, zero_lt_one⟩
  have hfd : τ ∈ ModularGroup.fd := by
    constructor
    · change 1 ≤ Complex.normSq (Complex.mk x 1)
      simp only [Complex.normSq_apply]
      nlinarith [sq_nonneg x]
    · change |x| ≤ 1 / 2
      exact abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
  simpa only [τ, UpperHalfPlane.coe_mk] using
    modularPeriodization_eq_zero_of_high_support (τ := τ) hhigh hfd le_rfl

end GapFamily.Analytic.CuspHighCompactTrace
