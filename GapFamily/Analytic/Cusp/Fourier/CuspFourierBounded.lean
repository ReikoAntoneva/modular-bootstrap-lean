import GapFamily.Analytic.Cusp.Fourier.CuspFourierProfileMeanZero
import GapFamily.Analytic.Cusp.Schur.CuspLocalSchurEvaluation
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

noncomputable section
namespace GapFamily.Analytic.CuspFourierCutoff
open Set MeasureTheory ModularGradient
open scoped ContDiff BoundedContinuousFunction

def boundedProfile (b : ℝ → ℂ) (hb : Continuous b) (hc : HasCompactSupport b) : ℝ →ᵇ ℂ :=
  ⟨⟨b, hb⟩, Metric.isBounded_range_iff.mp (hc.isCompact_range hb).isBounded⟩

def boundedMode (J : ℤ) : UpperHalfPlane →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun τ => cuspFourierMode J τ.re)
    ((contDiff_cuspFourierMode J).continuous.comp UpperHalfPlane.continuous_re)
    1 (by intro τ; simp)

def boundedFourierProfile (J : ℤ) (b : ℝ → ℂ)
    (hb : Continuous b) (hc : HasCompactSupport b) : UpperHalfPlane →ᵇ ℂ :=
  (boundedProfile b hb hc).compContinuous
    ⟨UpperHalfPlane.im, UpperHalfPlane.continuous_im⟩ * boundedMode J

@[simp] theorem boundedFourierProfile_apply (J : ℤ) (b : ℝ → ℂ)
    (hb : Continuous b) (hc : HasCompactSupport b) (τ : UpperHalfPlane) :
    boundedFourierProfile J b hb hc τ = b τ.im * cuspFourierMode J τ.re := rfl

theorem boundedFourierProfile_toLp (J : ℤ) (b : ℝ → ℂ)
    (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b) (hs : tsupport b ⊆ Ioi 1) :
    BoundedContinuousFunction.toLp 2 modularMeasure ℂ
      (boundedFourierProfile J b hb.continuous hc) =
      value (cuspFourierProfileCore J b hb hc hs) := by
  apply Lp.ext
  exact (BoundedContinuousFunction.coeFn_toLp _ _ _ _).trans
    (cuspFourierProfileCore_value_ae J b hb hc hs).symm

def clampedHeight (τ : UpperHalfPlane) : Icc (2 : ℝ) 3 :=
  ⟨max 2 (min 3 τ.im), le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem continuous_clampedHeight : Continuous clampedHeight := by
  unfold clampedHeight
  fun_prop

def boundedLogHeight : UpperHalfPlane →ᵇ ℂ :=
  (BoundedContinuousFunction.mkOfCompact
    ⟨fun y : Icc (2 : ℝ) 3 => (Real.log y : ℂ),
      Complex.continuous_ofReal.comp
        (Real.continuousOn_log.comp_continuous continuous_subtype_val
          (by intro y; exact ne_of_gt (lt_of_lt_of_le (by norm_num) y.property.1)))⟩).compContinuous
    ⟨clampedHeight, continuous_clampedHeight⟩

@[simp] theorem boundedLogHeight_apply (τ : UpperHalfPlane) :
    boundedLogHeight τ = (Real.log (max 2 (min 3 τ.im)) : ℂ) := rfl

theorem boundedLogHeight_apply_of_mem (τ : UpperHalfPlane) (hτ : τ.im ∈ Icc (2 : ℝ) 3) :
    boundedLogHeight τ = (Real.log τ.im : ℂ) := by
  simp [boundedLogHeight_apply, min_eq_right hτ.2, max_eq_right hτ.1]

end GapFamily.Analytic.CuspFourierCutoff
