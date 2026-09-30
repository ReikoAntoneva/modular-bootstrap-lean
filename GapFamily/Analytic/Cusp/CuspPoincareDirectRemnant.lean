import GapFamily.Analytic.Cusp.Fourier.CuspFourierCutoffProfile
import GapFamily.Analytic.Poincare.PoincareAnalytic
import GapFamily.Analytic.Foundation.PositiveBCFPower
import GapFamily.Analytic.Modular.ModularHilbert
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-!
# The weighted direct remainder below the cusp cutoff

The actual direct point seed, multiplied by the complementary cutoff and an
input-height weight, is represented in the modular Hilbert space. Clipping
the height at three gives bounded continuous powers without changing the
cutoff product. Their Banach-valued analyticity supplies Hilbert-norm
analyticity on the stated half-plane. No equation for the full Poincaré
series or membership in a differential-operator domain is asserted here.
-/

noncomputable section
namespace GapFamily.Analytic

open MeasureTheory Set CuspFourierCutoff
open scoped BoundedContinuousFunction

/-- Upper clipping preserves positivity and bounds the height globally. -/
def cuspDirectClippedHeight (τ : UpperHalfPlane) : ℝ := min τ.im 3

theorem continuous_cuspDirectClippedHeight : Continuous cuspDirectClippedHeight :=
  UpperHalfPlane.continuous_im.min continuous_const

theorem cuspDirectClippedHeight_pos (τ : UpperHalfPlane) :
    0 < cuspDirectClippedHeight τ := lt_min τ.im_pos (by norm_num)

theorem cuspDirectClippedHeight_le_three (τ : UpperHalfPlane) :
    cuspDirectClippedHeight τ ≤ 3 := min_le_right _ _

/-- The bounded complementary-cutoff Fourier amplitude. -/
def cuspDirectAmplitude (J : ℤ) (τ : UpperHalfPlane) : ℂ :=
  ((1 - cutoff τ.im : ℝ) : ℂ) * cuspFourierMode J τ.re

theorem continuous_cuspDirectAmplitude (J : ℤ) : Continuous (cuspDirectAmplitude J) :=
  (Complex.continuous_ofReal.comp
    (continuous_const.sub (contDiff_cutoff.continuous.comp UpperHalfPlane.continuous_im))).mul
      ((contDiff_cuspFourierMode J).continuous.comp UpperHalfPlane.continuous_re)

theorem norm_cuspDirectAmplitude_le_one (J : ℤ) (τ : UpperHalfPlane) :
    ‖cuspDirectAmplitude J τ‖ ≤ 1 := by
  have h0 : 0 ≤ cutoff τ.im := Real.smoothTransition.nonneg _
  have h1 : cutoff τ.im ≤ 1 := Real.smoothTransition.le_one _
  rw [cuspDirectAmplitude, norm_mul, norm_cuspFourierMode, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr h1)]
  linarith

def cuspDirectAmplitudeBCF (J : ℤ) : UpperHalfPlane →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (cuspDirectAmplitude J)
    (continuous_cuspDirectAmplitude J) 1 (norm_cuspDirectAmplitude_le_one J)

@[simp] theorem cuspDirectAmplitudeBCF_apply (J : ℤ) (τ : UpperHalfPlane) :
    cuspDirectAmplitudeBCF J τ = cuspDirectAmplitude J τ := rfl

theorem norm_cuspDirectAmplitudeBCF_le_one (J : ℤ) : ‖cuspDirectAmplitudeBCF J‖ ≤ 1 :=
  (BoundedContinuousFunction.norm_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
    (norm_cuspDirectAmplitude_le_one J)

/-- The ordinary weighted direct remainder formed from the literal point seed. -/
def cuspPoincareDirectRemnantTerm (J : ℤ) (α : ℝ) (w : ℂ) (τ : UpperHalfPlane) : ℂ :=
  ((τ.im ^ α : ℝ) : ℂ) * ((1 - cutoff τ.im : ℝ) : ℂ) *
    complexPointSeed 0 J w τ

theorem complexPointSeed_zero_eq_cuspFourierMode (J : ℤ) (w : ℂ) (τ : UpperHalfPlane) :
    complexPointSeed 0 J w τ = (τ.im : ℂ) ^ w * cuspFourierMode J τ.re := by
  simp only [complexPointSeed, mul_zero, zero_mul, zero_add]
  congr 1
  unfold cuspFourierMode
  congr 1
  push_cast
  ring

/-- Upper clipping changes no value of the actual complementary-cutoff product. -/
theorem cuspPoincareDirectRemnantTerm_eq_profile (J : ℤ) (α : ℝ) (w : ℂ)
    (τ : UpperHalfPlane) :
    cuspPoincareDirectRemnantTerm J α w τ =
      cuspDirectAmplitudeBCF J τ * (cuspDirectClippedHeight τ : ℂ) ^ (w + (α : ℂ)) := by
  rw [cuspDirectAmplitudeBCF_apply]
  by_cases hy : τ.im ≤ 3
  · rw [cuspDirectClippedHeight, min_eq_left hy,
      Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr τ.im_pos.ne'),
      ← Complex.ofReal_cpow τ.im_pos.le α]
    rw [cuspPoincareDirectRemnantTerm, complexPointSeed_zero_eq_cuspFourierMode,
      cuspDirectAmplitude]
    ring
  · have hc := cutoff_eq_one (le_of_not_ge hy)
    simp [cuspPoincareDirectRemnantTerm, cuspDirectAmplitude, hc]

/-- A total Hilbert family agreeing with the actual remainder on its analytic domain. -/
def cuspPoincareDirectRemnant (J : ℤ) (α : ℝ) (w : ℂ) : ModularHilbert :=
  BoundedContinuousFunction.toLp 2 modularMeasure ℂ
    (cuspDirectAmplitudeBCF J *
      PositiveBCFPower.positivePower cuspDirectClippedHeight continuous_cuspDirectClippedHeight
        cuspDirectClippedHeight_pos 3 cuspDirectClippedHeight_le_three (w + (α : ℂ)))

/-- Analyticity is in the actual modular Hilbert norm. -/
theorem cuspPoincareDirectRemnant_analyticAt (J : ℤ) (α : ℝ) {w : ℂ}
    (hw : 0 < w.re + α) : AnalyticAt ℂ (cuspPoincareDirectRemnant J α) w := by
  have hp : AnalyticAt ℂ (fun z : ℂ =>
      PositiveBCFPower.positivePower cuspDirectClippedHeight continuous_cuspDirectClippedHeight
        cuspDirectClippedHeight_pos 3 cuspDirectClippedHeight_le_three (z + (α : ℂ))) w :=
    (PositiveBCFPower.positivePower_analyticAt _ _ _ _ _ (by simpa using hw)).comp
      (by fun_prop)
  exact (ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := UpperHalfPlane →ᵇ ℂ)
    (F := ModularHilbert) (BoundedContinuousFunction.toLp 2 modularMeasure ℂ) _).comp_of_eq
      (analyticAt_const.mul hp) rfl

/-- Ordinary almost-everywhere identification, valid on the full exponent half-plane. -/
theorem cuspPoincareDirectRemnant_ae (J : ℤ) (α : ℝ) {w : ℂ} (hw : 0 < w.re + α) :
    cuspPoincareDirectRemnant J α w =ᵐ[modularMeasure] cuspPoincareDirectRemnantTerm J α w := by
  have hp := BoundedContinuousFunction.coeFn_toLp 2 modularMeasure ℂ
    (cuspDirectAmplitudeBCF J *
      PositiveBCFPower.positivePower cuspDirectClippedHeight continuous_cuspDirectClippedHeight
        cuspDirectClippedHeight_pos 3 cuspDirectClippedHeight_le_three (w + (α : ℂ)))
  filter_upwards [hp] with τ hp
  change cuspPoincareDirectRemnant J α w τ = _ at hp
  rw [hp]
  change cuspDirectAmplitudeBCF J τ *
    PositiveBCFPower.positivePower _ _ _ _ _ (w + (α : ℂ)) τ = _
  rw [PositiveBCFPower.positivePower_apply _ _ _ _ _ (by simpa using hw)]
  exact (cuspPoincareDirectRemnantTerm_eq_profile J α w τ).symm

/-- The ordinary remainder has genuine square-integrability, not just a totalized L² value. -/
theorem memLp_cuspPoincareDirectRemnantTerm (J : ℤ) (α : ℝ) {w : ℂ}
    (hw : 0 < w.re + α) : MemLp (cuspPoincareDirectRemnantTerm J α w) 2 modularMeasure :=
  (memLp_congr_ae (cuspPoincareDirectRemnant_ae J α hw)).mp
    (Lp.memLp (cuspPoincareDirectRemnant J α w))

theorem cuspPoincareDirectRemnant_analyticOnNhd (J : ℤ) (α : ℝ) :
    AnalyticOnNhd ℂ (cuspPoincareDirectRemnant J α) {w : ℂ | 0 < w.re + α} :=
  fun _ hw => cuspPoincareDirectRemnant_analyticAt J α hw

theorem cuspPoincareDirectRemnant_zero_weight_analyticAt (J : ℤ) {w : ℂ}
    (hw : 0 < w.re) : AnalyticAt ℂ (cuspPoincareDirectRemnant J 0) w :=
  cuspPoincareDirectRemnant_analyticAt J 0 (by simpa using hw)

/-- The quarter-weight shifted direct remainder is analytic through κ=0. -/
theorem shifted_cuspPoincareDirectRemnant_quarter_analyticAt_zero (J : ℤ) :
    AnalyticAt ℂ (fun κ : ℂ => cuspPoincareDirectRemnant J (1 / 4)
      ((5 / 2 : ℂ) + κ)) 0 :=
  (cuspPoincareDirectRemnant_analyticAt J (1 / 4) (w := (5 / 2 : ℂ))
    (by norm_num)).comp_of_eq (by fun_prop) (by simp)

theorem shifted_cuspPoincareDirectRemnant_zero_weight_analyticAt_zero (J : ℤ) :
    AnalyticAt ℂ (fun κ : ℂ => cuspPoincareDirectRemnant J 0 ((5 / 2 : ℂ) + κ)) 0 :=
  (cuspPoincareDirectRemnant_analyticAt J 0 (w := (5 / 2 : ℂ))
    (by norm_num)).comp_of_eq (by fun_prop) (by simp)

end GapFamily.Analytic
