import GapFamily.Analytic.Cusp.Fourier.CuspFourierProfileCore
import GapFamily.Analytic.Cusp.MeanZero.CuspMeanZeroForm
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Actual zero cusp average of nonzero compact Fourier profiles

The ordinary width-one phase integral vanishes for every nonzero integer.
The actual bounded cusp-average map then places the constructed profile in
its genuine closed form-domain kernel.
-/

noncomputable section

namespace GapFamily.Analytic

open Set MeasureTheory UpperHalfPlane ModularGradient
open scoped ContDiff

/-- The actual integer phase is ordinarily integrable on every finite interval. -/
theorem cuspFourierMode_intervalIntegrable (n : ℤ) (a b : ℝ) :
    IntervalIntegrable (cuspFourierMode n) volume a b :=
  (contDiff_cuspFourierMode n).continuous.intervalIntegrable a b

/-- The ordinary horizontal integral is zero for every nonzero integer mode,
including negative modes. -/
theorem integral_cuspFourierMode_eq_zero (n : ℤ) (hn : n ≠ 0) :
    (∫ x in (-1/2 : ℝ)..(1/2), cuspFourierMode n x) = 0 := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hc : 2*(Real.pi : ℂ)*Complex.I*(n : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero) hnC
  have hend : cuspFourierMode n (1/2) = cuspFourierMode n (-1/2) := by
    convert cuspFourierMode_add_int n (-1/2) 1 using 1
    norm_num
  change (∫ x in (-1/2 : ℝ)..(1/2),
    Complex.exp ((2*(Real.pi : ℂ)*Complex.I*(n : ℂ))*(x : ℂ))) = 0
  rw [integral_exp_mul_complex hc]
  change (cuspFourierMode n (1/2)-cuspFourierMode n (-1/2)) /
    (2*(Real.pi : ℂ)*Complex.I*(n : ℂ)) = 0
  rw [hend, sub_self, zero_div]

/-- The actual core average on every closed high-cusp slice is the profile
value times the ordinary phase integral. -/
theorem cuspFourierProfileCore_horizontalAverage (n : ℤ) (b : ℝ → ℂ)
    (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b) (hs : tsupport b ⊆ Ioi (1 : ℝ))
    {y : ℝ} (hy : 1 ≤ y) :
    cuspHorizontalAverage (cuspFourierProfileCore n b hb hc hs).val y =
      b y * ∫ x in (-1/2 : ℝ)..(1/2), cuspFourierMode n x := by
  change (∫ x in (-1/2 : ℝ)..(1/2),
    cuspHorizontalSlice (cuspFourierProfileCore n b hb hc hs).val y x) = _
  calc
    _ = ∫ x in (-1/2 : ℝ)..(1/2), b y * cuspFourierMode n x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le (by norm_num : (-1/2 : ℝ) ≤ 1/2)] at hx
      let τ : UpperHalfPlane := ⟨Complex.mk x y, lt_of_lt_of_le zero_lt_one hy⟩
      have hfd : τ ∈ ModularGroup.fd := by
        constructor
        · change 1 ≤ Complex.normSq (Complex.mk x y)
          simp only [Complex.normSq_apply]
          nlinarith [sq_nonneg x]
        · change |x| ≤ 1/2
          exact abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
      exact cuspFourierProfileCore_eq_on_fd n b hb hc hs (τ := τ) hfd
    _ = _ := intervalIntegral.integral_const_mul _ _

/-- Every nonzero integer compact profile has zero ordinary cusp average,
including at height one and at the horizontal seam endpoints. -/
theorem cuspFourierProfileCore_horizontalAverage_eq_zero (n : ℤ) (hn : n ≠ 0)
    (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b)
    (hs : tsupport b ⊆ Ioi (1 : ℝ)) {y : ℝ} (hy : 1 ≤ y) :
    cuspHorizontalAverage (cuspFourierProfileCore n b hb hc hs).val y = 0 := by
  rw [cuspFourierProfileCore_horizontalAverage n b hb hc hs hy,
    integral_cuspFourierMode_eq_zero n hn, mul_zero]

/-- The genuine completed-form cusp-average vector vanishes. -/
theorem cuspFormAverage_cuspFourierProfileCore (n : ℤ) (hn : n ≠ 0)
    (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b)
    (hs : tsupport b ⊆ Ioi (1 : ℝ)) :
    cuspFormAverage (coreForm (cuspFourierProfileCore n b hb hc hs)) = 0 := by
  apply Lp.ext
  filter_upwards [cuspFormAverage_core_ae (cuspFourierProfileCore n b hb hc hs),
    ae_restrict_mem (μ := modularMeasure) (measurableSet_highCusp 1),
    Lp.coeFn_zero (E := ℂ) (p := 2)
      (μ := modularMeasure.restrict {τ : UpperHalfPlane | 1 < τ.im})] with τ hτ hheight hzero
  rw [hτ, hzero]
  exact cuspFourierProfileCore_horizontalAverage_eq_zero n hn b hb hc hs hheight.le

/-- Nonzero compact Fourier forcing belongs to the actual zero-average closed
form space, with all membership conditions discharged by its constructed core. -/
theorem cuspFourierProfileCore_mem_cuspMeanZeroForm (n : ℤ) (hn : n ≠ 0)
    (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b)
    (hs : tsupport b ⊆ Ioi (1 : ℝ)) :
    coreForm (cuspFourierProfileCore n b hb hc hs) ∈ cuspMeanZeroForm :=
  cuspFormAverage_cuspFourierProfileCore n hn b hb hc hs

end GapFamily.Analytic
