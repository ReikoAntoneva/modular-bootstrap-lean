import GapFamily.Analytic.Cusp.MeanZero.CuspMeanZeroGap
import GapFamily.Analytic.Cusp.MeanZero.CuspMeanZeroPencilRegular
import GapFamily.Analytic.Foundation.PositiveQuarterPencil

noncomputable section
namespace GapFamily.Analytic.CuspMeanZeroGlobalUnit

/-- The proved constrained geometric gap is stronger than the generic quarter bound. -/
theorem actualMeanZero_norm_le_four_fifths :
    ‖cuspMeanZeroWeakResolvent‖ ≤ (4 / 5 : ℝ) :=
  cuspMeanZeroWeakResolvent_norm_le_five_sevenths.trans (by norm_num)

/-- The actual constrained pencil is regular off the real ray strictly above one quarter.
Its quarter endpoint uses the strict geometric gap, not an assumed spectral exclusion. -/
theorem cuspMeanZeroPencil_isUnit_regular_closed {z : ℂ}
    (hz : z.im ≠ 0 ∨ z.re ≤ (1 / 4 : ℝ)) : IsUnit (cuspMeanZeroPencil z) := by
  rcases hz with him | hre
  · exact cuspMeanZeroPencil_isUnit_of_im_ne_zero z him
  · by_cases hlt : z.re < (1 / 4 : ℝ)
    · exact positiveQuarterPencil_isUnit cuspMeanZeroWeakResolvent
        cuspMeanZeroWeakResolvent_isPositive actualMeanZero_norm_le_four_fifths (Or.inr hlt)
    · by_cases him : z.im = 0
      · have hzq : z = (1 / 4 : ℂ) := by
          apply Complex.ext
          · norm_num
            exact le_antisymm hre (le_of_not_gt hlt)
          · simpa using him
        rw [hzq]
        exact cuspMeanZeroPencil_isUnit_quarter
      · exact cuspMeanZeroPencil_isUnit_of_im_ne_zero z him

/-- Every complex spectral parameter with real part at most one quarter is an actual unit. -/
theorem cuspMeanZeroPencil_isUnit_of_re_le_quarter (z : ℂ) (hz : z.re ≤ (1 / 4 : ℝ)) :
    IsUnit (cuspMeanZeroPencil z) :=
  cuspMeanZeroPencil_isUnit_regular_closed (Or.inr hz)

/-- Every real spectral parameter at or below one quarter is an actual unit. -/
theorem cuspMeanZeroPencil_isUnit_of_real_le_quarter (t : ℝ) (ht : t ≤ (1 / 4 : ℝ)) :
    IsUnit (cuspMeanZeroPencil (t : ℂ)) :=
  cuspMeanZeroPencil_isUnit_of_re_le_quarter t ht

/-- The actual constrained pencil is a unit throughout the full physical κ half-plane. -/
theorem cuspMeanZeroPencil_isUnit_physical {κ : ℂ} (hκ : 0 < κ.re) :
    IsUnit (cuspMeanZeroPencil ((1 / 4 : ℂ) - κ ^ 2)) :=
  positiveQuarterPencil_isUnit_physical cuspMeanZeroWeakResolvent
    cuspMeanZeroWeakResolvent_isPositive actualMeanZero_norm_le_four_fifths hκ

/-- Every possible singularity of the actual constrained pencil lies strictly above one quarter. -/
theorem cuspMeanZeroPencil_nonunit_real_gt_quarter (z : ℂ)
    (hz : ¬ IsUnit (cuspMeanZeroPencil z)) : z.im = 0 ∧ (1 / 4 : ℝ) < z.re := by
  constructor
  · by_contra him
    exact hz (cuspMeanZeroPencil_isUnit_regular_closed (Or.inl him))
  · by_contra! hre
    exact hz (cuspMeanZeroPencil_isUnit_regular_closed (Or.inr hre))

end GapFamily.Analytic.CuspMeanZeroGlobalUnit
