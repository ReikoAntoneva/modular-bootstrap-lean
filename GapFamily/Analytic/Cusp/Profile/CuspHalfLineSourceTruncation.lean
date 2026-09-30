import GapFamily.Analytic.Cusp.Profile.CuspHalfLineSourceEmbedding
import GapFamily.Analytic.Modular.Geometry.ModularTruncatedIndicator

noncomputable section

namespace GapFamily.Analytic

open Set MeasureTheory

/-- Literal restriction to logarithmic heights at most `T`, with zero extension
inside the ordinary positive half-line Hilbert space. -/
def cuspHalfLineSourceTruncation (T : ℝ) (f : cuspHalfLineSourceHilbert) :
    cuspHalfLineSourceHilbert :=
  (MemLp.indicator measurableSet_Iic (Lp.memLp f)).toLp ((Iic T).indicator f)

theorem cuspHalfLineSourceTruncation_ae (T : ℝ) (f : cuspHalfLineSourceHilbert) :
    cuspHalfLineSourceTruncation T f =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (Iic T).indicator f :=
  MemLp.coeFn_toLp _

/-- The actual logarithmic indicator is exactly the physical modular height
cutoff after the proved half-line isometry, including the cutoff boundary. -/
theorem cuspHalfLineSourceEmbedding_truncation (T : ℝ) (f : cuspHalfLineSourceHilbert) :
    cuspHalfLineSourceEmbedding (cuspHalfLineSourceTruncation T f) =
      modularLowCut (Real.exp T) (cuspHalfLineSourceEmbedding f) := by
  have hlog := cuspHalfLine_ae_log_modular (cuspHalfLineSourceTruncation_ae T f)
  apply Lp.ext
  filter_upwards [cuspHalfLineSourceEmbedding_ae (cuspHalfLineSourceTruncation T f),
    modularLowCut_ae (Real.exp T) (cuspHalfLineSourceEmbedding f),
    cuspHalfLineSourceEmbedding_ae f, hlog] with τ htr hcut hf hlog
  rw [htr, hcut]
  by_cases hy : 1 < τ.im
  · rw [ite_eq_left hy, hlog hy]
    have hiff : Real.log τ.im ≤ T ↔ τ.im ≤ Real.exp T :=
      Real.log_le_iff_le_exp τ.im_pos
    by_cases hτ : τ.im ≤ Real.exp T
    · have ht : Real.log τ.im ≤ T := hiff.mpr hτ
      simp [Set.indicator, hτ, ht, hf, hy]
    · have ht : Real.log τ.im ∉ Iic T := fun h => hτ (hiff.mp h)
      simp [Set.indicator, hτ, ht]
  · simp only [ite_eq_right hy]
    by_cases hτ : τ.im ≤ Real.exp T
    · simp [Set.indicator, hτ, hf, hy]
    · simp [Set.indicator, hτ]

/-- The literal logarithmic truncation is a contraction in the original source norm. -/
theorem cuspHalfLineSourceTruncation_norm_le (T : ℝ) (f : cuspHalfLineSourceHilbert) :
    ‖cuspHalfLineSourceTruncation T f‖ ≤ ‖f‖ := by
  rw [← cuspHalfLineSourceEmbedding_norm, cuspHalfLineSourceEmbedding_truncation]
  exact (norm_modularLowCut_le (Real.exp T) _).trans_eq (cuspHalfLineSourceEmbedding_norm f)

theorem cuspHalfLineSourceTruncation_add (T : ℝ) (f g : cuspHalfLineSourceHilbert) :
    cuspHalfLineSourceTruncation T (f + g) =
      cuspHalfLineSourceTruncation T f + cuspHalfLineSourceTruncation T g := by
  apply cuspHalfLineSourceEmbedding.injective
  simp only [cuspHalfLineSourceEmbedding_truncation, map_add]

theorem cuspHalfLineSourceTruncation_smul (T : ℝ) (c : ℂ) (f : cuspHalfLineSourceHilbert) :
    cuspHalfLineSourceTruncation T (c • f) = c • cuspHalfLineSourceTruncation T f := by
  apply cuspHalfLineSourceEmbedding.injective
  simp only [cuspHalfLineSourceEmbedding_truncation, map_smul]

/-- Bounded linear packaging of the literal source indicator, for composition
with parameter-dependent Hilbert families. -/
def cuspHalfLineSourceTruncationCLM (T : ℝ) :
    cuspHalfLineSourceHilbert →L[ℂ] cuspHalfLineSourceHilbert :=
  ({ toFun := cuspHalfLineSourceTruncation T
     map_add' := cuspHalfLineSourceTruncation_add T
     map_smul' := cuspHalfLineSourceTruncation_smul T } :
      cuspHalfLineSourceHilbert →ₗ[ℂ] cuspHalfLineSourceHilbert).mkContinuous 1
        (fun f => by
          change ‖cuspHalfLineSourceTruncation T f‖ ≤ 1 * ‖f‖
          simpa only [one_mul] using cuspHalfLineSourceTruncation_norm_le T f)

@[simp] theorem cuspHalfLineSourceTruncationCLM_apply (T : ℝ)
    (f : cuspHalfLineSourceHilbert) :
    cuspHalfLineSourceTruncationCLM T f = cuspHalfLineSourceTruncation T f := rfl

theorem cuspHalfLineSourceTruncationCLM_norm_le (T : ℝ) :
    ‖cuspHalfLineSourceTruncationCLM T‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖cuspHalfLineSourceTruncation T f‖ ≤ 1 * ‖f‖
  simpa only [one_mul] using cuspHalfLineSourceTruncation_norm_le T f

end GapFamily.Analytic
