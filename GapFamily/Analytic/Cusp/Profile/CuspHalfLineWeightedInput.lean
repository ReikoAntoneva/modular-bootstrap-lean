import GapFamily.Analytic.Cusp.Profile.CuspHalfLineSourceTruncation
import GapFamily.Analytic.Cusp.Profile.CuspWeightedInput

noncomputable section

namespace GapFamily.Analytic

open Set MeasureTheory

private theorem halfLineWeight_memLp (α : ℝ) (hα : 0 ≤ α)
    (f : cuspHalfLineSourceHilbert) :
    MemLp (fun t : ℝ => (Real.exp (-α * t) : ℂ) * f t) 2
      (volume.restrict (Ioi (0 : ℝ))) := by
  have hw : Continuous (fun t : ℝ => (Real.exp (-α * t) : ℂ)) := by fun_prop
  apply (Lp.memLp f).of_le_mul (c := 1)
    (hw.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have he : Real.exp (-α * t) ≤ 1 := Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hα) ht.le)
  change ‖(Real.exp (-α * t) : ℂ) * f t‖ ≤ 1 * ‖f t‖
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_right he (norm_nonneg _)

private def halfLineWeightValue (α : ℝ) (hα : 0 ≤ α)
    (f : cuspHalfLineSourceHilbert) : cuspHalfLineSourceHilbert :=
  (halfLineWeight_memLp α hα f).toLp _

private theorem halfLineWeightValue_ae (α : ℝ) (hα : 0 ≤ α)
    (f : cuspHalfLineSourceHilbert) :
    halfLineWeightValue α hα f =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun t : ℝ => (Real.exp (-α * t) : ℂ) * f t) :=
  MemLp.coeFn_toLp _

/-- Multiplication by the actual real exponential decay on the full source half-line. -/
def cuspHalfLineWeight (α : ℝ) (hα : 0 ≤ α) :
    cuspHalfLineSourceHilbert →L[ℂ] cuspHalfLineSourceHilbert :=
  LinearMap.mkContinuous
    { toFun := halfLineWeightValue α hα
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [halfLineWeightValue_ae α hα (f + g),
          halfLineWeightValue_ae α hα f, halfLineWeightValue_ae α hα g,
          Lp.coeFn_add f g,
          Lp.coeFn_add (halfLineWeightValue α hα f) (halfLineWeightValue α hα g)]
          with t hfg hf hg hin hout
        simp only [Pi.add_apply] at hin hout
        rw [hfg, hout, hin, hf, hg]
        exact mul_add _ _ _
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [halfLineWeightValue_ae α hα (c • f),
          halfLineWeightValue_ae α hα f, Lp.coeFn_smul c f,
          Lp.coeFn_smul c (halfLineWeightValue α hα f)] with t hcf hf hin hout
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply] at hin hout ⊢
        rw [hcf, hout, hin, hf]
        ring }
    1 (fun f => by
      change ‖halfLineWeightValue α hα f‖ ≤ 1 * ‖f‖
      rw [one_mul]
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [halfLineWeightValue_ae α hα f,
        ae_restrict_mem measurableSet_Ioi] with t ht hpos
      have he : Real.exp (-α * t) ≤ 1 := Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hα) hpos.le)
      rw [ht, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact (mul_le_mul_of_nonneg_right he (norm_nonneg _)).trans_eq (one_mul _))

/-- The bounded operator has the literal exponential multiplier as its representative. -/
theorem cuspHalfLineWeight_ae (α : ℝ) (hα : 0 ≤ α) (f : cuspHalfLineSourceHilbert) :
    cuspHalfLineWeight α hα f =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun t : ℝ => (Real.exp (-α * t) : ℂ) * f t) :=
  halfLineWeightValue_ae α hα f

theorem cuspHalfLineWeight_norm_le (α : ℝ) (hα : 0 ≤ α) :
    ‖cuspHalfLineWeight α hα‖ ≤ 1 := by
  unfold cuspHalfLineWeight
  exact LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- The real exponential multiplier is symmetric in the actual half-line Hilbert space. -/
theorem cuspHalfLineWeight_inner (α : ℝ) (hα : 0 ≤ α)
    (f g : cuspHalfLineSourceHilbert) :
    inner ℂ (cuspHalfLineWeight α hα f) g = inner ℂ f (cuspHalfLineWeight α hα g) := by
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [cuspHalfLineWeight_ae α hα f, cuspHalfLineWeight_ae α hα g]
    with t hf hg
  rw [hf, hg]
  simp only [RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring


/-- The literal source decay and finite-height indicator commute. -/
theorem cuspHalfLineWeight_truncation (α : ℝ) (hα : 0 ≤ α) (T : ℝ)
    (f : cuspHalfLineSourceHilbert) :
    cuspHalfLineWeight α hα (cuspHalfLineSourceTruncation T f) =
      cuspHalfLineSourceTruncation T (cuspHalfLineWeight α hα f) := by
  apply Lp.ext
  filter_upwards [cuspHalfLineWeight_ae α hα (cuspHalfLineSourceTruncation T f),
    cuspHalfLineSourceTruncation_ae T f,
    cuspHalfLineSourceTruncation_ae T (cuspHalfLineWeight α hα f),
    cuspHalfLineWeight_ae α hα f] with t hw ht htw hf
  rw [hw, ht, htw]
  by_cases h : t ≤ T <;> simp [Set.indicator, h, hf]

/-- The actual logarithmic source weight equals physical cusp-height decay
after the constructed full half-line isometry. -/
theorem cuspHalfLineSourceEmbedding_weight (α : ℝ) (hα : 0 ≤ α)
    (f : cuspHalfLineSourceHilbert) :
    cuspHalfLineSourceEmbedding (cuspHalfLineWeight α hα f) =
      cuspWeightedInput α hα (cuspHalfLineSourceEmbedding f) := by
  have hlog := cuspHalfLine_ae_log_modular (cuspHalfLineWeight_ae α hα f)
  apply Lp.ext
  filter_upwards [cuspHalfLineSourceEmbedding_ae (cuspHalfLineWeight α hα f),
    cuspWeightedInput_ae α hα (cuspHalfLineSourceEmbedding f),
    cuspHalfLineSourceEmbedding_ae f, hlog] with τ hl hw hf hlog
  rw [hl, hw, hf]
  by_cases hy : 1 < τ.im
  · rw [ite_eq_left hy, hlog hy]
    have hp : τ.im ^ (-α) = Real.exp (-α * Real.log τ.im) := by
      rw [Real.rpow_def_of_pos τ.im_pos]
      congr 1
      ring
    rw [hp]
    simp only [ite_eq_left hy, Complex.real_smul]
    ring
  · simp [hy]

/-- The exact operator intertwining, with the actual Hilbert maps on both sides. -/
theorem cuspHalfLineSourceEmbedding_comp_weight (α : ℝ) (hα : 0 ≤ α) :
    cuspHalfLineSourceEmbedding.toContinuousLinearMap.comp (cuspHalfLineWeight α hα) =
      (cuspWeightedInput α hα).comp cuspHalfLineSourceEmbedding.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro f
  exact cuspHalfLineSourceEmbedding_weight α hα f

/-- Taking adjoints gives the literal global scalar-coefficient weighting law. -/
theorem cuspHalfLineSourceCoefficient_weightedInput (α : ℝ) (hα : 0 ≤ α)
    (F : ModularHilbert) :
    cuspHalfLineSourceCoefficient (cuspWeightedInput α hα F) =
      cuspHalfLineWeight α hα (cuspHalfLineSourceCoefficient F) := by
  apply ext_inner_left ℂ
  intro f
  rw [cuspHalfLineSourceCoefficient_inner_right,
    ← cuspWeightedInput_inner, ← cuspHalfLineSourceEmbedding_weight,
    ← cuspHalfLineSourceCoefficient_inner_right, cuspHalfLineWeight_inner]

theorem cuspHalfLineSourceCoefficient_comp_weightedInput (α : ℝ) (hα : 0 ≤ α) :
    cuspHalfLineSourceCoefficient.comp (cuspWeightedInput α hα) =
      (cuspHalfLineWeight α hα).comp cuspHalfLineSourceCoefficient := by
  apply ContinuousLinearMap.ext
  intro F
  exact cuspHalfLineSourceCoefficient_weightedInput α hα F

end GapFamily.Analytic
