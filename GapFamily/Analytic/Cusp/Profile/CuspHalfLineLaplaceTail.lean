import GapFamily.Analytic.Cusp.Profile.CuspHalfLineLaplace
import GapFamily.Analytic.Cusp.Profile.CuspHalfLineLaplacePairingBound

noncomputable section
namespace GapFamily.Analytic.CuspHalfLineLaplaceTail

open Set Filter MeasureTheory CuspHalfLineLaplace
open scoped Topology

private def tailCutValue (T : ℝ) (f : HalfLineL2) : HalfLineL2 :=
  ((Lp.memLp f).indicator measurableSet_Ioi).toLp ((Ioi T).indicator f)

private theorem tailCutValue_ae (T : ℝ) (f : HalfLineL2) :
    tailCutValue T f =ᵐ[volume.restrict (Ioi (0 : ℝ))] (Ioi T).indicator f :=
  MemLp.coeFn_toLp _

/-- Literal tail restriction within the genuine half-line Hilbert space. -/
def tailCut (T : ℝ) : HalfLineL2 →L[ℂ] HalfLineL2 :=
  LinearMap.mkContinuous
    { toFun := tailCutValue T
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [tailCutValue_ae T (f + g), tailCutValue_ae T f,
          tailCutValue_ae T g, Lp.coeFn_add f g,
          Lp.coeFn_add (tailCutValue T f) (tailCutValue T g)]
          with t hsum hf hg hin hout
        simp only [Pi.add_apply] at hin hout
        rw [hsum, hout, hf, hg]
        by_cases ht : t ∈ Ioi T
        · simp only [Set.indicator_of_mem ht]
          exact hin
        · simp only [Set.indicator_of_notMem ht, add_zero]
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [tailCutValue_ae T (c • f), tailCutValue_ae T f,
          Lp.coeFn_smul c f, Lp.coeFn_smul c (tailCutValue T f)]
          with t hcf hf hin hout
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply] at hin hout ⊢
        rw [hcf, hout, hf]
        by_cases ht : t ∈ Ioi T
        · simp only [Set.indicator_of_mem ht]
          exact hin
        · simp only [Set.indicator_of_notMem ht, mul_zero] }
    1 (fun f => by
      change ‖tailCutValue T f‖ ≤ 1 * ‖f‖
      rw [one_mul]
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [tailCutValue_ae T f] with t ht
      rw [ht]
      by_cases h : t ∈ Ioi T <;> simp [h])

theorem tailCut_ae (T : ℝ) (f : HalfLineL2) :
    tailCut T f =ᵐ[volume.restrict (Ioi (0 : ℝ))] (Ioi T).indicator f :=
  tailCutValue_ae T f

def tailExponential (T : ℝ) (β : ℂ) : HalfLineL2 := tailCut T (exponential β)

theorem tailExponential_ae (T : ℝ) {β : ℂ} (hβ : 0 < β.re) :
    tailExponential T β =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (Ioi T).indicator (fun t : ℝ => Complex.exp (-β * (t : ℂ))) := by
  filter_upwards [tailCut_ae T (exponential β), exponential_ae hβ] with t ht he
  change tailCut T (exponential β) t = _
  rw [ht]
  by_cases h : t ∈ Ioi T <;> simp [h, he]

private theorem integral_tail_indicator {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (g : ℝ → E) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t, (Ioi T).indicator g t ∂volume.restrict (Ioi (0 : ℝ))) =
      ∫ t in Ioi T, g t := by
  rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    inter_eq_left.mpr (Ioi_subset_Ioi hT)]

theorem tailExponential_norm_sq {T : ℝ} (hT : 0 ≤ T) {β : ℂ} (hβ : 0 < β.re) :
    ‖tailExponential T β‖ ^ 2 = Real.exp ((-2 * β.re) * T) / (2 * β.re) := by
  have hn : ‖tailExponential T β‖ ^ 2 =
      ∫ t, ‖tailExponential T β t‖ ^ 2 ∂volume.restrict (Ioi (0 : ℝ)) := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
  rw [hn]
  calc
    _ = ∫ t, (Ioi T).indicator
        (fun t : ℝ => ‖Complex.exp (-β * (t : ℂ))‖ ^ 2) t
        ∂volume.restrict (Ioi (0 : ℝ)) := by
      apply integral_congr_ae
      filter_upwards [tailExponential_ae T hβ] with t ht
      rw [ht]
      by_cases h : t ∈ Ioi T <;> simp [h]
    _ = ∫ t in Ioi T, ‖Complex.exp (-β * (t : ℂ))‖ ^ 2 :=
      integral_tail_indicator _ hT
    _ = _ := by
      simp_rw [cuspHalfLineLaplace_exp_norm_sq]
      rw [integral_exp_mul_Ioi (a := -2 * β.re) (by linarith) T]
      simp [neg_mul, div_eq_mul_inv]

theorem tailExponential_norm {T : ℝ} (hT : 0 ≤ T) {β : ℂ} (hβ : 0 < β.re) :
    ‖tailExponential T β‖ = Real.exp (-β.re * T) / Real.sqrt (2 * β.re) := by
  apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [tailExponential_norm_sq hT hβ, div_pow,
    Real.sq_sqrt (by positivity), ← Real.exp_nat_mul]
  congr 2
  ring

theorem tailExponential_analyticAt (T : ℝ) {β : ℂ} (hβ : 0 < β.re) :
    AnalyticAt ℂ (tailExponential T) β :=
  ((tailCut T).analyticAt _).comp (exponential_analyticAt hβ)

/-- The actual ordinary Laplace functional restricted to source heights above T. -/
def tailLaplace (T : ℝ) (β : ℂ) : HalfLineL2 →L[ℂ] ℂ :=
  (ContinuousLinearMap.mul ℂ ℂ).lpPairing (volume.restrict (Ioi (0 : ℝ))) 2 2
    (tailExponential T β)

theorem tailLaplace_integrable {T : ℝ} (hT : 0 ≤ T) {β : ℂ} (hβ : 0 < β.re)
    (f : HalfLineL2) :
    IntegrableOn (fun t : ℝ => Complex.exp (-β * (t : ℂ)) * f t) (Ioi T) :=
  (laplace_integrable hβ f).mono_set (Ioi_subset_Ioi hT)

theorem tailLaplace_apply {T : ℝ} (hT : 0 ≤ T) {β : ℂ} (hβ : 0 < β.re)
    (f : HalfLineL2) :
    tailLaplace T β f = ∫ t : ℝ in Ioi T, Complex.exp (-β * (t : ℂ)) * f t := by
  rw [tailLaplace, ContinuousLinearMap.lpPairing_eq_integral]
  refine (integral_congr_ae ?_).trans (integral_tail_indicator _ hT)
  filter_upwards [tailExponential_ae T hβ] with t ht
  change tailExponential T β t * f t = _
  rw [ht]
  by_cases h : t ∈ Ioi T <;> simp [h]

theorem tailLaplace_analyticAt (T : ℝ) {β : ℂ} (hβ : 0 < β.re) :
    AnalyticAt ℂ (tailLaplace T) β :=
  (((ContinuousLinearMap.mul ℂ ℂ).lpPairing (volume.restrict (Ioi (0 : ℝ))) 2 2).analyticAt _).comp
    (tailExponential_analyticAt T hβ)

theorem tailLaplace_norm_le {T : ℝ} (hT : 0 ≤ T) {β : ℂ} (hβ : 0 < β.re) :
    ‖tailLaplace T β‖ ≤ Real.exp (-β.re * T) / Real.sqrt (2 * β.re) := by
  exact (cuspHalfLineLaplace_lpPairing_norm_le (tailExponential T β)).trans_eq
    (tailExponential_norm hT hβ)

/-- A fixed right-half-plane disk has one explicit exponential source-tail bound. -/
theorem tailLaplace_norm_le_uniform {α T : ℝ} (hα : 0 < α) (hT : 0 ≤ T)
    {κ : ℂ} (hκ : ‖κ‖ ≤ α / 2) :
    ‖tailLaplace T ((α : ℂ) + κ)‖ ≤
      Real.exp (-(α / 2) * T) / Real.sqrt α := by
  have hre : α / 2 ≤ ((α : ℂ) + κ).re := by
    simp only [Complex.add_re, Complex.ofReal_re]
    have h := Complex.abs_re_le_norm κ
    have hn := neg_abs_le κ.re
    linarith
  have hβ : 0 < ((α : ℂ) + κ).re := (half_pos hα).trans_le hre
  have hd : Real.sqrt α ≤ Real.sqrt (2 * ((α : ℂ) + κ).re) :=
    Real.sqrt_le_sqrt (by linarith)
  have he : -((α : ℂ) + κ).re * T ≤ -(α / 2) * T :=
    mul_le_mul_of_nonneg_right (neg_le_neg hre) hT
  calc
    ‖tailLaplace T ((α : ℂ) + κ)‖ ≤
        Real.exp (-((α : ℂ) + κ).re * T) / Real.sqrt (2 * ((α : ℂ) + κ).re) :=
      tailLaplace_norm_le hT hβ
    _ ≤ Real.exp (-((α : ℂ) + κ).re * T) / Real.sqrt α :=
      div_le_div_of_nonneg_left (Real.exp_pos _).le (Real.sqrt_pos.mpr hα) hd
    _ ≤ _ := (div_le_div_iff_of_pos_right (Real.sqrt_pos.mpr hα)).mpr
      (Real.exp_le_exp.mpr he)

end GapFamily.Analytic.CuspHalfLineLaplaceTail
