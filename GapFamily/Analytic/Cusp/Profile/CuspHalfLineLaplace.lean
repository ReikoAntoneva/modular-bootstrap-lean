import GapFamily.Analytic.Foundation.PositiveBCFPower
import GapFamily.Analytic.Cusp.Profile.CuspHalfLineLaplaceNorm
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

noncomputable section
namespace GapFamily.Analytic.CuspHalfLineLaplace

open Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction

abbrev HalfLineL2 := Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))

private theorem bcfMul_memLp (f : HalfLineL2) (g : ℝ →ᵇ ℂ) :
    MemLp (fun t => g t * f t) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  apply (Lp.memLp f).of_le_mul (c := ‖g‖)
    (g.continuous.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
  exact Eventually.of_forall fun t => by
    change ‖g t * f t‖ ≤ ‖g‖ * ‖f t‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (g.norm_coe_le_norm t) (norm_nonneg _)

private def bcfMulValue (f : HalfLineL2) (g : ℝ →ᵇ ℂ) : HalfLineL2 :=
  (bcfMul_memLp f g).toLp _

private theorem bcfMulValue_ae (f : HalfLineL2) (g : ℝ →ᵇ ℂ) :
    bcfMulValue f g =ᵐ[volume.restrict (Ioi (0 : ℝ))] (fun t => g t * f t) :=
  MemLp.coeFn_toLp _

/-- Multiplying a fixed actual half-line L² vector by a bounded continuous amplitude. -/
def bcfMulL2 (f : HalfLineL2) : (ℝ →ᵇ ℂ) →L[ℂ] HalfLineL2 :=
  LinearMap.mkContinuous
    { toFun := bcfMulValue f
      map_add' := by
        intro g h
        apply Lp.ext
        filter_upwards [bcfMulValue_ae f (g + h), bcfMulValue_ae f g,
          bcfMulValue_ae f h, Lp.coeFn_add (bcfMulValue f g) (bcfMulValue f h)]
          with t hsum hg hh hout
        simp only [Pi.add_apply] at hout
        rw [hsum, hout, hg, hh]
        change (g t + h t) * f t = _
        exact add_mul _ _ _
      map_smul' := by
        intro c g
        apply Lp.ext
        filter_upwards [bcfMulValue_ae f (c • g), bcfMulValue_ae f g,
          Lp.coeFn_smul c (bcfMulValue f g)] with t hcg hg hout
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply] at hout ⊢
        rw [hcg, hout, hg]
        change (c * g t) * f t = c * (g t * f t)
        exact mul_assoc _ _ _ }
    ‖f‖ (fun g => by
      change ‖bcfMulValue f g‖ ≤ ‖f‖ * ‖g‖
      rw [mul_comm]
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [bcfMulValue_ae f g] with t ht
      rw [ht, norm_mul]
      exact mul_le_mul_of_nonneg_right (g.norm_coe_le_norm t) (norm_nonneg _))

theorem bcfMulL2_ae (f : HalfLineL2) (g : ℝ →ᵇ ℂ) :
    bcfMulL2 f g =ᵐ[volume.restrict (Ioi (0 : ℝ))] (fun t => g t * f t) :=
  bcfMulValue_ae f g

/-- The genuine exponential vector, totalized by zero off its L² parameter domain. -/
def exponential (β : ℂ) : HalfLineL2 :=
  if hβ : 0 < β.re then (cuspHalfLineLaplace_exp_memLp hβ).toLp _ else 0

theorem exponential_ae {β : ℂ} (hβ : 0 < β.re) :
    exponential β =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun t : ℝ => Complex.exp (-β * (t : ℂ))) := by
  simp only [exponential, dite_eq_left hβ]
  exact MemLp.coeFn_toLp _

theorem exponential_norm_sq {β : ℂ} (hβ : 0 < β.re) :
    ‖exponential β‖ ^ 2 = (2 * β.re)⁻¹ := by
  have hn : ‖exponential β‖ ^ 2 =
      ∫ t, ‖exponential β t‖ ^ 2 ∂volume.restrict (Ioi (0 : ℝ)) := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
  rw [hn]
  refine (integral_congr_ae ?_).trans (cuspHalfLineLaplace_exp_norm_sq_integral hβ)
  filter_upwards [exponential_ae hβ] with t ht
  rw [ht]

private def positiveBase (t : ℝ) : ℝ := Real.exp (-max t 0)

private theorem positiveBase_continuous : Continuous positiveBase := by
  unfold positiveBase
  fun_prop

private theorem positiveBase_pos (t : ℝ) : 0 < positiveBase t := Real.exp_pos _

private theorem positiveBase_le_one (t : ℝ) : positiveBase t ≤ 1 :=
  Real.exp_le_one_iff.mpr (neg_nonpos.mpr (le_max_right _ _))

private def power (β : ℂ) : ℝ →ᵇ ℂ :=
  PositiveBCFPower.positivePower positiveBase positiveBase_continuous
    positiveBase_pos 1 positiveBase_le_one β

private theorem power_analyticAt {β : ℂ} (hβ : 0 < β.re) : AnalyticAt ℂ power β :=
  PositiveBCFPower.positivePower_analyticAt positiveBase positiveBase_continuous
    positiveBase_pos 1 positiveBase_le_one hβ

private theorem power_mul_exp (a : ℝ) {β : ℂ} (hβ : a < β.re) {t : ℝ} (ht : 0 < t) :
    power (β - (a : ℂ)) t * Complex.exp (-(a : ℂ) * (t : ℂ)) =
      Complex.exp (-β * (t : ℂ)) := by
  have hs : 0 < (β - (a : ℂ)).re := by simpa using sub_pos.mpr hβ
  rw [power, PositiveBCFPower.positivePower_apply _ _ _ _ _ hs,
    positiveBase, max_eq_left ht.le,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)),
    ← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp, Complex.ofReal_neg,
    ← Complex.exp_add]
  congr 1
  ring

private theorem exponential_eq_bcfMul {a : ℝ} (ha : 0 < a) {β : ℂ} (hβ : a < β.re) :
    exponential β = bcfMulL2 (exponential (a : ℂ)) (power (β - (a : ℂ))) := by
  apply Lp.ext
  filter_upwards [exponential_ae (ha.trans hβ),
    bcfMulL2_ae (exponential (a : ℂ)) (power (β - (a : ℂ))),
    exponential_ae (by simpa using ha : 0 < (a : ℂ).re),
    ae_restrict_mem measurableSet_Ioi] with t hβt hm hat ht
  rw [hβt, hm, hat]
  exact (power_mul_exp a hβ ht).symm

/-- Norm holomorphy of the actual half-line L² exponential on its right half-plane. -/
theorem exponential_analyticAt {β : ℂ} (hβ : 0 < β.re) :
    AnalyticAt ℂ exponential β := by
  let a : ℝ := β.re / 2
  have ha : 0 < a := half_pos hβ
  have haβ : a < β.re := half_lt_self hβ
  have hs : 0 < (β - (a : ℂ)).re := by simpa using sub_pos.mpr haβ
  have hp : AnalyticAt ℂ (fun γ : ℂ => power (γ - (a : ℂ))) β :=
    (power_analyticAt hs).comp_of_eq (analyticAt_id.sub analyticAt_const) rfl
  have hm : AnalyticAt ℂ
      (fun γ => bcfMulL2 (exponential (a : ℂ)) (power (γ - (a : ℂ)))) β :=
    ((bcfMulL2 (exponential (a : ℂ))).analyticAt _).comp hp
  apply hm.congr
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds haβ]
    with γ hγ
  exact (exponential_eq_bcfMul ha hγ).symm

theorem exponential_analyticOnNhd :
    AnalyticOnNhd ℂ exponential {β : ℂ | 0 < β.re} :=
  fun _ hβ => exponential_analyticAt hβ

/-- The ordinary complex-bilinear Laplace functional on the actual half-line L² space. -/
def laplace (β : ℂ) : HalfLineL2 →L[ℂ] ℂ :=
  (ContinuousLinearMap.mul ℂ ℂ).lpPairing (volume.restrict (Ioi (0 : ℝ))) 2 2 (exponential β)

theorem laplace_integrable {β : ℂ} (hβ : 0 < β.re) (f : HalfLineL2) :
    IntegrableOn (fun t : ℝ => Complex.exp (-β * (t : ℂ)) * f t) (Ioi 0) :=
  (cuspHalfLineLaplace_exp_memLp hβ).integrable_mul (Lp.memLp f)

theorem laplace_apply {β : ℂ} (hβ : 0 < β.re) (f : HalfLineL2) :
    laplace β f = ∫ t : ℝ in Ioi 0, Complex.exp (-β * (t : ℂ)) * f t := by
  rw [laplace, ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [exponential_ae hβ] with t ht
  change exponential β t * f t = _
  rw [ht]

theorem laplace_analyticAt {β : ℂ} (hβ : 0 < β.re) : AnalyticAt ℂ laplace β :=
  (((ContinuousLinearMap.mul ℂ ℂ).lpPairing (volume.restrict (Ioi (0 : ℝ))) 2 2).analyticAt _).comp
    (exponential_analyticAt hβ)

end GapFamily.Analytic.CuspHalfLineLaplace
