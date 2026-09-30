import GapFamily.Analytic.Cusp.Scalar.CuspConstantResponseAnalytic
import GapFamily.Analytic.Cusp.Green.CuspGreenOperatorKernel
import GapFamily.Analytic.Cusp.Green.CuspGreenOperatorBasic
import GapFamily.Analytic.Cusp.Scalar.CuspConstantResponseBasic

noncomputable section
namespace GapFamily.Analytic

private theorem outgoing_exp_norm_quarter {κ : ℂ} (hκ : ‖κ‖ ≤ (1 / 4 : ℝ))
    {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    ‖Complex.exp (-κ * (t : ℂ))‖ ≤ Real.exp (T / 4) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  calc
    (-κ * (t : ℂ)).re ≤ ‖-κ * (t : ℂ)‖ := Complex.re_le_norm _
    _ = ‖κ‖ * t := by
      rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]
    _ ≤ (1 / 4 : ℝ) * t := mul_le_mul_of_nonneg_right hκ ht
    _ ≤ T / 4 := by linarith

private theorem half_exp_norm_le_one {t : ℝ} (ht : 0 ≤ t) :
    ‖Complex.exp (-(t : ℂ) / 2)‖ ≤ 1 := by
  rw [Complex.norm_exp]
  apply Real.exp_le_one_iff.mpr
  simp
  linarith

private theorem parameter_ne_half {κ : ℂ} (hκ : ‖κ‖ ≤ (1 / 4 : ℝ)) :
    κ ≠ (1 / 2 : ℂ) := by
  intro h
  subst κ
  norm_num at hκ

private theorem parameter_ne_neg_half {κ : ℂ} (hκ : ‖κ‖ ≤ (1 / 4 : ℝ)) :
    κ ≠ -(1 / 2 : ℂ) := by
  intro h
  subst κ
  norm_num at hκ

theorem cuspConstant_denominator_norm_lower_quarter {κ : ℂ} (hκ : ‖κ‖ ≤ (1 / 4 : ℝ)) :
    (3 / 16 : ℝ) ≤ ‖(1 / 4 : ℂ) - κ^2‖ := by
  have hsq : ‖κ‖^2 ≤ (1 / 4 : ℝ)^2 := pow_le_pow_left₀ (norm_nonneg κ) hκ 2
  calc
    (3 / 16 : ℝ) ≤ ‖(1 / 4 : ℂ)‖ - ‖κ^2‖ := by
      norm_num only [norm_div, norm_one, Complex.norm_ofNat, norm_pow]
      linarith
    _ ≤ ‖(1 / 4 : ℂ) - κ^2‖ := norm_sub_norm_le _ _

/-- An explicit bound for the actual response, uniform on a bounded position
collar and the closed parameter disk of radius one quarter. -/
theorem cuspConstantLogResponse_norm_le_on_quarter (T : ℝ) {κ : ℂ}
    (hκ : ‖κ‖ ≤ (1 / 4 : ℝ)) {t : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    ‖cuspConstantLogResponse κ t‖ ≤ (16 / 3 : ℝ) * (Real.exp (T / 4) + 1) := by
  rw [cuspConstantLogResponse_eq_quotient
    (parameter_ne_half hκ) (parameter_ne_neg_half hκ), norm_div]
  have hnum : ‖Complex.exp (-κ * (t : ℂ)) - Complex.exp (-(t : ℂ) / 2)‖ ≤
      Real.exp (T / 4) + 1 :=
    (norm_sub_le _ _).trans (add_le_add
      (outgoing_exp_norm_quarter hκ ht htT) (half_exp_norm_le_one ht))
  calc
    _ ≤ (Real.exp (T / 4) + 1) / ‖(1 / 4 : ℂ) - κ ^ 2‖ :=
      div_le_div_of_nonneg_right hnum (norm_nonneg _)
    _ ≤ (Real.exp (T / 4) + 1) / (3 / 16 : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num)
        (cuspConstant_denominator_norm_lower_quarter hκ)
    _ = _ := by ring


end GapFamily.Analytic


/-! Actual finite-collar constant response with uniform-norm analytic parameter dependence. -/
noncomputable section
namespace GapFamily.Analytic
open Filter Set
open scoped Topology

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- The genuine exponential response as a continuous function on compact positions. -/
def cuspConstantContinuousExp (t : C(X, ℝ)) (κ : ℂ) : C(X, ℂ) :=
  NormedSpace.exp (κ • (⟨fun x => -(t x : ℂ), by fun_prop⟩ : C(X, ℂ)))

theorem cuspConstantContinuousExp_apply (t : C(X, ℝ)) (κ : ℂ) (x : X) :
    cuspConstantContinuousExp t κ x = Complex.exp (-κ * (t x : ℂ)) := by
  simp [cuspConstantContinuousExp, continuousKernel_exp_apply, mul_neg, neg_mul]

theorem differentiable_cuspConstantContinuousExp (t : C(X, ℝ)) :
    Differentiable ℂ (cuspConstantContinuousExp t) :=
  differentiable_exp_smul_const ℂ _

/-- The removable constant response as an actual element of the uniform spatial Banach space. -/
def cuspConstantContinuousResponse (t : C(X, ℝ)) (κ : ℂ) : C(X, ℂ) :=
  (-(κ + (1 / 2 : ℂ))⁻¹) • dslope (cuspConstantContinuousExp t) (1 / 2) κ

/-- This Banach-valued realization agrees pointwise with the existing actual scalar response. -/
theorem cuspConstantContinuousResponse_apply (t : C(X, ℝ)) (κ : ℂ) (x : X) :
    cuspConstantContinuousResponse t κ x = cuspConstantLogResponse κ (t x) := by
  have h := (ContinuousMap.evalCLM ℂ x).dslope_comp
    (cuspConstantContinuousExp t) (1 / 2) κ
    (fun _ => differentiable_cuspConstantContinuousExp t (1 / 2))
  have heq : ((ContinuousMap.evalCLM ℂ x) ∘ cuspConstantContinuousExp t) =
      (fun z : ℂ => Complex.exp (-z * (t x : ℂ))) := by
    funext z
    exact cuspConstantContinuousExp_apply t z x
  rw [heq] at h
  simp only [ContinuousMap.evalCLM_apply] at h
  change (-(κ + (1 / 2 : ℂ))⁻¹) * _ = cuspConstantLogResponse κ (t x)
  rw [← h, cuspConstantLogResponse]
  ring

/-- Analyticity holds in the spatial uniform norm, including both κ=0 and κ=1/2.
Only the actual opposite-root pole is excluded. -/
theorem cuspConstantContinuousResponse_analyticAt (t : C(X, ℝ)) {κ : ℂ}
    (hκ : κ ≠ -(1 / 2 : ℂ)) : AnalyticAt ℂ (cuspConstantContinuousResponse t) κ := by
  have hs : Differentiable ℂ (dslope (cuspConstantContinuousExp t) (1 / 2)) :=
    differentiableOn_univ.mp
      ((Complex.differentiableOn_dslope (s := univ) (c := (1 / 2 : ℂ)) univ_mem).mpr
        (differentiable_cuspConstantContinuousExp t).differentiableOn)
  have hc : AnalyticAt ℂ (fun z : ℂ => z + (1 / 2 : ℂ)) κ := by fun_prop
  exact (hc.inv (cuspConstant_add_half_ne_zero hκ)).neg.smul (hs.analyticAt κ)

/-- The finite logarithmic collar uses its literal coordinate, with no rescaling. -/
def cuspConstantCollarPosition (T : ℝ) : C(CuspGreenCollar 0 T, ℝ) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- Actual locally restricted logarithmic constant response on the closed observation collar. -/
def cuspConstantCollarResponse (T : ℝ) (κ : ℂ) : C(CuspGreenCollar 0 T, ℂ) :=
  cuspConstantContinuousResponse (cuspConstantCollarPosition T) κ

@[simp] theorem cuspConstantCollarResponse_apply (T : ℝ) (κ : ℂ)
    (t : CuspGreenCollar 0 T) :
    cuspConstantCollarResponse T κ t = cuspConstantLogResponse κ t :=
  cuspConstantContinuousResponse_apply _ _ _

theorem cuspConstantCollarResponse_analyticAt (T : ℝ) {κ : ℂ}
    (hκ : κ ≠ -(1 / 2 : ℂ)) : AnalyticAt ℂ (cuspConstantCollarResponse T) κ :=
  cuspConstantContinuousResponse_analyticAt _ hκ

/-- In particular, threshold continuation exists in the genuine compact uniform norm. -/
theorem cuspConstantCollarResponse_analyticAt_zero (T : ℝ) :
    AnalyticAt ℂ (cuspConstantCollarResponse T) 0 :=
  cuspConstantCollarResponse_analyticAt T (by norm_num)

/-- The actual uniform threshold value has its explicit finite-position formula. -/
theorem cuspConstantCollarResponse_zero_apply (T : ℝ) (t : CuspGreenCollar 0 T) :
    cuspConstantCollarResponse T 0 t =
      4 * (1 - Complex.exp (-(t : ℂ) / 2)) := by
  rw [cuspConstantCollarResponse_apply, cuspConstantLogResponse_eq_quotient
    (by norm_num : (0 : ℂ) ≠ (1 / 2 : ℂ)) (by norm_num : (0 : ℂ) ≠ -(1 / 2 : ℂ))]
  norm_num
  ring

/-- The removable physical parameter remains part of the same uniform analytic family. -/
theorem cuspConstantCollarResponse_half_apply (T : ℝ) (t : CuspGreenCollar 0 T) :
    cuspConstantCollarResponse T (1 / 2) t =
      (t : ℂ) * Complex.exp (-(t : ℂ) / 2) := by
  rw [cuspConstantCollarResponse_apply, cuspConstantLogResponse_half]

/-- Parameter convergence at threshold is convergence of actual continuous functions in norm. -/
theorem cuspConstantCollarResponse_tendsto_zero (T : ℝ) :
    Tendsto (cuspConstantCollarResponse T) (𝓝 (0 : ℂ))
      (𝓝 (cuspConstantCollarResponse T 0)) :=
  (cuspConstantCollarResponse_analyticAt_zero T).continuousAt.tendsto

/-- The κ=1/2 removable limit also holds in the compact uniform norm. -/
theorem cuspConstantCollarResponse_tendsto_half (T : ℝ) :
    Tendsto (cuspConstantCollarResponse T) (𝓝 (1 / 2 : ℂ))
      (𝓝 (cuspConstantCollarResponse T (1 / 2))) :=
  (cuspConstantCollarResponse_analyticAt T (by norm_num :
    (1 / 2 : ℂ) ≠ -(1 / 2 : ℂ))).continuousAt.tendsto

/-- The square-root factor for the genuine physical height y=exp(t). -/
def cuspConstantCollarWeight (T : ℝ) : C(CuspGreenCollar 0 T, ℂ) :=
  ⟨fun t => (Real.sqrt (Real.exp (t : ℝ)) : ℂ), by fun_prop⟩

/-- Actual physical response restricted to heights exp(t), t in the fixed logarithmic collar. -/
def cuspConstantPhysicalCollarResponse (T : ℝ) (κ : ℂ) : C(CuspGreenCollar 0 T, ℂ) :=
  cuspConstantCollarWeight T * cuspConstantCollarResponse T κ

@[simp] theorem cuspConstantPhysicalCollarResponse_apply (T : ℝ) (κ : ℂ)
    (t : CuspGreenCollar 0 T) :
    cuspConstantPhysicalCollarResponse T κ t =
      cuspConstantPhysicalResponse κ (Real.exp (t : ℝ)) := by
  simp only [cuspConstantPhysicalCollarResponse, ContinuousMap.mul_apply,
    cuspConstantCollarWeight, ContinuousMap.coe_mk, cuspConstantCollarResponse_apply,
    cuspConstantPhysicalResponse, cuspLift, Complex.real_smul, Real.log_exp]

theorem cuspConstantPhysicalCollarResponse_analyticAt (T : ℝ) {κ : ℂ}
    (hκ : κ ≠ -(1 / 2 : ℂ)) : AnalyticAt ℂ (cuspConstantPhysicalCollarResponse T) κ :=
  analyticAt_const.mul (cuspConstantCollarResponse_analyticAt T hκ)

theorem cuspConstantPhysicalCollarResponse_analyticAt_zero (T : ℝ) :
    AnalyticAt ℂ (cuspConstantPhysicalCollarResponse T) 0 :=
  cuspConstantPhysicalCollarResponse_analyticAt T (by norm_num)

/-- The actual physical threshold value is finite on every fixed collar. -/
theorem cuspConstantPhysicalCollarResponse_zero_apply (T : ℝ) (t : CuspGreenCollar 0 T) :
    cuspConstantPhysicalCollarResponse T 0 t =
      4 * ((Real.sqrt (Real.exp (t : ℝ)) : ℂ) - 1) := by
  change (Real.sqrt (Real.exp (t : ℝ)) : ℂ) * cuspConstantCollarResponse T 0 t = _
  rw [cuspConstantCollarResponse_zero_apply]
  have he : (Real.sqrt (Real.exp (t : ℝ)) : ℂ) * Complex.exp (-(t : ℂ) / 2) = 1 := by
    rw [← Real.exp_half, Complex.ofReal_exp, ← Complex.exp_add]
    convert Complex.exp_zero using 1
    congr 1
    push_cast
    ring
  calc
    _ = 4 * ((Real.sqrt (Real.exp (t : ℝ)) : ℂ) -
        (Real.sqrt (Real.exp (t : ℝ)) : ℂ) * Complex.exp (-(t : ℂ) / 2)) := by ring
    _ = _ := by rw [he]


/-- Exact physical removable value on the logarithmic observation collar. -/
theorem cuspConstantPhysicalCollarResponse_half_apply (T : ℝ) (t : CuspGreenCollar 0 T) :
    cuspConstantPhysicalCollarResponse T (1 / 2) t = (t : ℂ) := by
  rw [cuspConstantPhysicalCollarResponse_apply,
    cuspConstantPhysicalResponse_half (Real.exp_pos _), Real.log_exp]

/-- The physical threshold limit is also a genuine uniform-norm limit. -/
theorem cuspConstantPhysicalCollarResponse_tendsto_zero (T : ℝ) :
    Tendsto (cuspConstantPhysicalCollarResponse T) (𝓝 (0 : ℂ))
      (𝓝 (cuspConstantPhysicalCollarResponse T 0)) :=
  (cuspConstantPhysicalCollarResponse_analyticAt_zero T).continuousAt.tendsto

/-- An explicit bound on the entire compact logarithmic profile near threshold. -/
theorem cuspConstantCollarResponse_norm_le_on_quarter (T : ℝ) {κ : ℂ}
    (hκ : ‖κ‖ ≤ (1 / 4 : ℝ)) :
    ‖cuspConstantCollarResponse T κ‖ ≤ (16 / 3 : ℝ) * (Real.exp (T / 4) + 1) := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  rw [cuspConstantCollarResponse_apply]
  exact cuspConstantLogResponse_norm_le_on_quarter T hκ t.property.1 t.property.2

/-- The true physical profile has a matching explicit fixed-collar uniform bound. -/
theorem cuspConstantPhysicalCollarResponse_norm_le_on_quarter (T : ℝ) {κ : ℂ}
    (hκ : ‖κ‖ ≤ (1 / 4 : ℝ)) :
    ‖cuspConstantPhysicalCollarResponse T κ‖ ≤
      Real.exp (T / 2) * ((16 / 3 : ℝ) * (Real.exp (T / 4) + 1)) := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  change ‖(Real.sqrt (Real.exp (t : ℝ)) : ℂ) * cuspConstantCollarResponse T κ t‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), cuspConstantCollarResponse_apply]
  have hw : Real.sqrt (Real.exp (t : ℝ)) ≤ Real.exp (T / 2) := by
    rw [← Real.exp_half]
    exact Real.exp_le_exp.mpr (by linarith [t.property.2])
  exact mul_le_mul hw
    (cuspConstantLogResponse_norm_le_on_quarter T hκ t.property.1 t.property.2)
    (norm_nonneg _) (Real.exp_pos _).le

end GapFamily.Analytic

