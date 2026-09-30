import GapFamily.Analytic.Cusp.Scalar.CuspConstantCollarAnalytic
import GapFamily.Analytic.Cusp.Green.CuspGreenCoefficient
import GapFamily.Analytic.Cusp.Green.CuspGreenOperatorLinear

/-! A genuine operator-norm analytic scalar functional from the local constant response. -/
noncomputable section
namespace GapFamily.Analytic
open Filter Set MeasureTheory
open scoped Topology

/-- The compact kernel uses a one-point observation space and the actual source collar. -/
def cuspConstantFunctionalProjection (T : ℝ) :
    C(Unit × CuspGreenCollar 0 T, CuspGreenCollar 0 T) :=
  ⟨Prod.snd, continuous_snd⟩

/-- Ordinary kernel integration, evaluation, and actual coefficient extraction are
one bounded complex-linear map from uniform collar profiles to scalar functionals. -/
def cuspConstantFunctionalMap (T : ℝ) :
    C(CuspGreenCollar 0 T, ℂ) →L[ℂ] (ModularHilbert →L[ℂ] ℂ) :=
  ((ContinuousLinearMap.compL ℂ ModularHilbert
      (Lp ℂ 2 (cuspGreenCollarMeasure 0 T)) ℂ).flip (cuspGreenSourceCoefficient T)).comp
    (((ContinuousLinearMap.compL ℂ (Lp ℂ 2 (cuspGreenCollarMeasure 0 T)) C(Unit, ℂ) ℂ
        (ContinuousMap.evalCLM ℂ ())).comp
      (compactKernelOperatorMap (cuspGreenCollarMeasure 0 T))).comp
        (ContinuousMap.compCLM ℂ ℂ (cuspConstantFunctionalProjection T)))

/-- The actual locally continued constant-pairing functional on modular L² sources. -/
def cuspConstantPairingFunctional (T : ℝ) (κ : ℂ) : ModularHilbert →L[ℂ] ℂ :=
  cuspConstantFunctionalMap T (cuspConstantCollarResponse T κ)

/-- Each displayed ordinary integral is genuinely integrable. -/
theorem cuspConstantPairingFunctional_integrable (T : ℝ) (κ : ℂ) (F : ModularHilbert) :
    Integrable (fun t : CuspGreenCollar 0 T =>
      cuspConstantLogResponse κ t * cuspGreenSourceCoefficient T F t)
      (cuspGreenCollarMeasure 0 T) := by
  simpa only [ContinuousMap.comp_apply, cuspConstantFunctionalProjection,
    ContinuousMap.coe_mk, cuspConstantCollarResponse_apply] using
    compactKernelIntegral_integrable (cuspGreenCollarMeasure 0 T)
      ((cuspConstantCollarResponse T κ).comp (cuspConstantFunctionalProjection T))
      (cuspGreenSourceCoefficient T F) ()

/-- Evaluation is exactly the ordinary nonconjugated collar integral, so its parameter
is holomorphic rather than antiholomorphic. -/
theorem cuspConstantPairingFunctional_apply (T : ℝ) (κ : ℂ) (F : ModularHilbert) :
    cuspConstantPairingFunctional T κ F =
      ∫ t : CuspGreenCollar 0 T,
        cuspConstantLogResponse κ t * cuspGreenSourceCoefficient T F t
          ∂cuspGreenCollarMeasure 0 T := by
  change compactKernelIntegralOperator (cuspGreenCollarMeasure 0 T)
      ((cuspConstantCollarResponse T κ).comp (cuspConstantFunctionalProjection T))
      (cuspGreenSourceCoefficient T F) () = _
  rw [compactKernelIntegralOperator_apply]
  simp only [ContinuousMap.comp_apply, cuspConstantFunctionalProjection,
    ContinuousMap.coe_mk, cuspConstantCollarResponse_apply]

/-- Parameter analyticity is in the actual operator norm on bounded scalar functionals. -/
theorem cuspConstantPairingFunctional_analyticAt (T : ℝ) {κ : ℂ}
    (hκ : κ ≠ -(1 / 2 : ℂ)) :
    AnalyticAt ℂ (cuspConstantPairingFunctional T) κ :=
  (ContinuousLinearMap.analyticAt (𝕜 := ℂ)
    (E := C(CuspGreenCollar 0 T, ℂ)) (F := ModularHilbert →L[ℂ] ℂ)
    (cuspConstantFunctionalMap T) _).comp_of_eq
      (cuspConstantCollarResponse_analyticAt T hκ) rfl

/-- The threshold scalar functional is analytic without constructing any threshold W vector. -/
theorem cuspConstantPairingFunctional_analyticAt_zero (T : ℝ) :
    AnalyticAt ℂ (cuspConstantPairingFunctional T) 0 :=
  cuspConstantPairingFunctional_analyticAt T (by norm_num)

/-- Actual operator-norm convergence of the scalar functional at threshold. -/
theorem cuspConstantPairingFunctional_tendsto_zero (T : ℝ) :
    Tendsto (cuspConstantPairingFunctional T) (𝓝 (0 : ℂ))
      (𝓝 (cuspConstantPairingFunctional T 0)) :=
  (cuspConstantPairingFunctional_analyticAt_zero T).continuousAt.tendsto

/-- A finite-collar bound follows from genuine Cauchy--Schwarz kernel integration. -/
theorem cuspConstantPairingFunctional_norm_le {T : ℝ} (hT : 0 ≤ T) (κ : ℂ) :
    ‖cuspConstantPairingFunctional T κ‖ ≤ Real.sqrt T * ‖cuspConstantCollarResponse T κ‖ := by
  let k : C(Unit × CuspGreenCollar 0 T, ℂ) :=
    (cuspConstantCollarResponse T κ).comp (cuspConstantFunctionalProjection T)
  have hk : ‖k‖ ≤ ‖cuspConstantCollarResponse T κ‖ := by
    apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
    intro p
    exact (cuspConstantCollarResponse T κ).norm_coe_le_norm p.2
  have hop : ‖compactKernelIntegralOperator (cuspGreenCollarMeasure 0 T) k‖ ≤
      Real.sqrt T * ‖cuspConstantCollarResponse T κ‖ := by
    apply (norm_compactKernelIntegralOperator_le (cuspGreenCollarMeasure 0 T) k).trans
    rw [cuspGreenCollarMeasure_real_univ 0 T hT, sub_zero]
    exact mul_le_mul_of_nonneg_left hk (Real.sqrt_nonneg _)
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro F
  change ‖compactKernelIntegralOperator (cuspGreenCollarMeasure 0 T) k
    (cuspGreenSourceCoefficient T F) ()‖ ≤ _
  calc
    _ ≤ ‖compactKernelIntegralOperator (cuspGreenCollarMeasure 0 T) k
        (cuspGreenSourceCoefficient T F)‖ := ContinuousMap.norm_coe_le_norm _ ()
    _ ≤ ‖compactKernelIntegralOperator (cuspGreenCollarMeasure 0 T) k‖ *
        ‖cuspGreenSourceCoefficient T F‖ :=
      (compactKernelIntegralOperator (cuspGreenCollarMeasure 0 T) k).le_opNorm _
    _ ≤ (Real.sqrt T * ‖cuspConstantCollarResponse T κ‖) * ‖F‖ :=
      mul_le_mul hop (cuspGreenSourceCoefficient_norm_le T F) (norm_nonneg _) (by positivity)

/-- An explicit uniform operator bound on a whole parameter neighborhood of threshold. -/
theorem cuspConstantPairingFunctional_norm_le_on_quarter {T : ℝ} (hT : 0 ≤ T)
    {κ : ℂ} (hκ : ‖κ‖ ≤ (1 / 4 : ℝ)) :
    ‖cuspConstantPairingFunctional T κ‖ ≤
      Real.sqrt T * ((16 / 3 : ℝ) * (Real.exp (T / 4) + 1)) :=
  (cuspConstantPairingFunctional_norm_le hT κ).trans
    (mul_le_mul_of_nonneg_left (cuspConstantCollarResponse_norm_le_on_quarter T hκ)
      (Real.sqrt_nonneg _))

/-- The threshold functional is the actual finite integral with the explicit local column. -/
theorem cuspConstantPairingFunctional_zero_apply (T : ℝ) (F : ModularHilbert) :
    cuspConstantPairingFunctional T 0 F =
      ∫ t : CuspGreenCollar 0 T,
        (4 * (1 - Complex.exp (-(t : ℂ) / 2))) * cuspGreenSourceCoefficient T F t
          ∂cuspGreenCollarMeasure 0 T := by
  rw [cuspConstantPairingFunctional_apply]
  apply integral_congr_ae
  filter_upwards with t
  have h := cuspConstantCollarResponse_zero_apply T t
  rw [cuspConstantCollarResponse_apply] at h
  rw [h]

end GapFamily.Analytic
