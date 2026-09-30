import GapFamily.Analytic.Cusp.Scalar.CuspConstantLocalResponse
import GapFamily.Analytic.Cusp.Scalar.CuspConstantGradientProfile

/-!
# Actual finite-height continuation of the constant-response gradient

The shifted logarithmic derivative is embedded with the actual source isometry.
Physical identification restricts the already constructed closed gradient; it
makes no assertion about the derivative or form-domain membership of a sharp cutoff.
-/

noncomputable section
namespace GapFamily.Analytic
open Set Filter MeasureTheory ModularGradient
open scoped Topology

/-- The literal shifted derivative on the finite logarithmic collar. -/
def cuspConstantCollarGradient (T : ℝ) (κ : ℂ) : C(CuspGreenCollar 0 T, ℂ) :=
  (κ + (1 / 2 : ℂ))⁻¹ • cuspConstantContinuousExp (cuspConstantCollarPosition T) κ

@[simp] theorem cuspConstantCollarGradient_apply (T : ℝ) (κ : ℂ)
    (t : CuspGreenCollar 0 T) :
    cuspConstantCollarGradient T κ t = Complex.exp (-κ * (t : ℂ)) / (κ + 1 / 2) := by
  simp [cuspConstantCollarGradient, cuspConstantContinuousExp_apply,
    cuspConstantCollarPosition, div_eq_mul_inv, mul_comm]

/-- This collar profile is the actual shifted ordinary derivative. -/
theorem cuspConstantCollarGradient_eq_shiftedDeriv (T : ℝ) {κ : ℂ}
    (hκ : κ ≠ -(1 / 2 : ℂ)) (t : CuspGreenCollar 0 T) :
    cuspConstantCollarGradient T κ t =
      deriv (cuspConstantLogResponse κ) t + (1 / 2 : ℂ) * cuspConstantLogResponse κ t := by
  rw [cuspConstantCollarGradient_apply, deriv_cuspConstantLogResponse_add_half hκ]

theorem cuspConstantCollarGradient_analyticAt (T : ℝ) {κ : ℂ}
    (hκ : κ ≠ -(1 / 2 : ℂ)) : AnalyticAt ℂ (cuspConstantCollarGradient T) κ := by
  have hc : AnalyticAt ℂ (fun z : ℂ => z + (1 / 2 : ℂ)) κ := by fun_prop
  exact (hc.inv (cuspConstant_add_half_ne_zero hκ)).smul
    ((differentiable_cuspConstantContinuousExp (cuspConstantCollarPosition T)).analyticAt κ)

@[simp] theorem cuspConstantCollarGradient_zero_apply (T : ℝ)
    (t : CuspGreenCollar 0 T) : cuspConstantCollarGradient T 0 t = 2 := by
  rw [cuspConstantCollarGradient_apply]
  norm_num

/-- The actual modular L² vertical gradient output on a finite height interval. -/
def cuspConstantLocalVerticalGradient (T : ℝ) (κ : ℂ) : ModularHilbert :=
  cuspGreenSourceEmbedding T
    (ContinuousMap.toLp 2 (cuspGreenCollarMeasure 0 T) ℂ (cuspConstantCollarGradient T κ))

theorem cuspConstantLocalVerticalGradient_analyticAt (T : ℝ) {κ : ℂ}
    (hκ : κ ≠ -(1 / 2 : ℂ)) : AnalyticAt ℂ (cuspConstantLocalVerticalGradient T) κ := by
  let J : C(CuspGreenCollar 0 T, ℂ) →L[ℂ] ModularHilbert :=
    (cuspGreenSourceEmbedding T).toContinuousLinearMap.comp
      (ContinuousMap.toLp 2 (cuspGreenCollarMeasure 0 T) ℂ)
  exact (J.analyticAt _).comp_of_eq (cuspConstantCollarGradient_analyticAt T hκ) rfl

theorem cuspConstantLocalVerticalGradient_analyticAt_zero (T : ℝ) :
    AnalyticAt ℂ (cuspConstantLocalVerticalGradient T) 0 :=
  cuspConstantLocalVerticalGradient_analyticAt T (by norm_num)

/-- Its representative is the literal square-root lift of the shifted derivative. -/
theorem cuspConstantLocalVerticalGradient_ae {T : ℝ} (hT : 0 ≤ T) (κ : ℂ) :
    cuspConstantLocalVerticalGradient T κ =ᵐ[modularMeasure]
      (fun τ : UpperHalfPlane => if 1 < τ.im ∧ τ.im ≤ Real.exp T then
        Real.sqrt τ.im • (Complex.exp (-κ * (Real.log τ.im : ℂ)) / (κ + 1 / 2))
      else 0) := by
  have hc : Continuous (fun t : ℝ => Complex.exp (-κ * (t : ℂ)) / (κ + 1 / 2)) := by
    fun_prop
  have he : cuspConstantCollarGradient T κ =
      (⟨fun t : CuspGreenCollar 0 T => Complex.exp (-κ * (t : ℂ)) / (κ + 1 / 2),
        hc.comp continuous_subtype_val⟩ : C(CuspGreenCollar 0 T, ℂ)) := by
    ext t
    exact cuspConstantCollarGradient_apply T κ t
  unfold cuspConstantLocalVerticalGradient
  rw [he]
  exact cuspGreenSourceEmbedding_continuous_ae T hT _ hc

/-- On the physical half-plane this is the restriction of the actual closed vertical gradient. -/
theorem cuspConstantLocalVerticalGradient_eq_lowCut {T : ℝ} (hT : 0 ≤ T)
    {κ : ℂ} (hκ : 0 < κ.re) :
    cuspConstantLocalVerticalGradient T κ = modularLowCut (Real.exp T)
      (formGradient (cuspConstantForm hκ)).ofLp.2 := by
  apply Lp.ext
  filter_upwards [cuspConstantLocalVerticalGradient_ae hT κ,
    modularLowCut_ae (Real.exp T) (formGradient (cuspConstantForm hκ)).ofLp.2,
    cuspConstantForm_gradient_snd_exp_ae hκ] with τ hl hc hw
  rw [hl, hc]
  by_cases ht : τ.im ≤ Real.exp T
  · simp only [indicator_apply, mem_ofPred_eq, ht, ite_true, hw, and_true]
  · simp only [indicator_apply, mem_ofPred_eq, ht, ite_false, and_false]

/-- The same physical identity for the actual scalar pencil inverse on the modular constant. -/
theorem cuspConstantLocalVerticalGradient_eq_pencil_lowCut {T : ℝ} (hT : 0 ≤ T)
    {κ : ℂ} (hκ : 0 < κ.re) :
    cuspConstantLocalVerticalGradient T κ = modularLowCut (Real.exp T)
      (cuspScalarGradient
        (cuspScalarPencilSolution ((1 / 4 : ℂ) - κ ^ 2) modularConstant)).ofLp.2 := by
  rw [← cuspConstantScalarForm_eq_pencilSolution hκ]
  exact cuspConstantLocalVerticalGradient_eq_lowCut hT hκ

/-- Both components of the local gradient in the genuine Hilbert gradient space. -/
def cuspConstantLocalGradient (T : ℝ) (κ : ℂ) : GradientSpace :=
  WithLp.toLp 2 (0, cuspConstantLocalVerticalGradient T κ)

theorem cuspConstantLocalGradient_analyticAt (T : ℝ) {κ : ℂ}
    (hκ : κ ≠ -(1 / 2 : ℂ)) : AnalyticAt ℂ (cuspConstantLocalGradient T) κ := by
  let J := (WithLp.prodContinuousLinearEquiv 2 ℂ ModularHilbert ModularHilbert).symm
  exact (J.toContinuousLinearMap.analyticAt _).comp_of_eq
    (analyticAt_const.prod (cuspConstantLocalVerticalGradient_analyticAt T hκ)) rfl

theorem cuspConstantLocalGradient_analyticAt_zero (T : ℝ) :
    AnalyticAt ℂ (cuspConstantLocalGradient T) 0 :=
  cuspConstantLocalGradient_analyticAt T (by norm_num)

@[simp] theorem cuspConstantLocalGradient_fst (T : ℝ) (κ : ℂ) :
    (cuspConstantLocalGradient T κ).ofLp.1 = 0 := rfl

@[simp] theorem cuspConstantLocalGradient_snd (T : ℝ) (κ : ℂ) :
    (cuspConstantLocalGradient T κ).ofLp.2 = cuspConstantLocalVerticalGradient T κ := rfl

/-- Restriction is applied to the actual two gradient components, with horizontal component zero. -/
theorem cuspConstantLocalGradient_eq_lowCut {T : ℝ} (hT : 0 ≤ T)
    {κ : ℂ} (hκ : 0 < κ.re) :
    cuspConstantLocalGradient T κ = WithLp.toLp 2
      (modularLowCut (Real.exp T) (formGradient (cuspConstantForm hκ)).ofLp.1,
       modularLowCut (Real.exp T) (formGradient (cuspConstantForm hκ)).ofLp.2) := by
  rw [cuspConstantForm_gradient_fst_eq_zero hκ, map_zero,
    ← cuspConstantLocalVerticalGradient_eq_lowCut hT hκ]
  rfl

end GapFamily.Analytic
