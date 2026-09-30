import GapFamily.Analytic.Cusp.Scalar.CuspConstantHalfLinePairing
import GapFamily.Analytic.Cusp.Profile.CuspHalfLineLaplace

noncomputable section
namespace GapFamily.Analytic
open Set MeasureTheory CuspHalfLineLaplace

/-- The actual full half-line constant observation with an exponential source weight. -/
def cuspWeightedConstantPairingFunctional (α : ℝ) (κ : ℂ) :
    ModularHilbert →L[ℂ] ℂ :=
  (((1 / 4 : ℂ) - κ ^ 2)⁻¹) •
    ((laplace ((α : ℂ) + κ) - laplace ((α : ℂ) + 1 / 2)).comp
      cuspHalfLineSourceCoefficient)

theorem cuspWeightedConstantPairingFunctional_analyticAt_zero {α : ℝ} (hα : 0 < α) :
    AnalyticAt ℂ (cuspWeightedConstantPairingFunctional α) 0 := by
  have hβ : 0 < ((α : ℂ) + (0 : ℂ)).re := by simpa using hα
  have hLap : AnalyticAt ℂ
      (fun κ : ℂ => laplace ((α : ℂ) + κ) - laplace ((α : ℂ) + 1 / 2)) 0 :=
    ((laplace_analyticAt hβ).comp_of_eq (analyticAt_const.add analyticAt_id) rfl).sub
      analyticAt_const
  have hc : AnalyticAt ℂ (fun κ : ℂ =>
      (laplace ((α : ℂ) + κ) - laplace ((α : ℂ) + 1 / 2)).comp
        cuspHalfLineSourceCoefficient) 0 :=
    ((ContinuousLinearMap.compL ℂ ModularHilbert HalfLineL2 ℂ).analyticAt_bilinear _).comp
      (hLap.prod analyticAt_const)
  have hi : AnalyticAt ℂ (fun κ : ℂ => ((1 / 4 : ℂ) - κ ^ 2)⁻¹) 0 := by
    apply (analyticAt_const.sub (analyticAt_id.pow 2)).inv
    norm_num
  exact hi.smul hc

private theorem weightedConstantLogResponse_eq (α : ℝ) {κ : ℂ}
    (hp : κ ≠ (1 / 2 : ℂ)) (hm : κ ≠ -(1 / 2 : ℂ)) (t : ℝ) :
    cuspConstantLogResponse κ t * Complex.exp (-(α : ℂ) * t) =
      ((1 / 4 : ℂ) - κ ^ 2)⁻¹ *
        (Complex.exp (-((α : ℂ) + κ) * t) -
          Complex.exp (-((α : ℂ) + 1 / 2) * t)) := by
  rw [cuspConstantLogResponse_eq_quotient hp hm]
  have h₁ : Complex.exp (-κ * t) * Complex.exp (-(α : ℂ) * t) =
      Complex.exp (-((α : ℂ) + κ) * t) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have h₂ : Complex.exp (-(t : ℂ) / 2) * Complex.exp (-(α : ℂ) * t) =
      Complex.exp (-((α : ℂ) + 1 / 2) * t) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [div_eq_mul_inv]
  calc
    _ = ((1 / 4 : ℂ) - κ ^ 2)⁻¹ *
        (Complex.exp (-κ * t) * Complex.exp (-(α : ℂ) * t) -
          Complex.exp (-(t : ℂ) / 2) * Complex.exp (-(α : ℂ) * t)) := by ring
    _ = _ := by rw [h₁, h₂]

theorem cuspWeightedConstantPairing_integrable {α : ℝ} (hα : 0 ≤ α) {κ : ℂ}
    (hβ : 0 < ((α : ℂ) + κ).re)
    (hp : κ ≠ (1 / 2 : ℂ)) (hm : κ ≠ -(1 / 2 : ℂ)) (F : ModularHilbert) :
    IntegrableOn (fun t : ℝ => cuspConstantLogResponse κ t *
      Complex.exp (-(α : ℂ) * t) * cuspHalfLineSourceCoefficient F t) (Ioi 0) := by
  have hh : 0 < ((α : ℂ) + 1 / 2).re := by simp only [Complex.add_re]; norm_num; linarith
  apply (((laplace_integrable hβ (cuspHalfLineSourceCoefficient F)).sub
    (laplace_integrable hh (cuspHalfLineSourceCoefficient F))).const_mul
      (((1 / 4 : ℂ) - κ ^ 2)⁻¹)).congr
  exact Filter.Eventually.of_forall fun t => by
    dsimp only [Pi.sub_apply]
    rw [weightedConstantLogResponse_eq α hp hm t]
    ring

theorem cuspWeightedConstantPairingFunctional_apply {α : ℝ} (hα : 0 ≤ α) {κ : ℂ}
    (hβ : 0 < ((α : ℂ) + κ).re)
    (hp : κ ≠ (1 / 2 : ℂ)) (hm : κ ≠ -(1 / 2 : ℂ)) (F : ModularHilbert) :
    cuspWeightedConstantPairingFunctional α κ F =
      ∫ t : ℝ in Ioi 0, cuspConstantLogResponse κ t *
        Complex.exp (-(α : ℂ) * t) * cuspHalfLineSourceCoefficient F t := by
  have hh : 0 < ((α : ℂ) + 1 / 2).re := by simp only [Complex.add_re]; norm_num; linarith
  change ((1 / 4 : ℂ) - κ ^ 2)⁻¹ *
    (laplace ((α : ℂ) + κ) (cuspHalfLineSourceCoefficient F) -
      laplace ((α : ℂ) + 1 / 2) (cuspHalfLineSourceCoefficient F)) = _
  rw [laplace_apply hβ, laplace_apply hh,
    ← integral_sub (laplace_integrable hβ _) (laplace_integrable hh _),
    ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by
    dsimp only
    rw [weightedConstantLogResponse_eq α hp hm t]
    ring

end GapFamily.Analytic
