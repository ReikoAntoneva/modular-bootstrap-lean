import GapFamily.Analytic.Cusp.Scalar.CuspConstantResponseAnalytic
import GapFamily.Analytic.Cusp.Profile.CuspLogCoordinateEnergy
import GapFamily.Analytic.Cusp.Profile.CuspLogCoordinateEnergyCore

/-! Actual finite scalar form energy of the noncompact constant-source response. -/
noncomputable section
namespace GapFamily.Analytic
open Set MeasureTheory Filter
open scoped Topology

/-- Ordinary shifted derivative energy, transported from the actual physical profile. -/
theorem cuspConstantLogResponse_shifted_energy {κ : ℂ} (hκ : 0 < κ.re) :
    (∫ t in Ioi (0 : ℝ), ‖deriv (cuspConstantLogResponse κ) t +
      (1 / 2 : ℝ) • cuspConstantLogResponse κ t‖ ^ 2) =
      1 / (2 * κ.re * ‖κ + 1 / 2‖ ^ 2) := by
  have hm : κ ≠ -(1 / 2 : ℂ) := by intro h; subst κ; norm_num at hκ
  have hv : Differentiable ℝ (cuspConstantLogResponse κ) :=
    fun t => (hasDerivAt_cuspConstantLogResponse hm t).differentiableAt
  rw [← integral_deriv_cuspLift_norm_sq hv]
  simpa only [cuspConstantPhysicalResponse, integral_Ici_eq_integral_Ioi] using
    integral_cuspConstantPhysicalResponse_deriv_sq hκ

/-- Both ordinary parts of the unshifted scalar form density are integrable. -/
theorem cuspConstantLogResponse_form_integrable {κ : ℂ} (hκ : 0 < κ.re) :
    IntegrableOn (fun t => ‖deriv (cuspConstantLogResponse κ) t‖ ^ 2 +
      ‖cuspConstantLogResponse κ t‖ ^ 2 / 4) (Ioi 0) :=
  ((cuspConstantLogResponse_deriv_memLp hκ).norm.integrable_sq).add
    ((cuspConstantLogResponse_memLp hκ).norm.integrable_sq.div_const 4)

/-- Genuine FTC boundary cancellation identifies the finite scalar form energy. -/
theorem cuspConstantLogResponse_form_energy {κ : ℂ} (hκ : 0 < κ.re) :
    (∫ t in Ioi (0 : ℝ), (‖deriv (cuspConstantLogResponse κ) t‖ ^ 2 +
      ‖cuspConstantLogResponse κ t‖ ^ 2 / 4)) =
      1 / (2 * κ.re * ‖κ + 1 / 2‖ ^ 2) := by
  have hm : κ ≠ -(1 / 2 : ℂ) := by intro h; subst κ; norm_num at hκ
  have hv : ContDiff ℝ 1 (cuspConstantLogResponse κ) :=
    (cuspConstantLogResponse_contDiff hm).of_le le_top
  have hm' : IntegrableOn (fun t => ‖cuspConstantLogResponse κ t‖ ^ 2) (Ioi 0) :=
    (cuspConstantLogResponse_memLp hκ).norm.integrable_sq
  have hd' : IntegrableOn (fun t => ‖deriv (cuspConstantLogResponse κ) t‖ ^ 2) (Ioi 0) :=
    (cuspConstantLogResponse_deriv_memLp hκ).norm.integrable_sq
  have ht : Tendsto (fun t => ‖cuspConstantLogResponse κ t‖ ^ 2) atTop (𝓝 0) := by
    simpa using (cuspConstantLogResponse_tendsto_zero hκ).norm.pow 2
  rw [← cusp_log_core_energy_identity_of_integrable hv hm' hd'
    (cuspConstantLogResponse_boundary κ) ht]
  exact cuspConstantLogResponse_shifted_energy hκ

end GapFamily.Analytic
