import GapFamily.Analytic.Cusp.Scalar.CuspConstantResponsePhysical
/-!
# Ordinary constant-source mass pairing in the physical cusp coordinate

The exponential change of variables identifies the actual integral against
`dy/y²` with the already integrable logarithmic pairing on `Re κ > -1/2`.
The removable value `κ = 1/2` is included throughout.
-/

open MeasureTheory Set
noncomputable section
namespace GapFamily.Analytic
private theorem physical_pairing_exp (κ : ℂ) (t : ℝ) :
    Real.exp t • (cuspConstantPhysicalResponse κ (Real.exp t) /
      ((Real.exp t : ℝ) : ℂ)^2) =
      Complex.exp (-(t : ℂ)/2) * cuspConstantLogResponse κ t := by
  rw [cuspConstantPhysicalResponse, cuspLift, Real.log_exp, Complex.real_smul,
    Complex.real_smul]
  have hc : ((Real.exp t : ℝ) : ℂ) * ((Real.sqrt (Real.exp t) : ℝ) : ℂ) /
      ((Real.exp t : ℝ) : ℂ)^2 = Complex.exp (-(t : ℂ)/2) := by
    rw [← Real.exp_half, Complex.ofReal_exp, Complex.ofReal_exp,
      ← Complex.exp_nat_mul, ← Complex.exp_add, ← Complex.exp_sub]
    congr 1
    push_cast
    ring
  calc
    _ = (((Real.exp t : ℝ) : ℂ) * ((Real.sqrt (Real.exp t) : ℝ) : ℂ) /
        ((Real.exp t : ℝ) : ℂ)^2) * cuspConstantLogResponse κ t := by ring
    _ = _ := by rw [hc]

/-- Absolute integrability of the actual physical-coordinate pairing on its
convergence half-plane, including the removable parameter. -/
theorem cuspConstantPhysicalResponse_pairing_integrable {κ : ℂ} (hκ : -(1/2 : ℝ) < κ.re) :
    IntegrableOn (fun y : ℝ => cuspConstantPhysicalResponse κ y / (y : ℂ)^2) (Ioi 1) := by
  have h := (integrableOn_comp_exp_Ioi
    (fun y : ℝ => cuspConstantPhysicalResponse κ y / (y : ℂ)^2) 0)
  simp only [physical_pairing_exp, Real.exp_zero] at h
  exact h.mp (cuspConstantLogResponse_pairing_integrable hκ)

/-- Evaluation of the ordinary physical-coordinate pairing against `dy/y²`. -/
theorem cuspConstantPhysicalResponse_pairing {κ : ℂ} (hκ : -(1/2 : ℝ) < κ.re) :
    (∫ y : ℝ in Ioi 1, cuspConstantPhysicalResponse κ y / (y : ℂ)^2) =
      1 / (κ + 1/2)^2 := by
  have h := integral_comp_exp_Ioi
    (fun y : ℝ => cuspConstantPhysicalResponse κ y / (y : ℂ)^2) 0
  simp only [physical_pairing_exp, Real.exp_zero] at h
  rw [← h]
  exact cuspConstantLogResponse_pairing hκ
private theorem integrable_cuspMeasure_one_iff (f : ℝ → ℂ) :
    Integrable f (cuspMeasure 1) ↔
      IntegrableOn (fun y : ℝ => f y / (y : ℂ)^2) (Ioi 1) := by
  rw [cuspMeasure, integrable_withDensity_iff_integrable_smul' (by fun_prop) (by simp)]
  have heq : (fun y : ℝ => (ENNReal.ofReal ((y^2)⁻¹)).toReal • f y) =
      (fun y : ℝ => f y / (y : ℂ)^2) := by
    funext y
    rw [ENNReal.toReal_ofReal (by positivity), Complex.real_smul]
    simp [div_eq_mul_inv, mul_comm]
  rw [heq]
  exact integrableOn_Ici_iff_integrableOn_Ioi

private theorem integral_cuspMeasure_one_eq (f : ℝ → ℂ) :
    (∫ y, f y ∂cuspMeasure 1) =
      ∫ y in Ioi (1 : ℝ), f y / (y : ℂ)^2 := by
  rw [cuspMeasure, integral_withDensity_eq_integral_toReal_smul (by fun_prop) (by simp)]
  have heq : (fun y : ℝ => (ENNReal.ofReal ((y^2)⁻¹)).toReal • f y) =
      (fun y : ℝ => f y / (y : ℂ)^2) := by
    funext y
    rw [ENNReal.toReal_ofReal (by positivity), Complex.real_smul]
    simp [div_eq_mul_inv, mul_comm]
  rw [heq, integral_Ici_eq_integral_Ioi]

/-- The actual response is integrable for the vertical hyperbolic measure on
the full pairing convergence half-plane. This is weaker than L² membership. -/
theorem cuspConstantPhysicalResponse_integrable_cuspMeasure {κ : ℂ}
    (hκ : -(1 / 2 : ℝ) < κ.re) :
    Integrable (cuspConstantPhysicalResponse κ) (cuspMeasure 1) :=
  (integrable_cuspMeasure_one_iff _).mpr
    (cuspConstantPhysicalResponse_pairing_integrable hκ)

/-- The ordinary integral in the actual vertical hyperbolic measure, with
integrability supplied by the preceding theorem. -/
theorem cuspConstantPhysicalResponse_integral_cuspMeasure {κ : ℂ}
    (hκ : -(1 / 2 : ℝ) < κ.re) :
    (∫ y, cuspConstantPhysicalResponse κ y ∂cuspMeasure 1) =
      1 / (κ + 1 / 2)^2 := by
  rw [integral_cuspMeasure_one_eq]
  exact cuspConstantPhysicalResponse_pairing hκ

/-- Actual ordinary integrability of the physical squared-mass density on the
physical parameter half-plane. -/
theorem cuspConstantPhysicalResponse_norm_sq_div_integrable {κ : ℂ}
    (hκ : 0 < κ.re) :
    IntegrableOn (fun y : ℝ => ‖cuspConstantPhysicalResponse κ y‖ ^ 2 / y ^ 2)
      (Ioi 1) := by
  have h := (cuspConstantPhysicalResponse_memLp hκ).norm.integrable_sq
  rw [cuspMeasure,
    integrable_withDensity_iff_integrable_smul' (by fun_prop) (by simp)] at h
  have heq : (fun y : ℝ => (ENNReal.ofReal ((y ^ 2)⁻¹)).toReal •
      ‖cuspConstantPhysicalResponse κ y‖ ^ 2) =
      (fun y : ℝ => ‖cuspConstantPhysicalResponse κ y‖ ^ 2 / y ^ 2) := by
    funext y
    rw [ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
    simp [div_eq_mul_inv, mul_comm]
  rw [heq] at h
  rw [← restrict_Ioi_eq_restrict_Ici] at h
  exact h

/-- The two squared-mass expressions are the same weighted integral.
The preceding theorem proves finiteness when `Re κ > 0`. -/
theorem integral_cuspConstantPhysicalResponse_norm_sq_div (κ : ℂ) :
    (∫ y : ℝ in Ioi 1, ‖cuspConstantPhysicalResponse κ y‖ ^ 2 / y ^ 2) =
      ∫ y, ‖cuspConstantPhysicalResponse κ y‖ ^ 2 ∂cuspMeasure 1 := by
  rw [cuspMeasure, integral_withDensity_eq_integral_toReal_smul (by fun_prop) (by simp),
    integral_Ici_eq_integral_Ioi]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  dsimp only
  rw [ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
  simp [div_eq_mul_inv, mul_comm]

end GapFamily.Analytic
