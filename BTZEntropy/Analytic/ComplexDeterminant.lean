import BTZEntropy.Analytic.ComplexEulerBound
import BTZEntropy.Analytic.ReferenceAssembly
import BTZEntropy.Analytic.ComplexKernel

/-!
# Holomorphic continuation of the dual boundary-graviton determinant

The modularly transformed Euler product supplies an explicit holomorphic
continuation of the actual positive-temperature determinant. This expression
also exposes its decay along vertical contours.
-/

noncomputable section

open scoped Topology

namespace BTZEntropy

def complexDualTemperature (z : ℂ) : ℂ := 4 * (Real.pi : ℂ) ^ 2 / z

def complexDualBoundaryGravitonFactor (z : ℂ) : ℂ :=
  (1 - Complex.exp (-complexDualTemperature z)) ^ 2 *
    (2 * (Real.pi : ℂ) / z) * Complex.exp ((z - complexDualTemperature z) / 12) *
    (complexEulerProduct (Complex.exp (-z)))⁻¹ ^ 2

def complexAmplitude (φ : SmoothKernel) (z : ℂ) : ℂ :=
  complexKernelTransform φ z * complexDualBoundaryGravitonFactor z

theorem complexEulerProduct_exp_ofReal {β : ℝ} (hβ : 0 < β) :
    complexEulerProduct (Complex.exp (-(β : ℂ))) = ((descendantEuler β)⁻¹ : ℝ) := by
  have h := (hasProd_thermalEuler hβ).map Complex.ofRealHom Complex.continuous_ofReal
  simpa [complexEulerProduct, thermalNome, Complex.ofReal_exp] using h.tprod_eq

theorem descendantEuler_sq_dual_solved {β : ℝ} (hβ : 0 < β) :
    descendantEuler (dualTemperature β) ^ 2 =
      (2 * Real.pi / β) * Real.exp ((β - dualTemperature β) / 12) *
        descendantEuler β ^ 2 := by
  rw [descendantEuler_sq_dual β hβ]
  symm
  have he : Real.exp ((β - dualTemperature β) / 12) *
      Real.exp ((dualTemperature β - β) / 12) = 1 := by
    rw [← Real.exp_add]
    have hzero : (β - dualTemperature β) / 12 + (dualTemperature β - β) / 12 = 0 := by ring
    rw [hzero, Real.exp_zero]
  calc
    _ = (2 * Real.pi / β * (β / (2 * Real.pi))) *
        (Real.exp ((β - dualTemperature β) / 12) *
          Real.exp ((dualTemperature β - β) / 12)) *
        descendantEuler (dualTemperature β) ^ 2 := by ring
    _ = _ := by rw [he]; field_simp

theorem complexDualBoundaryGravitonFactor_ofReal {β : ℝ} (hβ : 0 < β) :
    complexDualBoundaryGravitonFactor β =
      (boundaryGravitonFactor (dualTemperature β) : ℂ) := by
  rw [complexDualBoundaryGravitonFactor, complexEulerProduct_exp_ofReal hβ,
    boundaryGravitonFactor_eq_descendantEuler (dualTemperature_pos hβ),
    descendantEuler_sq_dual_solved hβ]
  simp only [complexDualTemperature, dualTemperature, ← Complex.ofReal_pow,
    ← Complex.ofReal_ofNat, ← Complex.ofReal_mul, ← Complex.ofReal_div,
    ← Complex.ofReal_sub, ← Complex.ofReal_neg, ← Complex.ofReal_exp,
    ← Complex.ofReal_one, ← Complex.ofReal_inv, inv_inv]
  push_cast
  ring

theorem complexAmplitude_ofReal (φ : SmoothKernel) {β : ℝ} (hβ : 0 < β) :
    complexAmplitude φ β = (amplitude φ β : ℂ) := by
  rw [complexAmplitude, complexKernelTransform_ofReal,
    complexDualBoundaryGravitonFactor_ofReal hβ]
  simp [amplitude, dualTemperature]

theorem norm_exp_neg_lt_one {z : ℂ} (hz : 0 < z.re) :
    ‖Complex.exp (-z)‖ < 1 := by
  rw [Complex.norm_exp, Complex.neg_re]
  exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos hz)

theorem analyticAt_complexDualBoundaryGravitonFactor {z : ℂ} (hz : 0 < z.re) :
    AnalyticAt ℂ complexDualBoundaryGravitonFactor z := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hd : AnalyticAt ℂ complexDualTemperature z :=
    analyticAt_const.div analyticAt_id hz0
  have he := analyticAt_complexEulerProduct_inv_sq (norm_exp_neg_lt_one hz)
  have hexp : AnalyticAt ℂ (fun w : ℂ => Complex.exp (-w)) z := by fun_prop
  exact ((((analyticAt_const.sub (hd.neg.cexp)).pow 2).mul
    (analyticAt_const.div analyticAt_id hz0)).mul
    ((analyticAt_id.sub hd).div_const (c := 12)).cexp).mul
      (he.comp (f := fun w : ℂ => Complex.exp (-w)) hexp)

theorem analyticAt_complexAmplitude (φ : SmoothKernel) {z : ℂ} (hz : 0 < z.re) :
    AnalyticAt ℂ (complexAmplitude φ) z :=
  (analyticAt_complexKernelTransform φ z).mul
    (analyticAt_complexDualBoundaryGravitonFactor hz)

end BTZEntropy
