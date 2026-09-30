import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Logarithmic coordinates in the scalar cusp channel

The actual map `u ↦ sqrt(y) • u(log y)` carries ordinary squared mass in the
logarithmic coordinate to hyperbolic squared mass `dy/y²` above a positive cusp
height. The extended-integral identity includes infinite values, and genuine
integrability is transported in both directions.
-/

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace GapFamily.Analytic

/-- The scalar cusp coordinate substitution, with its square-root normalization. -/
def cuspLift {E : Type*} [SMul ℝ E] (u : ℝ → E) (y : ℝ) : E :=
  Real.sqrt y • u (Real.log y)

/-- The actual hyperbolic measure in the scalar vertical channel above height `Y`. -/
def cuspMeasure (Y : ℝ) : Measure ℝ :=
  (volume.restrict (Ici Y)).withDensity (fun y : ℝ => ENNReal.ofReal ((y^2)⁻¹))

/-- Positive logarithmic substitution for nonnegative extended integrals.
No integrability premise can hide divergence in this identity. -/
theorem lintegral_log_weight_Ici (g : ℝ → ℝ≥0∞) {Y : ℝ} (hY : 0 < Y) :
    (∫⁻ y in Ici Y, ENNReal.ofReal (y⁻¹) * g (Real.log y)) =
      ∫⁻ t in Ici (Real.log Y), g t := by
  have h := lintegral_image_eq_lintegral_abs_deriv_mul (measurableSet_Ici (a := Real.log Y))
    (fun t _ => (Real.hasDerivAt_exp t).hasDerivWithinAt) Real.exp_injective.injOn
    (fun y : ℝ => ENNReal.ofReal (y⁻¹) * g (Real.log y))
  rw [Real.image_exp_Ici, Real.exp_log hY] at h
  rw [h]
  apply lintegral_congr
  intro t
  rw [Real.log_exp, abs_of_pos (Real.exp_pos t), ← mul_assoc,
    ← ENNReal.ofReal_mul (Real.exp_pos t).le]
  simp [Real.exp_ne_zero]

/-- Logarithmic substitution transports ordinary integrability, including measurability. -/
theorem integrableOn_log_weight_Ici {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → E) {Y : ℝ} (hY : 0 < Y) :
    IntegrableOn (fun y : ℝ => y⁻¹ • g (Real.log y)) (Ici Y) ↔
      IntegrableOn g (Ici (Real.log Y)) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul
    (measurableSet_Ici (a := Real.log Y))
    (fun t _ => (Real.hasDerivAt_exp t).hasDerivWithinAt) Real.exp_injective.injOn
    (fun y : ℝ => y⁻¹ • g (Real.log y))
  rw [Real.image_exp_Ici, Real.exp_log hY] at h
  simpa only [Real.log_exp, abs_of_pos (Real.exp_pos _), smul_smul,
    mul_inv_cancel₀ (Real.exp_ne_zero _), one_smul] using h

/-- The scalar normalization cancels one power of hyperbolic decay. -/
theorem cuspLift_norm_sq_div {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : ℝ → E) {y : ℝ} (hy : 0 < y) :
    ‖cuspLift u y‖^2 / y^2 = y⁻¹ * ‖u (Real.log y)‖^2 := by
  rw [cuspLift, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    mul_pow, Real.sq_sqrt hy.le]
  field_simp

/-- Equality of the actual extended squared norms, valid before either side is
known to be finite and for both real and complex valued channels. -/
theorem lintegral_cuspLift_norm_sq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : ℝ → E) {Y : ℝ} (hY : 0 < Y) :
    (∫⁻ y in Ici Y, ENNReal.ofReal (‖cuspLift u y‖^2 / y^2)) =
      ∫⁻ t in Ici (Real.log Y), ENNReal.ofReal (‖u t‖^2) := by
  rw [← lintegral_log_weight_Ici (fun t => ENNReal.ofReal (‖u t‖^2)) hY]
  apply setLIntegral_congr_fun measurableSet_Ici
  intro y hy
  dsimp only
  rw [cuspLift_norm_sq_div u (hY.trans_le hy),
    ENNReal.ofReal_mul (inv_nonneg.mpr (hY.trans_le hy).le)]

/-- Finiteness and measurability of the actual weighted squared norm are
exactly finiteness and measurability of the logarithmic squared norm. -/
theorem integrableOn_cuspLift_norm_sq_iff {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (u : ℝ → E) {Y : ℝ} (hY : 0 < Y) :
    IntegrableOn (fun y => ‖cuspLift u y‖^2 / y^2) (Ici Y) ↔
      IntegrableOn (fun t => ‖u t‖^2) (Ici (Real.log Y)) := by
  rw [← integrableOn_log_weight_Ici (fun t => ‖u t‖^2) hY]
  apply integrableOn_congr_fun _ measurableSet_Ici
  intro y hy
  exact cuspLift_norm_sq_div u (hY.trans_le hy)

/-- The extended norm identity expressed using the actual vertical hyperbolic measure. -/
theorem lintegral_cuspMeasure_cuspLift_norm_sq {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (u : ℝ → E) {Y : ℝ} (hY : 0 < Y) :
    (∫⁻ y, ENNReal.ofReal (‖cuspLift u y‖^2) ∂cuspMeasure Y) =
      ∫⁻ t in Ici (Real.log Y), ENNReal.ofReal (‖u t‖^2) := by
  rw [cuspMeasure, lintegral_withDensity_eq_lintegral_mul_non_measurable _
    (by fun_prop) (by simp)]
  calc
    _ = ∫⁻ y in Ici Y, ENNReal.ofReal (‖cuspLift u y‖^2 / y^2) := by
      apply lintegral_congr
      intro y
      dsimp only [Pi.mul_apply]
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      simp [div_eq_mul_inv, mul_comm]
    _ = _ := lintegral_cuspLift_norm_sq u hY

/-- Integrability of the squared norm for the hyperbolic measure is equivalent
to ordinary integrability of the logarithmic squared norm. -/
theorem integrable_cuspMeasure_cuspLift_norm_sq_iff {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (u : ℝ → E) {Y : ℝ} (hY : 0 < Y) :
    Integrable (fun y => ‖cuspLift u y‖^2) (cuspMeasure Y) ↔
      IntegrableOn (fun t => ‖u t‖^2) (Ici (Real.log Y)) := by
  rw [cuspMeasure, integrable_withDensity_iff_integrable_smul' (by fun_prop) (by simp)]
  have heq : (fun y : ℝ => (ENNReal.ofReal ((y^2)⁻¹)).toReal • ‖cuspLift u y‖^2) =
      (fun y : ℝ => ‖cuspLift u y‖^2/y^2) := by
    funext y
    rw [ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
    simp [div_eq_mul_inv, mul_comm]
  rw [heq]
  exact integrableOn_cuspLift_norm_sq_iff u hY

/-- The finite ordinary squared norms agree whenever the logarithmic channel
has integrable squared norm; the preceding equivalence proves the other side's
integrability rather than relying on totalized integral values. -/
theorem integral_cuspMeasure_cuspLift_norm_sq {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (u : ℝ → E) {Y : ℝ} (hY : 0 < Y)
    (hu : IntegrableOn (fun t => ‖u t‖^2) (Ici (Real.log Y))) :
    (∫ y, ‖cuspLift u y‖^2 ∂cuspMeasure Y) =
      ∫ t in Ici (Real.log Y), ‖u t‖^2 := by
  have hl := (integrable_cuspMeasure_cuspLift_norm_sq_iff u hY).mpr hu
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun y => sq_nonneg _))
    hl.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun t => sq_nonneg _))
      hu.aestronglyMeasurable,
    lintegral_cuspMeasure_cuspLift_norm_sq u hY]

/-- Measurability is preserved by the actual coordinate and scalar maps. -/
theorem measurable_cuspLift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {u : ℝ → E} (hu : Measurable u) : Measurable (cuspLift u) := by
  unfold cuspLift
  fun_prop

/-- The substitution preserves actual `MemLp 2`, including vector-valued
measurability, for measurable channels such as real or complex scalar modes. -/
theorem memLp_two_cuspLift_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {u : ℝ → E} (hu : Measurable u) {Y : ℝ} (hY : 0 < Y) :
    MemLp (cuspLift u) 2 (cuspMeasure Y) ↔
      MemLp u 2 (volume.restrict (Ici (Real.log Y))) := by
  rw [memLp_two_iff_integrable_sq_norm (measurable_cuspLift hu).aestronglyMeasurable,
    memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable]
  exact integrable_cuspMeasure_cuspLift_norm_sq_iff u hY

/-- The inverse coordinate map is explicit at the level of ordinary functions. -/
def cuspPullback {E : Type*} [SMul ℝ E] (f : ℝ → E) (t : ℝ) : E :=
  (Real.sqrt (Real.exp t))⁻¹ • f (Real.exp t)

theorem cuspPullback_cuspLift {E : Type*} [AddCommGroup E] [Module ℝ E]
    (u : ℝ → E) : cuspPullback (cuspLift u) = u := by
  funext t
  simp [cuspPullback, cuspLift, smul_smul, Real.sqrt_ne_zero'.mpr (Real.exp_pos t)]

theorem cuspLift_cuspPullback {E : Type*} [AddCommGroup E] [Module ℝ E]
    (f : ℝ → E) {y : ℝ} (hy : 0 < y) : cuspLift (cuspPullback f) y = f y := by
  simp [cuspPullback, cuspLift, Real.exp_log hy, smul_smul, Real.sqrt_ne_zero'.mpr hy]

end GapFamily.Analytic
