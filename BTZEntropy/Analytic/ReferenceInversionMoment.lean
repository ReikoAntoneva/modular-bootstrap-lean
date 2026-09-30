import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr

/-!
# Thermal domination of polynomial energy moments

An integrable thermal weight at half the inverse temperature controls every
polynomial energy moment. The same majorant is uniform on a closed complex
right half-plane and applies to the differentiated Laplace integrand.
-/

noncomputable section

open MeasureTheory

namespace BTZEntropy

/-- Sacrificing half the thermal decay controls any polynomial energy moment. -/
theorem thermalMoment_le {x β : ℝ} (hx : 0 ≤ x) (hβ : 0 < β) (n : ℕ) :
    x ^ n * Real.exp (-β * x) ≤
      (n.factorial : ℝ) * (2 / β) ^ n * Real.exp (-(β / 2) * x) := by
  have hfact : (0 : ℝ) < n.factorial := by positivity
  have hseries := Real.pow_div_factorial_le_exp ((β / 2) * x)
    (show 0 ≤ (β / 2) * x by positivity) n
  have hpow : ((β / 2) * x) ^ n ≤
      (n.factorial : ℝ) * Real.exp ((β / 2) * x) := by
    exact (div_le_iff₀ hfact).mp hseries |>.trans_eq (mul_comm _ _)
  have hcancel : (2 / β) * ((β / 2) * x) = x := by field_simp
  calc
    x ^ n * Real.exp (-β * x) =
        (2 / β) ^ n * ((β / 2) * x) ^ n * Real.exp (-β * x) := by
          rw [← mul_pow, hcancel]
    _ ≤ (2 / β) ^ n * ((n.factorial : ℝ) * Real.exp ((β / 2) * x)) *
        Real.exp (-β * x) := by gcongr
    _ = (n.factorial : ℝ) * (2 / β) ^ n *
        (Real.exp ((β / 2) * x) * Real.exp (-β * x)) := by ring
    _ = (n.factorial : ℝ) * (2 / β) ^ n * Real.exp (-(β / 2) * x) := by
      rw [← Real.exp_add]
      congr 2
      ring

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- One absolute thermal moment at half the inverse temperature implies
integrability of every energy moment, including signed measurable weights. -/
theorem integrable_abs_weight_thermalMoment {energy weight : α → ℝ} {β : ℝ}
    (he : Measurable energy) (hw : Measurable weight)
    (henergy : ∀ᵐ q ∂μ, 0 ≤ energy q) (hβ : 0 < β)
    (hthermal : Integrable (fun q => weight q * Real.exp (-(β / 2) * energy q)) μ)
    (n : ℕ) :
    Integrable (fun q => |weight q| * energy q ^ n * Real.exp (-β * energy q)) μ := by
  have hmajor := hthermal.norm.const_mul ((n.factorial : ℝ) * (2 / β) ^ n)
  apply hmajor.mono'
  · exact (((continuous_abs.measurable.comp hw).mul (he.pow_const n)).mul
      (Real.measurable_exp.comp (measurable_const.mul he))).aestronglyMeasurable
  · filter_upwards [henergy] with q hq
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ |weight q| * energy q ^ n * Real.exp (-β * energy q))]
    have h := mul_le_mul_of_nonneg_left (thermalMoment_le hq hβ n) (abs_nonneg (weight q))
    simpa only [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      mul_assoc, mul_left_comm, mul_comm] using h

/-- The norm of a complex thermal moment is its ordinary real thermal weight. -/
theorem norm_weightedComplexThermalMoment (x w : ℝ) (z : ℂ) (n : ℕ)
    (hx : 0 ≤ x) :
    ‖(w : ℂ) * (x : ℂ) ^ n * Complex.exp (-z * (x : ℂ))‖ =
      |w| * x ^ n * Real.exp (-z.re * x) := by
  simp [norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hx, Complex.norm_exp, Complex.mul_re]

/-- A fixed real inverse temperature controls every complex thermal moment to
its right. -/
theorem norm_weightedComplexThermalMoment_le {x β : ℝ} (w : ℝ) {z : ℂ}
    (n : ℕ) (hx : 0 ≤ x) (hz : β ≤ z.re) :
    ‖(w : ℂ) * (x : ℂ) ^ n * Complex.exp (-z * (x : ℂ))‖ ≤
      |w| * x ^ n * Real.exp (-β * x) := by
  rw [norm_weightedComplexThermalMoment x w z n hx]
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
  exact mul_le_mul_of_nonneg_right (neg_le_neg hz) hx

/-- The first derivative of a weighted Laplace integrand has a uniform thermal
majorant throughout a closed right half-plane. -/
theorem norm_weightedComplexThermalDerivative_le {x β : ℝ} (w : ℝ) {z : ℂ}
    (hx : 0 ≤ x) (hz : β ≤ z.re) :
    ‖-(x : ℂ) * (w : ℂ) * Complex.exp (-z * (x : ℂ))‖ ≤
      |w| * x * Real.exp (-β * x) := by
  have h := norm_weightedComplexThermalMoment_le w 1 hx hz
  simpa only [pow_one, neg_mul, norm_neg, mul_comm (x : ℂ) (w : ℂ)] using h

/-- Every polynomially weighted complex Laplace integrand is integrable to the
right of a positive inverse temperature with a half-temperature moment. -/
theorem integrable_weightedComplexThermalMoment {energy weight : α → ℝ}
    {β : ℝ} {z : ℂ} (he : Measurable energy) (hw : Measurable weight)
    (henergy : ∀ᵐ q ∂μ, 0 ≤ energy q) (hβ : 0 < β)
    (hthermal : Integrable (fun q => weight q * Real.exp (-(β / 2) * energy q)) μ)
    (hz : β ≤ z.re) (n : ℕ) :
    Integrable (fun q => (weight q : ℂ) * (energy q : ℂ) ^ n *
      Complex.exp (-z * (energy q : ℂ))) μ := by
  apply (integrable_abs_weight_thermalMoment he hw henergy hβ hthermal n).mono'
  · exact (((Complex.measurable_ofReal.comp hw).mul
      ((Complex.measurable_ofReal.comp he).pow_const n)).mul
      (Complex.measurable_exp.comp
        (measurable_const.mul (Complex.measurable_ofReal.comp he)))).aestronglyMeasurable
  · filter_upwards [henergy] with q hq
    exact norm_weightedComplexThermalMoment_le (weight q) n hq hz

/-- In particular, the actual first derivative integrand is integrable. -/
theorem integrable_weightedComplexThermalDerivative {energy weight : α → ℝ}
    {β : ℝ} {z : ℂ} (he : Measurable energy) (hw : Measurable weight)
    (henergy : ∀ᵐ q ∂μ, 0 ≤ energy q) (hβ : 0 < β)
    (hthermal : Integrable (fun q => weight q * Real.exp (-(β / 2) * energy q)) μ)
    (hz : β ≤ z.re) :
    Integrable (fun q => -(energy q : ℂ) * (weight q : ℂ) *
      Complex.exp (-z * (energy q : ℂ))) μ := by
  have h := (integrable_weightedComplexThermalMoment he hw henergy hβ hthermal hz 1).neg
  convert h using 1
  funext q
  simp only [Pi.neg_apply, pow_one]
  ring

end BTZEntropy
