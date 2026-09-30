import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!+# Integral estimates for smooth cusp profile cutoffs

These estimates use ordinary integrals with the literal weights of the scalar
cusp value and vertical derivative. The cutoff hypotheses are quantitative
properties to be supplied by the constructed smooth cutoff sequence.
-/

noncomputable section

namespace GapFamily.Analytic

open Set Filter MeasureTheory
open scoped Topology ContDiff

private theorem norm_cutoff_sub_le {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (v : ℂ) :
    ‖a • v - v‖ ≤ ‖v‖ := by
  have heq : a • v - v = (a - 1) • v := by simp [sub_smul]
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr ha1)]
  nlinarith [norm_nonneg v]

theorem cuspProfile_cutoff_value_error_le {a y : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (v : ℂ) : ‖a • v - v‖ ^ 2 / y ^ 2 ≤ ‖v‖ ^ 2 / y ^ 2 := by
  exact div_le_div_of_nonneg_right
    ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (norm_cutoff_sub_le ha0 ha1 v))
    (sq_nonneg y)

theorem cuspProfile_cutoff_deriv_error_le {χ : ℝ → ℝ} {b : ℝ → ℂ} {y : ℝ}
    (hχ : DifferentiableAt ℝ χ y) (hb : DifferentiableAt ℝ b y)
    (hχ0 : 0 ≤ χ y) (hχ1 : χ y ≤ 1) :
    ‖deriv (fun x => χ x • b x) y - deriv b y‖ ≤
      ‖deriv χ y‖ * ‖b y‖ + ‖deriv b y‖ := by
  rw [deriv_fun_smul hχ hb, add_comm (χ y • deriv b y) (deriv χ y • b y)]
  calc
    ‖deriv χ y • b y + χ y • deriv b y - deriv b y‖ =
        ‖deriv χ y • b y + (χ y • deriv b y - deriv b y)‖ := by rw [add_sub_assoc]
    _ ≤ ‖deriv χ y • b y‖ + ‖χ y • deriv b y - deriv b y‖ := norm_add_le _ _
    _ ≤ ‖deriv χ y‖ * ‖b y‖ + ‖deriv b y‖ := by
      rw [norm_smul]
      exact add_le_add le_rfl (norm_cutoff_sub_le hχ0 hχ1 _)

/-- A fixed integrable majorant for the squared derivative error. Its three
terms are derivative energy, a finite collar constant, and weighted value energy. -/
def cuspProfileDerivativeMajorant (b : ℝ → ℂ) (C L : ℝ) (y : ℝ) : ℝ :=
  2 * ‖deriv b y‖ ^ 2 +
    (Icc (1 : ℝ) 2).indicator (fun _ => 2 * (C * L) ^ 2) y +
    2 * C ^ 2 * (‖b y‖ ^ 2 / y ^ 2)

theorem cuspProfileDerivativeMajorant_integrable {b : ℝ → ℂ} (C L : ℝ)
    (hv : IntegrableOn (fun y => ‖b y‖ ^ 2 / y ^ 2) (Ioi 1))
    (hd : IntegrableOn (fun y => ‖deriv b y‖ ^ 2) (Ioi 1)) :
    IntegrableOn (cuspProfileDerivativeMajorant b C L) (Ioi 1) := by
  have hc : Integrable ((Icc (1 : ℝ) 2).indicator (fun _ => 2 * (C * L) ^ 2)) volume :=
    (integrableOn_const (by simp : volume (Icc (1 : ℝ) 2) ≠ ⊤)).integrable_indicator
      measurableSet_Icc
  exact ((hd.const_mul 2).add hc.integrableOn).add (hv.const_mul (2 * C ^ 2))

theorem cuspProfile_cutoff_deriv_sq_le {χ : ℝ → ℝ} {b : ℝ → ℂ} {C L y : ℝ}
    (hχ : DifferentiableAt ℝ χ y) (hb : DifferentiableAt ℝ b y)
    (hχ0 : 0 ≤ χ y) (hχ1 : χ y ≤ 1) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hy : 1 < y)
    (hbnd : ∀ x ∈ Icc (1 : ℝ) 2, ‖b x‖ ≤ L * (x - 1))
    (hderiv : ‖deriv χ y‖ ≤ if y ≤ 2 then C / (y - 1) else C / y) :
    ‖deriv (fun x => χ x • b x) y - deriv b y‖ ^ 2 ≤
      cuspProfileDerivativeMajorant b C L y := by
  have he := cuspProfile_cutoff_deriv_error_le hχ hb hχ0 hχ1
  have hsq : ‖deriv (fun x => χ x • b x) y - deriv b y‖ ^ 2 ≤
      2 * (‖deriv χ y‖ * ‖b y‖) ^ 2 + 2 * ‖deriv b y‖ ^ 2 := by
    have hh := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr he
    nlinarith [sq_nonneg (‖deriv χ y‖ * ‖b y‖ - ‖deriv b y‖)]
  by_cases hy2 : y ≤ 2
  · simp only [hy2, ↓reduceIte] at hderiv
    have hpoint := hbnd y ⟨hy.le, hy2⟩
    have hprod : ‖deriv χ y‖ * ‖b y‖ ≤ C * L := by
      calc
        _ ≤ (C / (y - 1)) * (L * (y - 1)) :=
          mul_le_mul hderiv hpoint (norm_nonneg _) (by positivity)
        _ = C * L := by field_simp [(sub_pos.mpr hy).ne']
    have hprod2 := (sq_le_sq₀ (by positivity) (mul_nonneg hC hL)).mpr hprod
    simp only [cuspProfileDerivativeMajorant, indicator_of_mem (show y ∈ Icc (1 : ℝ) 2 from ⟨hy.le, hy2⟩)]
    have hw : 0 ≤ 2 * C ^ 2 * (‖b y‖ ^ 2 / y ^ 2) := by positivity
    nlinarith
  · simp only [hy2, ↓reduceIte] at hderiv
    have hprod := mul_le_mul_of_nonneg_right hderiv (norm_nonneg (b y))
    have hprod2 := (sq_le_sq₀ (by positivity) (by positivity)).mpr hprod
    have heq : (C / y * ‖b y‖) ^ 2 = C ^ 2 * (‖b y‖ ^ 2 / y ^ 2) := by ring
    rw [heq] at hprod2
    simp only [cuspProfileDerivativeMajorant,
      indicator_of_notMem (show y ∉ Icc (1 : ℝ) 2 from fun h => hy2 h.2), add_zero]
    nlinarith

end GapFamily.Analytic
