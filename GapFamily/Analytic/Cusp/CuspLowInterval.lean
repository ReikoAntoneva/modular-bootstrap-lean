import GapFamily.Analytic.Foundation.IntervalTrace
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Ordinary weighted mass on a low cusp fiber

The true interval integrals use only values and derivative energy on [a,1],
with a ≥ 3/4. The constants are uniform over the actual curved lower edge of
the modular fundamental domain. No energy outside that fiber is counted.
-/

noncomputable section
namespace GapFamily.Analytic.IntervalTrace
open Set MeasureTheory

theorem integral_inverse_square {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    (∫ y in a..(1 : ℝ), 1 / y ^ 2) = 1 / a - 1 := by
  have hn (y : ℝ) (hy : y ∈ Icc a 1) : y ≠ 0 := ne_of_gt (ha.trans_le hy.1)
  have hc : ContinuousOn (fun y : ℝ => -y⁻¹) (Icc a 1) :=
    (continuousOn_id.inv₀ hn).neg
  have hd (y : ℝ) (hy : y ∈ Ioo a 1) :
      HasDerivAt (fun y : ℝ => -y⁻¹) (1 / y ^ 2) y := by
    convert! (hasDerivAt_inv (hn y ⟨hy.1.le, hy.2.le⟩)).neg using 1
    simp [one_div]
  have hi : IntervalIntegrable (fun y : ℝ => 1 / y ^ 2) volume a 1 :=
    (continuousOn_const.div (continuousOn_id.pow 2)
      (fun y hy => pow_ne_zero 2 (hn y hy))).intervalIntegrable_of_Icc ha1
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ha1 hc hd hi
  simpa only [inv_one, sub_neg_eq_add, one_div, sub_eq_add_neg, neg_neg, add_comm] using h

/-- A weighted low-fiber bound that never uses derivative energy outside [a,1]. -/
theorem low_weighted_mass_le {g g' : ℝ → ℂ} {a : ℝ}
    (ha : (3 / 4 : ℝ) ≤ a) (ha1 : a ≤ 1)
    (hg : ContinuousOn g (Icc a 1)) (hg' : ContinuousOn g' (Icc a 1))
    (hd : ∀ t ∈ Ioo a 1, HasDerivAt g (g' t) t) :
    (∫ y in a..(1 : ℝ), ‖g y‖ ^ 2 / y ^ 2) ≤
      (2 / 3 : ℝ) * ‖g 1‖ ^ 2 + (1 / 6 : ℝ) * (∫ y in a..1, ‖g' y‖ ^ 2) := by
  by_cases haeq : a = 1
  · subst a
    simp only [intervalIntegral.integral_same, mul_zero, add_zero]
    positivity
  have halt : a < 1 := lt_of_le_of_ne ha1 haeq
  have ha0 : 0 < a := by linarith
  let D : ℝ := ∫ t in a..1, ‖g' t‖
  let E : ℝ := ∫ t in a..1, ‖g' t‖ ^ 2
  have hD : 0 ≤ D := intervalIntegral.integral_nonneg ha1 (fun _ _ => norm_nonneg _)
  have hE : 0 ≤ E := intervalIntegral.integral_nonneg ha1 (fun _ _ => sq_nonneg _)
  have hcs : D ^ 2 ≤ (1 - a) * E := integral_sq_le_length_mul_integral_sq halt hg'.norm
  have hpoint (y : ℝ) (hy : y ∈ Icc a 1) :
      ‖g y‖ ^ 2 ≤ 2 * ‖g 1‖ ^ 2 + 2 * (1 - a) * E := by
    have hsub : Icc y 1 ⊆ Icc a 1 := Icc_subset_Icc hy.1 le_rfl
    have hdiff : ‖g y - g 1‖ ≤ D := by
      have hlocal := left_sub_le_integral (hg.mono hsub) (hg'.mono hsub)
        (fun t ht => hd t ⟨hy.1.trans_lt ht.1, ht.2⟩)
        (show (1 : ℝ) ∈ Icc y 1 from ⟨hy.2, le_rfl⟩)
      exact hlocal.trans (intervalIntegral.integral_mono_interval hy.1 hy.2 le_rfl
        (Filter.Eventually.of_forall fun _ => norm_nonneg _)
        (hg'.norm.intervalIntegrable_of_Icc ha1))
    have hn : ‖g y‖ ≤ ‖g 1‖ + D := by
      calc
        _ = ‖(g y - g 1) + g 1‖ := by rw [sub_add_cancel]
        _ ≤ ‖g y - g 1‖ + ‖g 1‖ := norm_add_le _ _
        _ ≤ _ := by linarith
    have hs := (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) hD)).mpr hn
    nlinarith [sq_nonneg (‖g 1‖ - D)]
  have hn (y : ℝ) (hy : y ∈ Icc a 1) : y ≠ 0 := ne_of_gt (ha0.trans_le hy.1)
  have hw : IntervalIntegrable (fun y : ℝ => 1 / y ^ 2) volume a 1 :=
    (continuousOn_const.div (continuousOn_id.pow 2)
      (fun y hy => pow_ne_zero 2 (hn y hy))).intervalIntegrable_of_Icc ha1
  have hm : IntervalIntegrable (fun y : ℝ => ‖g y‖ ^ 2 / y ^ 2) volume a 1 :=
    ((hg.norm.pow 2).div (continuousOn_id.pow 2)
      (fun y hy => pow_ne_zero 2 (hn y hy))).intervalIntegrable_of_Icc ha1
  have hbound := intervalIntegral.integral_mono_on ha1 hm
    (hw.const_mul (2 * ‖g 1‖ ^ 2 + 2 * (1 - a) * E))
    (fun y hy => by
      simpa only [mul_one_div] using
        div_le_div_of_nonneg_right (hpoint y hy) (sq_nonneg y))
  rw [intervalIntegral.integral_const_mul, integral_inverse_square ha0 ha1] at hbound
  have hw0 : 0 ≤ 1 / a - 1 := by
    have h := (one_le_div ha0).mpr ha1
    linarith
  have hwle : 1 / a - 1 ≤ (1 / 3 : ℝ) := by
    have h : 1 / a ≤ (4 / 3 : ℝ) := (div_le_iff₀ ha0).mpr (by linarith)
    linarith
  have hC : 0 ≤ 2 * ‖g 1‖ ^ 2 + 2 * (1 - a) * E := by positivity
  have hc := mul_le_mul_of_nonneg_left hwle hC
  have he := mul_le_mul_of_nonneg_right (show 1 - a ≤ (1 / 4 : ℝ) by linarith) hE
  change (∫ y in a..1, ‖g y‖ ^ 2 / y ^ 2) ≤ (2 / 3 : ℝ) * ‖g 1‖ ^ 2 + (1 / 6 : ℝ) * E
  nlinarith

end GapFamily.Analytic.IntervalTrace
