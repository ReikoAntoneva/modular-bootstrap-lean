import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Local interval trace estimates

These estimates use an actual continuous derivative field on a nondegenerate
compact interval. No behavior outside that interval is prescribed. In
particular they apply to vertical restrictions of smooth functions on the
upper half-plane. All integrals are ordinary Lebesgue interval integrals.
-/

open Set MeasureTheory

namespace GapFamily.Analytic.IntervalTrace

/-- Integral Cauchy inequality with only local continuity. -/
theorem integral_sq_le_length_mul_integral_sq {g : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hg : ContinuousOn g (Icc a b)) :
    (∫ x in a..b, g x)^2 ≤ (b - a) * (∫ x in a..b, (g x)^2) := by
  let m : ℝ := ∫ x in a..b, g x
  let d : ℝ := b - a
  have hd : 0 < d := sub_pos.mpr hab
  have hgi : IntervalIntegrable g volume a b := hg.intervalIntegrable_of_Icc hab.le
  have hg2i : IntervalIntegrable (fun x => (g x)^2) volume a b :=
    (hg.pow 2).intervalIntegrable_of_Icc hab.le
  have hpoly : (fun x => (d * g x - m)^2) =
      (fun x => d^2 * (g x)^2 - (2 * d * m) * g x + m^2) := by
    funext x
    ring
  have hvariance : (∫ x in a..b, (d * g x - m)^2) =
      d * (d * (∫ x in a..b, (g x)^2) - m^2) := by
    rw [hpoly,
      intervalIntegral.integral_add
        ((hg2i.const_mul (d^2)).sub (hgi.const_mul (2 * d * m))) intervalIntegrable_const,
      intervalIntegral.integral_sub (hg2i.const_mul (d^2)) (hgi.const_mul (2 * d * m)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const]
    change d^2 * (∫ x in a..b, (g x)^2) - (2 * d * m) * m + d * m^2 =
      d * (d * (∫ x in a..b, (g x)^2) - m^2)
    ring
  have hnonneg : 0 ≤ ∫ x in a..b, (d * g x - m)^2 :=
    intervalIntegral.integral_nonneg_of_forall hab.le (fun _ => sq_nonneg _)
  rw [hvariance] at hnonneg
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hd).mp hnonneg)

/-- Every displacement from the left endpoint is bounded by the integral of
the continuous speed on the whole interval. -/
theorem left_sub_le_integral {g g' : ℝ → ℂ} {a b x : ℝ}
    (hg : ContinuousOn g (Icc a b)) (hg' : ContinuousOn g' (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt g (g' t) t) (hx : x ∈ Icc a b) :
    ‖g a - g x‖ ≤ ∫ t in a..b, ‖g' t‖ := by
  have hsub : Icc a x ⊆ Icc a b := Icc_subset_Icc le_rfl hx.2
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.1
    (hg.mono hsub) (fun t ht => hd t ⟨ht.1, ht.2.trans_le hx.2⟩)
    ((hg'.mono hsub).intervalIntegrable_of_Icc hx.1)
  rw [norm_sub_rev, ← hftc]
  exact (intervalIntegral.norm_integral_le_integral_norm hx.1).trans
    (intervalIntegral.integral_mono_interval le_rfl hx.1 hx.2
      (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      (hg'.norm.intervalIntegrable_of_Icc (hx.1.trans hx.2)))

/-- Squared endpoint-to-average error is at most length times derivative
energy. In particular the error tends to zero on shrinking intervals if the
derivative energy remains bounded. -/
theorem left_sub_mean_sq_le {g g' : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hg : ContinuousOn g (Icc a b)) (hg' : ContinuousOn g' (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt g (g' t) t) :
    ‖g a - (b - a)⁻¹ • (∫ t in a..b, g t)‖^2 ≤
      (b - a) * (∫ t in a..b, ‖g' t‖^2) := by
  let D : ℝ := ∫ t in a..b, ‖g' t‖
  have hD : 0 ≤ D := intervalIntegral.integral_nonneg hab.le (fun _ _ => norm_nonneg _)
  have hbound : ∀ t ∈ uIoc a b, ‖g a - g t‖ ≤ D := by
    intro t ht
    rw [uIoc_of_le hab.le] at ht
    exact left_sub_le_integral hg hg' hd ⟨ht.1.le, ht.2⟩
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [intervalIntegral.integral_sub intervalIntegrable_const (hg.intervalIntegrable_of_Icc hab.le),
    intervalIntegral.integral_const, abs_of_pos (sub_pos.mpr hab)] at h
  have heq : (b - a) • (g a - (b - a)⁻¹ • (∫ t in a..b, g t)) =
      (b - a) • g a - ∫ t in a..b, g t := by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ (sub_pos.mpr hab).ne', one_smul]
  rw [← heq, norm_smul, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hab)] at h
  have hmean : ‖g a - (b - a)⁻¹ • (∫ t in a..b, g t)‖ ≤ D :=
    (mul_le_mul_iff_right₀ (sub_pos.mpr hab)).mp (by simpa only [mul_comm] using h)
  exact ((sq_le_sq₀ (norm_nonneg _) hD).mpr hmean).trans
    (integral_sq_le_length_mul_integral_sq hab hg'.norm)

/-- A local complex interval trace estimate. All energy terms are finite by
the explicit continuity hypotheses. -/
theorem left_norm_sq_le {g g' : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hg : ContinuousOn g (Icc a b)) (hg' : ContinuousOn g' (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt g (g' t) t) :
    ‖g a‖^2 ≤ 2 / (b - a) * (∫ t in a..b, ‖g t‖^2) +
      2 * (b - a) * (∫ t in a..b, ‖g' t‖^2) := by
  let D : ℝ := ∫ t in a..b, ‖g' t‖
  have hD : 0 ≤ D := intervalIntegral.integral_nonneg hab.le (fun _ _ => norm_nonneg _)
  have hpoint : ∀ t ∈ Icc a b, ‖g a‖^2 ≤ 2 * ‖g t‖^2 + 2 * D^2 := by
    intro t ht
    have hdiff := left_sub_le_integral hg hg' hd ht
    have hn : ‖g a‖ ≤ ‖g t‖ + D := by
      calc
        ‖g a‖ = ‖(g a - g t) + g t‖ := by rw [sub_add_cancel]
        _ ≤ ‖g a - g t‖ + ‖g t‖ := norm_add_le _ _
        _ ≤ ‖g t‖ + D := by linarith
    have hs := (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) hD)).mpr hn
    nlinarith [sq_nonneg (‖g t‖ - D)]
  have hmono := intervalIntegral.integral_mono_on hab.le
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => ‖g a‖^2) volume a b)
    (((hg.norm.pow 2).intervalIntegrable_of_Icc hab.le).const_mul 2 |>.add
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => 2 * D^2) volume a b)) hpoint
  rw [intervalIntegral.integral_const,
    intervalIntegral.integral_add
      (((hg.norm.pow 2).intervalIntegrable_of_Icc hab.le).const_mul 2) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at hmono
  simp only [Pi.pow_apply, smul_eq_mul] at hmono
  have hcs := integral_sq_le_length_mul_integral_sq hab hg'.norm
  have henergy : (b - a) * ‖g a‖^2 ≤
      2 * (∫ t in a..b, ‖g t‖^2) +
        2 * (b - a)^2 * (∫ t in a..b, ‖g' t‖^2) := by
    have hmul := mul_le_mul_of_nonneg_left hcs (show 0 ≤ 2 * (b - a) by linarith)
    change D^2 ≤ _ at hcs
    change 2 * (b - a) * D^2 ≤ _ at hmul
    nlinarith
  apply (mul_le_mul_iff_right₀ (sub_pos.mpr hab)).mp
  calc
    (b - a) * ‖g a‖^2 ≤ 2 * (∫ t in a..b, ‖g t‖^2) +
        2 * (b - a)^2 * (∫ t in a..b, ‖g' t‖^2) := henergy
    _ = (b - a) * (2 / (b - a) * (∫ t in a..b, ‖g t‖^2) +
        2 * (b - a) * (∫ t in a..b, ‖g' t‖^2)) := by
      field_simp [(sub_pos.mpr hab).ne']

end GapFamily.Analytic.IntervalTrace
