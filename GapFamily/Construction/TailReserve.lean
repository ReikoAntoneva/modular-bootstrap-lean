import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Uniform exponent reserve for tail cells

These estimates supply the uniform scalar growth step in construction C8.
The exponent difference remains positive for unbounded energy, and the
polynomial loss is controlled uniformly above any fixed positive charge ray.
-/

open Set Filter
open scoped Topology

namespace GapFamily.Construction

/-- The default exponent difference dominates half the lower square root,
including charge zero. -/
theorem tail_exponent_gap {a L : ℝ} (ha : 0 ≤ a) (hL : 10 ≤ L) :
    Real.sqrt (a * L) / 2 ≤
      8 * Real.sqrt (a * L) - 7 * Real.sqrt (a * (L + 1)) := by
  have hL0 : 0 ≤ L := by linarith
  have hs : 14 * Real.sqrt (a * (L + 1)) ≤ 15 * Real.sqrt (a * L) := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    have h₁ := Real.sq_sqrt (mul_nonneg ha (show 0 ≤ L + 1 by linarith))
    have h₂ := Real.sq_sqrt (mul_nonneg ha hL0)
    have h₃ := mul_nonneg ha (show 0 ≤ 29 * L - 196 by linarith)
    nlinarith
  linarith

private theorem tailLogMargin_hasDerivAt {a L : ℝ} (ha : 0 < a) (hL : 0 < L) :
    HasDerivAt (fun L => Real.sqrt (a * L) / 2 - 6 * Real.log (a + L))
      (a / (2 * Real.sqrt (a * L)) / 2 - 6 * (1 / (a + L))) L := by
  convert (((hasDerivAt_id L).const_mul a).sqrt (by positivity)).div_const 2 |>.sub
    ((((hasDerivAt_id L).const_add a).log (by positivity)).const_mul 6) using 1 <;> first | rfl | simp

private theorem tailLogMargin_deriv_nonneg {a L : ℝ} (ha : 12 ≤ a) (hL : 0 < L) :
    0 ≤ a / (2 * Real.sqrt (a * L)) / 2 - 6 * (1 / (a + L)) := by
  have ha0 : 0 < a := by linarith
  have hsum : 0 < a + L := by positivity
  have hroot : 0 < Real.sqrt (a * L) := Real.sqrt_pos.2 (mul_pos ha0 hL)
  have hAM : 2 * Real.sqrt (a * L) ≤ a + L := by
    have hsq : Real.sqrt (a * L) ≤ (a + L) / 2 := by
      apply (Real.sqrt_le_iff).2
      constructor
      · positivity
      · nlinarith [sq_nonneg (a - L)]
    linarith
  have hnum : 24 * Real.sqrt (a * L) ≤ a * (a + L) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) (le_of_lt hsum)]
  apply sub_nonneg.mpr
  rw [div_div, ← mul_div_assoc, mul_one]
  apply (div_le_div_iff₀ hsum (by positivity : 0 < 2 * Real.sqrt (a * L) * 2)).2
  nlinarith

theorem monotoneOn_tailLogMargin_pos {a : ℝ} (ha : 12 ≤ a) :
    MonotoneOn (fun L => Real.sqrt (a * L) / 2 - 6 * Real.log (a + L)) (Ioi 0) := by
  have ha0 : 0 < a := by linarith
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioi 0)
  · intro L hL
    exact (tailLogMargin_hasDerivAt ha0 hL).continuousAt.continuousWithinAt
  · intro L hL
    exact (tailLogMargin_hasDerivAt ha0 (interior_subset hL)).hasDerivWithinAt
  · intro L hL
    exact tailLogMargin_deriv_nonneg ha (interior_subset hL)

theorem monotoneOn_tailLogMargin {a : ℝ} (ha : 12 < a) :
    MonotoneOn (fun L => Real.sqrt (a * L) / 2 - 6 * Real.log (a + L)) (Ici 10) :=
  (monotoneOn_tailLogMargin_pos ha.le).mono (by intro L hL; have : 10 ≤ L := hL; show 0 < L; linarith)


/-- Along every positive fixed ray, the square-root tail gain dominates the logarithmic loss. -/
theorem tendsto_tailLogMargin_ray {t : ℝ} (ht : 0 < t) :
    Tendsto (fun a : ℝ => Real.sqrt (a * (t * a)) / 2 -
      6 * Real.log (a + t * a)) atTop atTop := by
  have hscale : Tendsto (fun a : ℝ => (1 + t) * a) atTop atTop :=
    tendsto_id.const_mul_atTop (by linarith : 0 < 1 + t)
  have hlog : Tendsto (fun a : ℝ => Real.log ((1 + t) * a) / ((1 + t) * a))
      atTop (𝓝 0) := by
    simpa [Function.comp_def] using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hscale
  have hlog' : Tendsto (fun a : ℝ => Real.log (a + t * a) / a)
      atTop (𝓝 0) := by
    have h := hlog.mul_const (1 + t)
    simp only [zero_mul] at h
    convert h using 1
    ext a
    have ht' : 1 + t ≠ 0 := ne_of_gt (by linarith)
    rw [show a + t * a = (1 + t) * a by ring]
    by_cases ha : a = 0
    · simp [ha]
    · field_simp
  have hcoeff : Tendsto (fun a : ℝ => Real.sqrt t / 2 -
      6 * (Real.log (a + t * a) / a)) atTop (𝓝 (Real.sqrt t / 2)) := by
    simpa using tendsto_const_nhds.sub (hlog'.const_mul 6)
  have hlim := hcoeff.pos_mul_atTop (div_pos (Real.sqrt_pos.2 ht) (by norm_num))
    (tendsto_id : Tendsto (fun a : ℝ => a) atTop atTop)
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
  have hsqrt : Real.sqrt (a * (t * a)) = Real.sqrt t * a := by
    rw [show a * (t * a) = t * (a * a) by ring,
      Real.sqrt_mul ht.le, Real.sqrt_mul_self ha.le]
  simp only [id_eq]
  rw [hsqrt]
  field_simp


/-- One charge threshold bounds the logarithmic margin from below at every
energy above the positive fixed ray, with no upper energy restriction. -/
theorem eventually_tail_log_margin_ge_uniform {t : ℝ} (ht : 0 < t) (R : ℝ) :
    ∀ᶠ a : ℝ in atTop, ∀ L : ℝ, t * a ≤ L →
      R ≤ Real.sqrt (a * L) / 2 - 6 * Real.log (a + L) := by
  filter_upwards [(tendsto_tailLogMargin_ray ht).eventually_ge_atTop R,
    eventually_ge_atTop (13 : ℝ), eventually_ge_atTop (10 / t)] with a hR ha htL
  have hta : 10 ≤ t * a := by
    have hh := (div_le_iff₀ ht).mp htL
    simpa only [mul_comm] using hh
  intro L hL
  exact hR.trans ((monotoneOn_tailLogMargin (by linarith)) hta (hta.trans hL) hL)

/-- The actual exponent difference has the same uniform logarithmic reserve. -/
theorem eventually_tail_exponent_margin_ge_uniform {t : ℝ} (ht : 0 < t) (R : ℝ) :
    ∀ᶠ a : ℝ in atTop, ∀ L : ℝ, t * a ≤ L →
      R ≤ 8 * Real.sqrt (a * L) - 7 * Real.sqrt (a * (L + 1)) -
        6 * Real.log (a + L) := by
  filter_upwards [eventually_tail_log_margin_ge_uniform ht R,
    eventually_ge_atTop (0 : ℝ), eventually_ge_atTop (10 / t)] with a hR ha htL
  have hta : 10 ≤ t * a := by
    simpa only [mul_comm] using (div_le_iff₀ ht).mp htL
  intro L hL
  exact (hR L hL).trans (sub_le_sub_right (tail_exponent_gap ha (hta.trans hL)) _)

/-- Any fixed polynomial prefactor of degree six is eventually absorbed by
the actual tail exponent gain, uniformly over all larger energies. -/
theorem eventually_tail_exponential_dominates {t C : ℝ} (ht : 0 < t) (hC : 0 < C) :
    ∀ᶠ a : ℝ in atTop, ∀ L : ℝ, t * a ≤ L →
      C * (a + L)^6 * Real.exp (7 * Real.sqrt (a * (L + 1))) ≤
        Real.exp (8 * Real.sqrt (a * L)) := by
  filter_upwards [eventually_tail_exponent_margin_ge_uniform ht (Real.log C),
    eventually_gt_atTop (0 : ℝ)] with a hmargin ha
  intro L hL
  have hL0 : 0 < L := (mul_pos ht ha).trans_le hL
  have hsum : 0 < a + L := add_pos ha hL0
  have hbound : C * (a + L)^6 ≤
      Real.exp (8 * Real.sqrt (a * L) - 7 * Real.sqrt (a * (L + 1))) := by
    apply (Real.log_le_iff_le_exp (mul_pos hC (pow_pos hsum 6))).mp
    rw [Real.log_mul hC.ne' (pow_pos hsum 6).ne', Real.log_pow]
    norm_num
    linarith [hmargin L hL]
  calc
    C * (a + L)^6 * Real.exp (7 * Real.sqrt (a * (L + 1))) ≤
        Real.exp (8 * Real.sqrt (a * L) - 7 * Real.sqrt (a * (L + 1))) *
          Real.exp (7 * Real.sqrt (a * (L + 1))) :=
      mul_le_mul_of_nonneg_right hbound (Real.exp_pos _).le
    _ = Real.exp (8 * Real.sqrt (a * L)) := by
      rw [← Real.exp_add, sub_add_cancel]

/-- The positive tail reserve diverges uniformly over every unbounded ray.
Its denominator includes both the interval-length loss and the twelfth power
of the degree scale appearing in C8. -/
theorem eventually_tail_reserve_ge_uniform {t : ℝ} (ht : 0 < t) (R : ℝ) :
    ∀ᶠ a : ℝ in atTop, ∀ L : ℝ, t * a ≤ L →
      R ≤ Real.exp (8 * Real.sqrt (a * L)) / ((L + 1) * (a + L)^12) := by
  let C : ℝ := max 1 R
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  filter_upwards [eventually_tail_log_margin_ge_uniform ht (max 0 (Real.log C)),
    eventually_ge_atTop (1 : ℝ)] with a hmargin ha
  intro L hL
  have ha0 : 0 < a := by linarith
  have hL0 : 0 < L := (mul_pos ht ha0).trans_le hL
  have hsum : 0 < a + L := add_pos ha0 hL0
  have hden : 0 < (L + 1) * (a + L)^12 := by positivity
  have hlogL : Real.log (L + 1) ≤ Real.log (a + L) :=
    Real.log_le_log (by positivity) (by linarith)
  have hm := hmargin L hL
  have hm0 := (le_max_left 0 (Real.log C)).trans hm
  have hmC := (le_max_right 0 (Real.log C)).trans hm
  have hbound : C * ((L + 1) * (a + L)^12) ≤ Real.exp (8 * Real.sqrt (a * L)) := by
    apply (Real.log_le_iff_le_exp (mul_pos hC hden)).mp
    rw [Real.log_mul hC.ne' hden.ne',
      Real.log_mul (show L + 1 ≠ 0 by positivity) (pow_pos hsum 12).ne', Real.log_pow]
    norm_num
    nlinarith [Real.sqrt_nonneg (a * L)]
  exact (le_max_right 1 R).trans ((le_div_iff₀ hden).mpr hbound)

/-- The lower comparison for the degree assigned to the integer layer. -/
theorem tail_layer_degree_lower {K a L : ℝ} {m : ℕ} (hK : 0 ≤ K)
    (hL : L < (m : ℝ) + 1) :
    K * (a + L) ≤ K * (a + (m : ℝ) + 1) := by
  apply mul_le_mul_of_nonneg_left _ hK
  linarith

/-- The upper degree comparison, including the added constant coordinate. -/
theorem tail_layer_degree_upper {K a L : ℝ} {m : ℕ} (hK : 0 ≤ K)
    (ha : 1 ≤ a) (hm : (m : ℝ) ≤ L) :
    K * (a + (m : ℝ) + 1) + 1 ≤ 2 * (K + 1) * (a + L) := by
  have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
  have h₁ := mul_nonneg hK (sub_nonneg.mpr hm)
  have h₂ := mul_nonneg hK (show 0 ≤ a + L - 1 by linarith)
  nlinarith

end GapFamily.Construction
