import GapFamily.Construction.TailReserve
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Uniform reserve above a fixed tail threshold

The lower tail endpoint is independent of charge. The square-root gain at that
endpoint still dominates every fixed logarithmic loss as charge tends to infinity.
-/

open Set Filter
open scoped Topology
open GapFamily.Construction

namespace BTZEntropy.Construction

/-- At any fixed positive energy the tail logarithmic margin tends to infinity. -/
theorem tendsto_fixedTail_logMargin {T : ℝ} (hT : 0 < T) :
    Tendsto (fun a : ℝ => Real.sqrt (a * T) / 2 - 6 * Real.log (a + T))
      atTop atTop := by
  have hshift : Tendsto (fun a : ℝ => a + T) atTop atTop :=
    tendsto_atTop_add_const_right atTop T tendsto_id
  have hroot : Tendsto (fun a : ℝ => Real.sqrt (a + T)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hshift
  have hlog : Tendsto (fun a : ℝ => Real.log (a + T) / Real.sqrt (a + T))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (by norm_num : 0 < (1 / 2 : ℝ))).tendsto_div_nhds_zero.comp
        hshift
  have hcoeff : Tendsto (fun a : ℝ => Real.sqrt (T / 2) / 2 -
      6 * (Real.log (a + T) / Real.sqrt (a + T))) atTop
      (𝓝 (Real.sqrt (T / 2) / 2)) := by
    simpa using tendsto_const_nhds.sub (hlog.const_mul 6)
  have hlim := hcoeff.pos_mul_atTop (by positivity : 0 < Real.sqrt (T / 2) / 2) hroot
  refine tendsto_atTop_mono' _ ?_ hlim
  filter_upwards [eventually_ge_atTop T] with a ha
  have ha0 : 0 < a := hT.trans_le ha
  have hs : 0 < Real.sqrt (a + T) := Real.sqrt_pos.2 (add_pos ha0 hT)
  have hmul : Real.sqrt (T / 2) * Real.sqrt (a + T) ≤ Real.sqrt (a * T) := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ T / 2)]
    apply Real.sqrt_le_sqrt
    nlinarith [mul_nonneg hT.le (sub_nonneg.mpr ha)]
  have hcancel : (Real.sqrt (T / 2) / 2 -
      6 * (Real.log (a + T) / Real.sqrt (a + T))) * Real.sqrt (a + T) =
      Real.sqrt (T / 2) * Real.sqrt (a + T) / 2 - 6 * Real.log (a + T) := by
    field_simp [hs.ne']
  rw [hcancel]
  linarith

/-- One charge threshold bounds the logarithmic margin at every energy above a
fixed lower tail endpoint. -/
theorem eventually_fixedTail_log_margin_ge_uniform {T : ℝ} (hT : 10 ≤ T) (R : ℝ) :
    ∀ᶠ a : ℝ in atTop, ∀ L : ℝ, T ≤ L →
      R ≤ Real.sqrt (a * L) / 2 - 6 * Real.log (a + L) := by
  filter_upwards [(tendsto_fixedTail_logMargin (by linarith : 0 < T)).eventually_ge_atTop R,
    eventually_ge_atTop (13 : ℝ)] with a hR ha
  intro L hL
  exact hR.trans ((monotoneOn_tailLogMargin (by linarith)) hT (hT.trans hL) hL)

/-- The actual exponent difference retains the same fixed-threshold reserve. -/
theorem eventually_fixedTail_exponent_margin_ge_uniform {T : ℝ} (hT : 10 ≤ T) (R : ℝ) :
    ∀ᶠ a : ℝ in atTop, ∀ L : ℝ, T ≤ L →
      R ≤ 8 * Real.sqrt (a * L) - 7 * Real.sqrt (a * (L + 1)) -
        6 * Real.log (a + L) := by
  filter_upwards [eventually_fixedTail_log_margin_ge_uniform hT R,
    eventually_ge_atTop (0 : ℝ)] with a hR ha
  intro L hL
  exact (hR L hL).trans (sub_le_sub_right (tail_exponent_gap ha (hT.trans hL)) _)

/-- The tail exponent gain absorbs every fixed degree-six prefactor, uniformly
above a fixed energy threshold. -/
theorem eventually_fixedTail_exponential_dominates {T C : ℝ} (hT : 10 ≤ T) (hC : 0 < C) :
    ∀ᶠ a : ℝ in atTop, ∀ L : ℝ, T ≤ L →
      C * (a + L)^6 * Real.exp (7 * Real.sqrt (a * (L + 1))) ≤
        Real.exp (8 * Real.sqrt (a * L)) := by
  filter_upwards [eventually_fixedTail_exponent_margin_ge_uniform hT (Real.log C),
    eventually_gt_atTop (0 : ℝ)] with a hmargin ha
  intro L hL
  have hL0 : 0 < L := by linarith
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

/-- The positive tail reserve diverges uniformly above a fixed energy threshold. -/
theorem eventually_fixedTail_reserve_ge_uniform {T : ℝ} (hT : 10 ≤ T) (R : ℝ) :
    ∀ᶠ a : ℝ in atTop, ∀ L : ℝ, T ≤ L →
      R ≤ Real.exp (8 * Real.sqrt (a * L)) / ((L + 1) * (a + L)^12) := by
  let C : ℝ := max 1 R
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  filter_upwards [eventually_fixedTail_log_margin_ge_uniform hT (max 0 (Real.log C)),
    eventually_ge_atTop (1 : ℝ)] with a hmargin ha
  intro L hL
  have ha0 : 0 < a := by linarith
  have hL0 : 0 < L := by linarith
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

end BTZEntropy.Construction
