import GapFamily.Analytic.Bessel.BesselCoshOrder

/-! Uniform nonvanishing of the actual complex-order cosh integral near order zero. -/
noncomputable section
namespace GapFamily.Analytic.BesselCoshOrder
open Set Filter MeasureTheory
open scoped Topology

/-- The ordinary order-zero Bessel integral decreases on positive arguments. -/
theorem besselK0_antitoneOn_pos : AntitoneOn besselK0 (Ioi 0) := by
  intro s hs t ht hst
  rw [besselK0_eq_coshIntegral, besselK0_eq_coshIntegral]
  apply integral_mono (besselK0_coshIntegrable ht) (besselK0_coshIntegrable hs)
  intro u
  exact Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right (neg_le_neg hst) (Real.cosh_pos u).le)

/-- On an argument interval above one, the actual compact family stays uniformly
away from zero on a closed disk of complex orders. -/
theorem exists_besselK_closedBall_lower_bound (a b : ℝ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ κ : ℂ, ‖κ‖ ≤ δ → ∀ t ∈ Icc a b,
      besselK0 b / 2 ≤ ‖besselK κ t‖ := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hb : 1 ≤ b := ha.trans hab
  have hL : 0 < besselK0 b := besselK0_pos hb
  have hc := (besselKOn_analyticAt a b ha0 (0 : ℂ)).continuousAt
  have hnear : ∀ᶠ κ in 𝓝 (0 : ℂ),
      ‖besselKOn a b κ - besselKOn a b 0‖ < besselK0 b / 2 := by
    simpa only [Metric.mem_ball, dist_eq_norm] using
      hc.eventually (Metric.ball_mem_nhds (besselKOn a b 0) (half_pos hL))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hnear
  refine ⟨r / 2, half_pos hr, ?_⟩
  intro κ hκ t ht
  have hκball : κ ∈ Metric.ball (0 : ℂ) r := by
    simpa only [Metric.mem_ball, dist_zero_right] using
      hκ.trans_lt (half_lt_self hr)
  have hsmall := hball κ hκball
  have hpoint : ‖besselK κ t - besselK 0 t‖ < besselK0 b / 2 := by
    have heval := (besselKOn a b κ - besselKOn a b 0).norm_coe_le_norm
      (⟨t, ht⟩ : Icc a b)
    simpa only [ContinuousMap.sub_apply, besselKOn_apply a b ha0] using
      heval.trans_lt hsmall
  have ht1 : 1 ≤ t := ha.trans ht.1
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  have hbase : besselK0 b ≤ besselK0 t :=
    besselK0_antitoneOn_pos ht0 (lt_of_lt_of_le zero_lt_one hb) ht.2
  have hzero : ‖besselK 0 t‖ = besselK0 t := by
    rw [besselK_zero, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (besselK0_pos ht1)]
  have hrev := norm_sub_norm_le (besselK 0 t) (besselK κ t)
  rw [norm_sub_rev, hzero] at hrev
  linarith

/-- The same closed order disk gives genuine pointwise nonvanishing and the
uniform reciprocal estimate with the original positive K0 normalization. -/
theorem exists_besselK_closedBall_nonzero_inv_bound (a b : ℝ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ κ : ℂ, ‖κ‖ ≤ δ → ∀ t ∈ Icc a b,
      besselK κ t ≠ 0 ∧ ‖(besselK κ t)⁻¹‖ ≤ 2 / besselK0 b := by
  obtain ⟨δ, hδ, hlower⟩ := exists_besselK_closedBall_lower_bound a b ha hab
  have hL : 0 < besselK0 b := besselK0_pos (ha.trans hab)
  refine ⟨δ, hδ, ?_⟩
  intro κ hκ t ht
  have hlow := hlower κ hκ t ht
  refine ⟨norm_pos_iff.mp ((half_pos hL).trans_le hlow), ?_⟩
  rw [norm_inv]
  calc
    ‖besselK κ t‖⁻¹ ≤ (besselK0 b / 2)⁻¹ := inv_anti₀ (half_pos hL) hlow
    _ = 2 / besselK0 b := by simp [div_eq_mul_inv]

end GapFamily.Analytic.BesselCoshOrder
