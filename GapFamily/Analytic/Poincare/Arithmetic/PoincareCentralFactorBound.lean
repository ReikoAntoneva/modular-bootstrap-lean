import GapFamily.Analytic.Poincare.Arithmetic.PoincareCentralFactor

noncomputable section
namespace GapFamily.Analytic.PoincareCentralFactor
open Set Filter BesselCoshOrder
open scoped Topology

/-- The literal Gamma--Bessel factor on the fixed Fourier argument collar. -/
def centralBesselOn (κ : ℂ) : C(Icc Real.pi (2 * Real.pi), ℂ) :=
  centralGammaFactor κ • besselKOn Real.pi (2 * Real.pi) κ

 theorem centralBesselOn_apply (κ : ℂ) (t : Icc Real.pi (2 * Real.pi)) :
    centralBesselOn κ t = centralGammaFactor κ * besselK κ t.val := by
  simp only [centralBesselOn, ContinuousMap.smul_apply, smul_eq_mul,
    besselKOn_apply Real.pi (2 * Real.pi) Real.pi_pos]

/-- This compact-argument family is genuinely norm-entire in the order parameter. -/
theorem centralBesselOn_analyticAt (κ : ℂ) : AnalyticAt ℂ centralBesselOn κ := by
  exact (centralGammaFactor_analyticAt κ).smul
    (besselKOn_analyticAt Real.pi (2 * Real.pi) Real.pi_pos κ)

/-- The actual compact Gamma--Bessel factor is uniformly bounded and nonzero on one
closed order disk. This is a local result obtained from its positive order-zero value. -/
theorem exists_centralBesselOn_closedBall_bounds :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 8 ∧ ∃ M : ℝ, 0 < M ∧
      ∀ κ : ℂ, ‖κ‖ ≤ δ → ∀ t ∈ Icc Real.pi (2 * Real.pi),
        centralGammaFactor κ * besselK κ t ≠ 0 ∧
        ‖centralGammaFactor κ * besselK κ t‖ ≤ M ∧
        ‖(centralGammaFactor κ * besselK κ t)⁻¹‖ ≤ M := by
  have hpi : 1 ≤ Real.pi := by linarith [Real.two_le_pi]
  have hb : 1 ≤ 2 * Real.pi := by linarith [Real.two_le_pi]
  let L : ℝ := besselK0 (2 * Real.pi)
  have hL : 0 < L := besselK0_pos hb
  have hc := (centralBesselOn_analyticAt (0 : ℂ)).continuousAt
  have hnear : ∀ᶠ κ in 𝓝 (0 : ℂ), ‖centralBesselOn κ - centralBesselOn 0‖ < L := by
    simpa only [Metric.mem_ball, dist_eq_norm] using
      hc.eventually (Metric.ball_mem_nhds (centralBesselOn 0) hL)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hnear
  let M : ℝ := ‖centralBesselOn 0‖ + L + L⁻¹ + 1
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨min (r / 2) (1 / 8), lt_min (half_pos hr) (by norm_num), min_le_right _ _, M, hM, ?_⟩
  intro κ hκ t ht
  have hkball : κ ∈ Metric.ball (0 : ℂ) r := by
    simpa only [Metric.mem_ball, dist_zero_right] using
      (hκ.trans (min_le_left _ _)).trans_lt (half_lt_self hr)
  have hsmall := hball κ hkball
  let tp : Icc Real.pi (2 * Real.pi) := ⟨t, ht⟩
  have hpoint : ‖centralBesselOn κ tp - centralBesselOn 0 tp‖ < L := by
    have h := (centralBesselOn κ - centralBesselOn 0).norm_coe_le_norm tp
    simpa only [ContinuousMap.sub_apply] using h.trans_lt hsmall
  have ht1 : 1 ≤ t := hpi.trans ht.1
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  have hz : ‖centralBesselOn 0 tp‖ = 2 * besselK0 t := by
    rw [centralBesselOn_apply, centralGammaFactor_zero, besselK_zero, norm_mul]
    norm_num
    change |besselK0 t| = besselK0 t
    exact abs_of_pos (besselK0_pos ht1)
  have hbase : L ≤ besselK0 t :=
    besselK0_antitoneOn_pos ht0 (show 0 < 2 * Real.pi by positivity) ht.2
  have hrev := norm_sub_norm_le (centralBesselOn 0 tp) (centralBesselOn κ tp)
  rw [norm_sub_rev, hz] at hrev
  have hlow : L ≤ ‖centralBesselOn κ tp‖ := by linarith
  have hnon : centralBesselOn κ tp ≠ 0 := norm_pos_iff.mp (hL.trans_le hlow)
  have hup : ‖centralBesselOn κ tp‖ ≤ M := by
    have htri := norm_sub_le (centralBesselOn κ tp - centralBesselOn 0 tp)
      (-centralBesselOn 0 tp)
    simp only [sub_neg_eq_add, sub_add_cancel, norm_neg] at htri
    have hev := (centralBesselOn 0).norm_coe_le_norm tp
    dsimp [M]
    have hi : 0 ≤ L⁻¹ := (inv_pos.mpr hL).le
    linarith
  have hinv : ‖(centralBesselOn κ tp)⁻¹‖ ≤ M := by
    rw [norm_inv]
    have hi := inv_anti₀ hL hlow
    dsimp [M]
    have hn := norm_nonneg (centralBesselOn 0)
    linarith
  simpa only [centralBesselOn_apply, tp] using And.intro hnon (And.intro hup hinv)

end GapFamily.Analytic.PoincareCentralFactor
