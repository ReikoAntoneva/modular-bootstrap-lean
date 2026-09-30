import GapFamily.Analytic.Poincare.Continuation.PoincareCompactCoherence

/-! The shifted actual compact Poincare family stays in the original convergence region. -/
noncomputable section
namespace GapFamily.Analytic.PoincareThresholdWeak
open Set UpperHalfPlane CuspFourierCutoff PoincareCanonical

variable {K : Set ℂ} [CompactSpace K]

/-- The actual compact continuation shifted by two in its spectral parameter. -/
def shiftedFamily (D : Continuation K) (J : ℤ) (κ : ℂ) : C(K, ℂ) :=
  D.family J (κ + 2)

/-- The shift lands strictly in the original common-series half-plane on the
whole continuation region, including its small disk across the imaginary axis. -/
theorem shifted_parameter_re (D : Continuation K) {κ : ℂ}
    (hκ : κ ∈ continuationRegion D.radius) : (3 / 2 : ℝ) < (κ + 2).re := by
  rcases hκ with hκ | hκ
  · have hn : ‖κ‖ < D.radius := by simpa only [Metric.mem_ball, dist_zero_right] using hκ
    have hr := D.radius_le_eighth
    have hlow : -‖κ‖ ≤ κ.re := (abs_le.mp (Complex.abs_re_le_norm κ)).1
    norm_num
    linarith
  · have hpos := hκ.1
    norm_num
    linarith

/-- In particular, the shifted parameter belongs to the analytic region of D. -/
theorem shifted_parameter_mem (D : Continuation K) {κ : ℂ}
    (hκ : κ ∈ continuationRegion D.radius) : κ + 2 ∈ continuationRegion D.radius := by
  have hr := shifted_parameter_re D hκ
  right
  refine ⟨by linarith, ?_⟩
  intro heq
  rw [heq] at hr
  norm_num at hr

/-- This is analyticity in the actual uniform norm on C(K), obtained by
composing the constructed analytic family with the affine parameter shift. -/
theorem analyticOnNhd_shiftedFamily (D : Continuation K) (J : ℤ) :
    AnalyticOnNhd ℂ (shiftedFamily D J) (continuationRegion D.radius) := by
  intro κ hκ
  exact (D.analytic_family J (κ + 2) (shifted_parameter_mem D hκ)).comp
    (f := fun ξ : ℂ => ξ + 2) (x := κ) (analyticAt_id.add analyticAt_const)

/-- Throughout the region, the shifted family equals the literal convergent
zero-energy Poincare series at exponent κ+1/2+2. -/
theorem shiftedFamily_apply (D : Continuation K) (J : ℤ) {κ : ℂ}
    (hκ : κ ∈ continuationRegion D.radius) (z : K) :
    shiftedFamily D J κ z =
      complexPoincareSeries 0 J (exponent κ + 2) (ofComplex z) := by
  simpa only [shiftedFamily, exponent, add_assoc] using
    D.common_region J (κ + 2) (shifted_parameter_re D hκ) z

/-- At the threshold the shifted source is the literal original series at 5/2. -/
theorem shiftedFamily_zero_apply (D : Continuation K) (J : ℤ) (z : K) :
    shiftedFamily D J 0 z = complexPoincareSeries 0 J (5 / 2 : ℂ) (ofComplex z) := by
  have hz : (0 : ℂ) ∈ continuationRegion D.radius := by
    left
    simpa only [Metric.mem_ball, dist_self] using D.radius_pos
  simpa only [exponent, add_zero, show (1 / 2 : ℂ) + 2 = 5 / 2 by norm_num] using
    shiftedFamily_apply D J hz z

end GapFamily.Analytic.PoincareThresholdWeak
