import GapFamily.Analytic.Poincare.Continuation.PoincareCompactEnergyAnalytic

/-! Entire complex-energy dependence of the actual compact energy correction. -/
noncomputable section
namespace GapFamily.Analytic.PoincareEnergyConvergentAnalytic
open Set MeasureTheory UpperHalfPlane
open scoped Topology

/-- At every exponent in the correction's genuine convergence range, the actual
C(K)-valued sum is norm analytic at every complex energy. -/
theorem compactEnergySeries_analyticAt_energy (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (J : ℤ) {s : ℂ} (hs : 0 < s.re) (E : ℂ) :
    AnalyticAt ℂ (fun F => compactEnergySeries K hKH F J s) E := by
  let B : ℝ := ‖E‖ + 1
  obtain ⟨u, hu, hu0, hbound⟩ := compactEnergyTerm_normal_on_strip K hKH hs hs B
  have hd : DifferentiableOn ℂ (fun F => compactEnergySeries K hKH F J s)
      (Metric.ball (0 : ℂ) B) := by
    apply Complex.differentiableOn_tsum_of_summable_norm (hu.mul_left B)
    · intro q F _
      exact (compactEnergyTerm_analyticAt_energy K hKH J s q F).differentiableAt.differentiableWithinAt
    · exact Metric.isOpen_ball
    · intro q F hF
      have hn : ‖F‖ < B := by simpa only [Metric.mem_ball, dist_zero_right] using hF
      exact (hbound F hn.le J q s le_rfl le_rfl).trans
        (mul_le_mul_of_nonneg_right hn.le (hu0 q))
  exact hd.analyticAt (Metric.isOpen_ball.mem_nhds
    (show E ∈ Metric.ball (0 : ℂ) B by simp [B]))

/-- Entire differentiability holds in the actual compact supremum norm. -/
theorem compactEnergySeries_differentiable_energy (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (J : ℤ) {s : ℂ} (hs : 0 < s.re) :
    Differentiable ℂ (fun E => compactEnergySeries K hKH E J s) :=
  fun E => (compactEnergySeries_analyticAt_energy K hKH J hs E).differentiableAt

/-- The actual entire energy family is norm continuous. -/
theorem compactEnergySeries_continuous_energy (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (J : ℤ) {s : ℂ} (hs : 0 < s.re) :
    Continuous (fun E : ℂ => compactEnergySeries K hKH E J s) :=
  (compactEnergySeries_differentiable_energy K hKH J hs).continuous

/-- Restriction to real input energy is continuous in C(K), with its literal cast. -/
theorem compactEnergySeries_continuous_realEnergy (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (J : ℤ) {s : ℂ} (hs : 0 < s.re) :
    Continuous (fun E : ℝ => compactEnergySeries K hKH (E : ℂ) J s) :=
  (compactEnergySeries_continuous_energy K hKH J hs).comp Complex.continuous_ofReal

/-- The actual real-energy C(K) family is strongly measurable for ordinary
Bochner integration against any Borel measure on the real line. -/
theorem compactEnergySeries_stronglyMeasurable_realEnergy (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (J : ℤ) {s : ℂ} (hs : 0 < s.re) :
    StronglyMeasurable (fun E : ℝ => compactEnergySeries K hKH (E : ℂ) J s) :=
  (compactEnergySeries_continuous_realEnergy K hKH J hs).stronglyMeasurable

end GapFamily.Analytic.PoincareEnergyConvergentAnalytic
