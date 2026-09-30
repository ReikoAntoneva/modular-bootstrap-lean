import GapFamily.Analytic.Cusp.Schur.CuspLocalSchurCoherence

noncomputable section
namespace GapFamily.Analytic
open Set Filter
open scoped Topology

variable {E : Type*}

/-- Literal gluing along the complete overlap with an open physical region. -/
def analyticBallGlue (r : ℝ) (A B : ℂ → E) (κ : ℂ) : E :=
  if ‖κ‖ < r then A κ else B κ

theorem analyticBallGlue_eqOn_ball (r : ℝ) (A B : ℂ → E) :
    EqOn (analyticBallGlue r A B) A (Metric.ball 0 r) := by
  intro κ hκ
  simp only [Metric.mem_ball, dist_zero_right] at hκ
  exact ite_eq_left hκ

theorem analyticBallGlue_eqOn_of_eqOn (r : ℝ) (A B : ℂ → E) {U : Set ℂ}
    (hAB : EqOn A B (Metric.ball 0 r ∩ U)) :
    EqOn (analyticBallGlue r A B) B U := by
  intro κ hκ
  by_cases hn : ‖κ‖ < r
  · rw [analyticBallGlue, ite_eq_left hn]
    exact hAB ⟨by simpa only [Metric.mem_ball, dist_zero_right] using hn, hκ⟩
  · exact ite_eq_right hn

variable [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Genuine agreement on the overlap glues two norm-analytic families across
the boundary of the patch as well as at its center. -/
theorem analyticBallGlue_analyticOnNhd (r : ℝ) {A B : ℂ → E} {U : Set ℂ}
    (hU : IsOpen U) (hA : AnalyticOnNhd ℂ A (Metric.ball 0 r))
    (hB : AnalyticOnNhd ℂ B U) (hAB : EqOn A B (Metric.ball 0 r ∩ U)) :
    AnalyticOnNhd ℂ (analyticBallGlue r A B) (Metric.ball 0 r ∪ U) := by
  intro κ hκ
  rcases hκ with hκ | hκ
  · apply (hA κ hκ).congr
    filter_upwards [Metric.isOpen_ball.mem_nhds hκ] with z hz
    exact (analyticBallGlue_eqOn_ball r A B hz).symm
  · apply (hB κ hκ).congr
    filter_upwards [hU.mem_nhds hκ] with z hz
    exact (analyticBallGlue_eqOn_of_eqOn r A B hAB hz).symm

end GapFamily.Analytic
