import GapFamily.Analytic.Poincare.Arithmetic.PoincareCentralNumerator
import GapFamily.Analytic.Poincare.Arithmetic.PoincareCentralFactor

/-! Division-free height coherence on the actual connected continuation domain. -/
noncomputable section
namespace GapFamily.Analytic.PoincareCentralZeta
open Set Filter CuspFourierCutoff PoincareFourierContinuation
open PoincareCanonical PoincareCentralFactor
open scoped Topology

/-- The actual common-region numerator is the Bessel factor times the literal
Kloosterman Dirichlet series. No nonvanishing is used here. -/
theorem centralNumerator_eq_factor_mul_dirichlet (y : ℝ) (hy : 0 < y)
    (j J : ℤ) (hj : j ≠ 0) {κ : ℂ} (hκ : (1 / 2 : ℝ) < κ.re) :
    centralNumerator y hy j J κ = centralFourierFactor y j κ *
      kloostermanDirichlet j J (exponent κ) := by
  rw [centralNumerator_eq_dirichlet_common y hy j J hκ,
    centralFourierFactor_eq_integral hy hj (show 0 < κ.re by linarith)]
  rfl

/-- Cross multiplication identifies the actual numerators at two heights
throughout their common connected continuation region, even at factor zeros. -/
theorem centralNumerator_cross_eqOn (y v : ℝ) (hy : 0 < y) (hv : 0 < v)
    (j J : ℤ) (hj : j ≠ 0) :
    EqOn (fun κ => centralNumerator y hy j J κ * centralFourierFactor v j κ)
      (fun κ => centralNumerator v hv j J κ * centralFourierFactor y j κ)
      (continuationRegion (min (horizontalContinuation y hy).radius
        (horizontalContinuation v hv).radius)) := by
  have hay := (analyticOnNhd_centralNumerator y hy j J).mono
    (continuationRegion_mono (min_le_left (horizontalContinuation y hy).radius
      (horizontalContinuation v hv).radius))
  have hav := (analyticOnNhd_centralNumerator v hv j J).mono
    (continuationRegion_mono (min_le_right (horizontalContinuation y hy).radius
      (horizontalContinuation v hv).radius))
  have hdy : AnalyticOnNhd ℂ (centralFourierFactor y j)
      (continuationRegion (min (horizontalContinuation y hy).radius
        (horizontalContinuation v hv).radius)) := by
    intro κ _
    exact centralFourierFactor_analyticAt hy hj κ
  have hdv : AnalyticOnNhd ℂ (centralFourierFactor v j)
      (continuationRegion (min (horizontalContinuation y hy).radius
        (horizontalContinuation v hv).radius)) := by
    intro κ _
    exact centralFourierFactor_analyticAt hv hj κ
  apply eqOn_continuationRegion_of_common
    (lt_min (horizontalContinuation y hy).radius_pos (horizontalContinuation v hv).radius_pos)
    (hay.mul hdv) (hav.mul hdy)
  intro κ hκ
  rw [centralNumerator_eq_factor_mul_dirichlet y hy j J hj (by linarith),
    centralNumerator_eq_factor_mul_dirichlet v hv j J hj (by linarith)]
  ring

/-- The cross-product identity holds as an actual germ at the threshold. -/
theorem centralNumerator_cross_eventuallyEq (y v : ℝ) (hy : 0 < y) (hv : 0 < v)
    (j J : ℤ) (hj : j ≠ 0) :
    (fun κ => centralNumerator y hy j J κ * centralFourierFactor v j κ) =ᶠ[𝓝 (0 : ℂ)]
      (fun κ => centralNumerator v hv j J κ * centralFourierFactor y j κ) := by
  have hz : (0 : ℂ) ∈ continuationRegion (min (horizontalContinuation y hy).radius
      (horizontalContinuation v hv).radius) := by
    left
    simpa only [Metric.mem_ball, dist_self] using
      lt_min (horizontalContinuation y hy).radius_pos (horizontalContinuation v hv).radius_pos
  filter_upwards [(isOpen_continuationRegion _).mem_nhds hz] with κ hκ
  exact centralNumerator_cross_eqOn y v hy hv j J hj hκ

/-- In particular the actual threshold cross products agree. -/
theorem centralNumerator_cross_zero (y v : ℝ) (hy : 0 < y) (hv : 0 < v)
    (j J : ℤ) (hj : j ≠ 0) :
    centralNumerator y hy j J 0 * centralFourierFactor v j 0 =
      centralNumerator v hv j J 0 * centralFourierFactor y j 0 :=
  (centralNumerator_cross_eventuallyEq y v hy hv j J hj).eq_of_nhds

end GapFamily.Analytic.PoincareCentralZeta
