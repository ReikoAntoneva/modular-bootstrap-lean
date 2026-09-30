import GapFamily.Analytic.Elliptic.WeakSobolevPotential
import GapFamily.Analytic.Elliptic.WeakSobolevClassical

/-! Classical smoothness from constructed local finite weak orders. -/
noncomputable section
namespace GapFamily.Analytic.EllipticSobolev
open Set MeasureTheory Homogenization
open scoped ContDiff

/-- Every finite order may use its own smaller neighborhood. Genuine weak
regularity and continuity of the actual representative imply classical smoothness. -/
theorem contDiffAt_infty_zero_of_local_weakSobolev
    {U : Set (Vec 2)} {F : Vec 2 → ℝ} (hFc : ContinuousOn F U)
    (horder : ∀ n : ℕ, ∃ V : Set (Vec 2), IsOpen V ∧ (0 : Vec 2) ∈ V ∧
      V ⊆ U ∧ weakSobolev n V F) : ContDiffAt ℝ ∞ F 0 := by
  apply contDiffAt_infty.mpr
  intro m
  obtain ⟨V, hV, h0V, hVU, hweak⟩ := horder (m + 2)
  exact contDiffAt_zero_of_continuousOn_weakSobolev m hV h0V (hFc.mono hVU) hweak

/-- The actual continuous representative of an H1 solution to a genuine
smooth compact potential equation is classically smooth at the chart center. -/
theorem contDiffAt_infty_zero_of_continuousOn_potential
    {U : Set (Vec 2)} (hU : IsOpen U) (h0 : (0 : Vec 2) ∈ U)
    (u : H1Function U) {a g : Vec 2 → ℝ}
    (ha : ContDiff ℝ ∞ a) (hac : HasCompactSupport a)
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hP : WeakPoissonEquationOn U u (fun x => a x * u x + g x))
    (F : Vec 2 → ℝ) (hF : u.toFun =ᵐ[volume.restrict U] F)
    (hFc : ContinuousOn F U) : ContDiffAt ℝ ∞ F 0 :=
  contDiffAt_infty_zero_of_local_weakSobolev hFc
    (weakSobolev_potential_allOrders_zero_ae hU h0 u ha hac hg hgc hP F hF)

end GapFamily.Analytic.EllipticSobolev
