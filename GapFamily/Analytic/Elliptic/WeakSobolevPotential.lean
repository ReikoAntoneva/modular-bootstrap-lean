import GapFamily.Analytic.Elliptic.WeakSobolevMultiplier
import GapFamily.Analytic.Elliptic.WeakSobolevPoissonGain
import GapFamily.Analytic.Elliptic.WeakSobolevAE

/-! Actual construction of every finite local weak order from a smooth-potential equation. -/
noncomputable section
namespace GapFamily.Analytic.EllipticSobolev
open Set MeasureTheory Homogenization
open scoped ContDiff

/-- An actual weak H1 solution of -Delta u=a*u+g with smooth compact
coefficients has every finite weak derivative order on a neighborhood of zero.
Each finite order is built from the equation, not supplied as an infinite-jet premise. -/
theorem weakSobolev_potential_allOrders_zero {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpen U) (h0 : (0 : Vec d) ∈ U) (u : H1Function U)
    {a g : Vec d → ℝ} (ha : ContDiff ℝ ∞ a) (hac : HasCompactSupport a)
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hP : WeakPoissonEquationOn U u (fun x => a x * u x + g x)) (n : ℕ) :
    ∃ V : Set (Vec d), IsOpen V ∧ (0 : Vec d) ∈ V ∧ V ⊆ U ∧
      weakSobolev n V u.toFun := by
  induction n with
  | zero => exact ⟨U, hU, h0, Subset.rfl, u.memL2⟩
  | succ n ih =>
      obtain ⟨V, hV, h0V, hVU, horder⟩ := ih
      have hf : weakSobolev n V (fun x => a x * u x + g x) :=
        weakSobolev_smoothPotentialSource hV horder ha hac hg hgc
      obtain ⟨W, hW, h0W, hWV, hgain⟩ := weakSobolev_poisson_gain_zero hV h0V
        (u.restrict hV hVU) (hP.restrict hV hVU) hf
      refine ⟨W, hW, h0W, hWV.trans hVU, ?_⟩
      exact weakSobolev_succ_down hgain

/-- Every actual representative agreeing with the weak solution almost
everywhere inherits these constructed finite orders by honest weak-IBP transport. -/
theorem weakSobolev_potential_allOrders_zero_ae {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpen U) (h0 : (0 : Vec d) ∈ U) (u : H1Function U)
    {a g : Vec d → ℝ} (ha : ContDiff ℝ ∞ a) (hac : HasCompactSupport a)
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hP : WeakPoissonEquationOn U u (fun x => a x * u x + g x))
    (F : Vec d → ℝ) (hF : u.toFun =ᵐ[volume.restrict U] F) (n : ℕ) :
    ∃ V : Set (Vec d), IsOpen V ∧ (0 : Vec d) ∈ V ∧ V ⊆ U ∧
      weakSobolev n V F := by
  obtain ⟨V, hV, h0V, hVU, horder⟩ :=
    weakSobolev_potential_allOrders_zero hU h0 u ha hac hg hgc hP n
  exact ⟨V, hV, h0V, hVU,
    weakSobolev_congr_ae horder (ae_restrict_of_ae_restrict_of_subset hVU hF)⟩

end GapFamily.Analytic.EllipticSobolev
