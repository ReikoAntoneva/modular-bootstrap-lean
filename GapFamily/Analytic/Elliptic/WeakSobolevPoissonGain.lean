import GapFamily.Analytic.Elliptic.WeakSobolevOrder
import GapFamily.Analytic.Elliptic.EllipticGradientBootstrap

/-! Actual finite-order interior Poisson regularity at the origin of a real chart. -/
noncomputable section
namespace GapFamily.Analytic.EllipticSobolev
open Set MeasureTheory Homogenization ModularElliptic EllipticGradientBootstrap
open scoped Topology ContDiff

/-- A fresh centered full cube gives a smaller neighborhood with an actual weak
Hessian while preserving the literal value, gradient, and Poisson equation. -/
theorem exists_local_weakHessian_zero {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpen U) (h0 : (0 : Vec d) ∈ U) (u : H1Function U)
    {f : Vec d → ℝ} (hP : WeakPoissonEquationOn U u f) (hf : MemL2On U f) :
    ∃ (W : Set (Vec d)) (_hW : IsOpen W), (0 : Vec d) ∈ W ∧ W ⊆ U ∧
      ∃ (uW : H1Function W) (_H : HasWeakHessianOn W uW),
        uW.toFun = u.toFun ∧ uW.grad = u.grad ∧ WeakPoissonEquationOn W uW f := by
  obtain ⟨Q, _hcenter, hQU, h0Q⟩ := exists_centered_cube_closed_subset hU h0
  have hOU : openCubeSet Q ⊆ U := by
    intro x hx
    apply hQU
    have hx' : x ∈ scaledOpenCubeSet Q 1 := by
      simpa only [scaledOpenCubeSet_eq_metricBall Q (by norm_num : (0 : ℝ) < 1),
        one_mul, ball_cubeCenter_eq_openCubeSet] using hx
    exact fun i => (hx' i).le
  let W := scaledOpenCubeSet Q (1 / 2)
  have hW : IsOpen W :=
    (scaledOpenCubeSet_isOpenBoundedConvexDomain Q (by norm_num : (0 : ℝ) < 1 / 2)).isOpen
  have hWO : W ⊆ openCubeSet Q := by
    rw [show W = Metric.ball (cubeCenter Q) ((1 / 2) * cubeRadius Q) from
      scaledOpenCubeSet_eq_metricBall Q (by norm_num), ← ball_cubeCenter_eq_openCubeSet]
    exact Metric.ball_subset_ball (by linarith [cubeRadius_pos Q])
  have hWU : W ⊆ U := hWO.trans hOU
  obtain ⟨uW, hvalue, hgrad, ⟨H⟩⟩ := halfCube_weakHessian Q
    (u.restrict (isOpen_openCubeSet Q) hOU) f
    (hP.restrict (isOpen_openCubeSet Q) hOU) (memL2On_mono hOU hf)
  have hv : uW.toFun = u.toFun := hvalue
  have hg : uW.grad = u.grad := hgrad
  refine ⟨W, hW, h0Q, hWU, uW, H, hv, hg, ?_⟩
  intro φ hφ hc hs
  change (∫ x in W, vecDot (uW.grad x) (euclideanGradient φ x)) = _
  rw [hg]
  exact (hP.restrict hW hWU) φ hφ hc hs

/-- An actual H1 weak Poisson solution gains two finite weak derivative orders
locally. Each step constructs new Hessians and differentiated weak equations;
no collection of higher-order derivative witnesses is assumed. -/
theorem weakSobolev_poisson_gain_zero {d n : ℕ} {U : Set (Vec d)}
    (hU : IsOpen U) (h0 : (0 : Vec d) ∈ U) (u : H1Function U)
    {f : Vec d → ℝ} (hP : WeakPoissonEquationOn U u f) (hf : weakSobolev n U f) :
    ∃ V : Set (Vec d), IsOpen V ∧ (0 : Vec d) ∈ V ∧ V ⊆ U ∧
      weakSobolev (n + 2) V u.toFun := by
  induction n generalizing U f with
  | zero =>
    obtain ⟨W, hW, h0W, hWU, uW, H, hv, _hg, _hPW⟩ :=
      exists_local_weakHessian_zero hU h0 u hP hf
    refine ⟨W, hW, h0W, hWU, uW, hv, ?_⟩
    intro i
    exact (weakSobolev_one W (fun x => uW.grad x i)).mpr ⟨gradientH1 H i, rfl⟩
  | succ n ih =>
    obtain ⟨g, hgf, hgorder⟩ := hf
    have hfL2 : MemL2On U f := hgf ▸ g.memL2
    obtain ⟨W, hW, h0W, hWU, uW, H, hv, _hg, hPW⟩ :=
      exists_local_weakHessian_zero hU h0 u hP hfL2
    let gW : H1Function W := g.restrict hW hWU
    have hPg : WeakPoissonEquationOn W uW gW := by
      change WeakPoissonEquationOn W uW g.toFun
      rw [hgf]
      exact hPW
    have hcoords : ∀ i : Fin d, ∃ V : Set (Vec d),
        IsOpen V ∧ (0 : Vec d) ∈ V ∧ V ⊆ W ∧
          weakSobolev (n + 2) V (fun x => uW.grad x i) := by
      intro i
      exact ih hW h0W (gradientH1 H i) (weakPoisson_gradient_h1 H gW hPg i)
        (weakSobolev_restrict (hgorder i) hW hWU)
    choose V hVo h0V hVW hVorder using hcoords
    let S : Set (Vec d) := W ∩ ⋂ i : Fin d, V i
    have hS : IsOpen S := hW.inter (isOpen_iInter_of_finite hVo)
    have h0S : (0 : Vec d) ∈ S := ⟨h0W, Set.mem_iInter.mpr h0V⟩
    have hSW : S ⊆ W := inter_subset_left
    have hSV (i : Fin d) : S ⊆ V i := by
      intro x hx
      exact Set.mem_iInter.mp hx.2 i
    refine ⟨S, hS, h0S, hSW.trans hWU, uW.restrict hS hSW, hv, ?_⟩
    intro i
    exact weakSobolev_restrict (hVorder i) hS (hSV i)

end GapFamily.Analytic.EllipticSobolev
