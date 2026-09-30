import GapFamily.Analytic.Modular.Elliptic.ModularEllipticCube

/-!
# A genuine differentiated weak Poisson equation

A weak Hessian bundles each actual gradient coordinate as an H1 function.
The derivative equation below is proved by ordinary compact-test identities;
no differentiated PDE or Hessian symmetry is assumed.
-/

noncomputable section
namespace GapFamily.Analytic.EllipticGradientBootstrap
open Set MeasureTheory Homogenization
open scoped ContDiff

variable {d : ℕ} {U : Set (Vec d)} {u : H1Function U}

/-- The i-th weak derivative with its actual Hessian row as weak gradient. -/
def gradientH1 (H : HasWeakHessianOn U u) (i : Fin d) : H1Function U where
  toFun := fun x => u.grad x i
  grad := fun x j => H.hess i j x
  memL2 := u.gradMemL2 i
  gradMemL2 := H.hess_memL2 i
  hasWeakGradient := H.weak_second i

/-- L2 fields have genuine ordinary pairings with continuous compact tests. -/
theorem integral_test_integrable {g : Vec d → ℝ} (hg : MemL2On U g)
    {φ : Vec d → ℝ} (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    IntegrableOn (fun x => g x * φ x) U := by
  simpa only [IntegrableOn, smul_eq_mul, mul_comm] using
    (hg.locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport hφ hc

/-- Weak Hessian coordinates are symmetric in every ordinary compact test pairing. -/
theorem integral_hessian_test_symm (H : HasWeakHessianOn U u) (i j : Fin d)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ U) :
    (∫ x in U, H.hess i j x * φ x) = ∫ x in U, H.hess j i x * φ x := by
  have hi := u.hasWeakGradient i (euclideanCoordDeriv j φ)
    (contDiff_euclideanCoordDeriv hφ j) (hasCompactSupport_euclideanCoordDeriv hc j)
    ((tsupport_euclideanCoordDeriv_subset_tsupport j φ).trans hs)
  have hj := u.hasWeakGradient j (euclideanCoordDeriv i φ)
    (contDiff_euclideanCoordDeriv hφ i) (hasCompactSupport_euclideanCoordDeriv hc i)
    ((tsupport_euclideanCoordDeriv_subset_tsupport i φ).trans hs)
  have hij := H.weak_second i j φ hφ hc hs
  have hji := H.weak_second j i φ hφ hc hs
  have hmix : (∫ x in U, u x * euclideanCoordSecondDeriv j i φ x) =
      ∫ x in U, u x * euclideanCoordSecondDeriv i j φ x := by
    congr 1
    funext x
    rw [euclideanCoordSecondDeriv_comm hφ j i x]
  change (∫ x in U, u x * euclideanCoordSecondDeriv j i φ x) = _ at hi
  change (∫ x in U, u x * euclideanCoordSecondDeriv i j φ x) = _ at hj
  change (∫ x in U, u.grad x i * euclideanCoordDeriv j φ x) = _ at hij
  change (∫ x in U, u.grad x j * euclideanCoordDeriv i φ x) = _ at hji
  linarith

/-- If -Delta u=f, the actual weak derivative of u solves -Delta(D_i u)=D_i f.
Only the original Poisson equation and the actual first weak derivative of f
are hypotheses. -/
theorem weakPoisson_gradient (H : HasWeakHessianOn U u)
    {f fi : Vec d → ℝ} (h : WeakPoissonEquationOn U u f)
    (i : Fin d) (hfi : HasWeakPartialDerivOn U i f fi) :
    WeakPoissonEquationOn U (gradientH1 H i) fi := by
  intro φ hφ hc hs
  have hDi := contDiff_euclideanCoordDeriv hφ i
  have hcDi := hasCompactSupport_euclideanCoordDeriv hc i
  have hsDi := (tsupport_euclideanCoordDeriv_subset_tsupport i φ).trans hs
  have hp := h (euclideanCoordDeriv i φ) hDi hcDi hsDi
  have hsrc := hfi φ hφ hc hs
  have hintH : ∀ j : Fin d, IntegrableOn
      (fun x => H.hess i j x * euclideanCoordDeriv j φ x) U := by
    intro j
    exact integral_test_integrable (H.hess_memL2 i j)
      (contDiff_euclideanCoordDeriv hφ j).continuous
      (hasCompactSupport_euclideanCoordDeriv hc j)
  have hintG : ∀ j : Fin d, IntegrableOn
      (fun x => u.grad x j * euclideanCoordSecondDeriv i j φ x) U := by
    intro j
    exact integral_test_integrable (u.gradMemL2 j)
      (contDiff_euclideanCoordSecondDeriv hφ i j).continuous
      (hasCompactSupport_euclideanCoordSecondDeriv hc i j)
  have hj : ∀ j : Fin d,
      (∫ x in U, H.hess i j x * euclideanCoordDeriv j φ x) =
        -(∫ x in U, u.grad x j * euclideanCoordSecondDeriv i j φ x) := by
    intro j
    rw [integral_hessian_test_symm H i j (contDiff_euclideanCoordDeriv hφ j)
      (hasCompactSupport_euclideanCoordDeriv hc j)
      ((tsupport_euclideanCoordDeriv_subset_tsupport j φ).trans hs)]
    have hw := H.weak_second j i (euclideanCoordDeriv j φ)
      (contDiff_euclideanCoordDeriv hφ j) (hasCompactSupport_euclideanCoordDeriv hc j)
      ((tsupport_euclideanCoordDeriv_subset_tsupport j φ).trans hs)
    change (∫ x in U, u.grad x j * euclideanCoordSecondDeriv j i φ x) = _ at hw
    rw [euclideanCoordSecondDeriv_comm_fun hφ j i] at hw
    linarith
  change (∫ x in U, ∑ j : Fin d, H.hess i j x * euclideanCoordDeriv j φ x) = _
  rw [integral_finsetSum _ (fun j _ => hintH j)]
  simp_rw [hj]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun j _ => hintG j)]
  change -(∫ x in U, vecDot (u.grad x)
    (euclideanGradient (euclideanCoordDeriv i φ) x)) = _
  rw [hp]
  change (∫ x in U, f x * euclideanCoordDeriv i φ x) = _ at hsrc
  linarith

/-- An H1 source provides the derivative hypothesis without extra assumptions. -/
theorem weakPoisson_gradient_h1 (H : HasWeakHessianOn U u) (f : H1Function U)
    (h : WeakPoissonEquationOn U u f) (i : Fin d) :
    WeakPoissonEquationOn U (gradientH1 H i) (fun x => f.grad x i) :=
  weakPoisson_gradient H h i (f.hasWeakGradient i)

/-- The existing interior estimate now supplies a genuine weak Hessian of each
actual gradient coordinate: one regularity gain beyond the input weak Hessian. -/
theorem halfCube_gradient_weakHessian (Q : TriadicCube d)
    (u f : H1Function (openCubeSet Q)) (H : HasWeakHessianOn (openCubeSet Q) u)
    (h : WeakPoissonEquationOn (openCubeSet Q) u f) (i : Fin d) :
    ∃ v : H1Function (scaledOpenCubeSet Q (1 / 2)),
      v.toFun = (fun x => u.grad x i) ∧
      v.grad = (fun x j => H.hess i j x) ∧
      Nonempty (HasWeakHessianOn (scaledOpenCubeSet Q (1 / 2)) v) := by
  exact ModularElliptic.halfCube_weakHessian Q (gradientH1 H i) (fun x => f.grad x i)
    (weakPoisson_gradient_h1 H f h i) (f.gradMemL2 i)

end GapFamily.Analytic.EllipticGradientBootstrap
