import GapFamily.Analytic.Modular.Elliptic.ModularEllipticH1

noncomputable section
namespace GapFamily.Analytic.H1SecondTest

open Set MeasureTheory Homogenization
open scoped BigOperators

variable {d : ℕ} {S : Set (Vec d)}

/-- Compact continuous test multiplication is genuinely integrable for the actual
restricted-volume L² class. No finite-volume assumption on the domain is needed. -/
theorem integrable_mul_test {g φ : Vec d → ℝ}
    (hg : MemLp g 2 (volume.restrict S)) (hφ : Continuous φ)
    (hc : HasCompactSupport φ) :
    Integrable (fun x => g x * φ x) (volume.restrict S) := by
  simpa only [smul_eq_mul] using
    (hg.locallyIntegrable (by norm_num)).integrable_smul_right_of_hasCompactSupport hφ hc

theorem integrable_grad_coord_test (u : H1Function S) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) (i : Fin d) :
    Integrable (fun x => u.grad x i * euclideanCoordDeriv i φ x)
      (volume.restrict S) :=
  integrable_mul_test (u.gradMemL2 i) (contDiff_euclideanCoordDeriv hφ i).continuous
    (hasCompactSupport_euclideanCoordDeriv hc i)

theorem integrable_grad_test (u : H1Function S) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    Integrable (fun x => vecDot (u.grad x) (euclideanGradient φ x))
      (volume.restrict S) := by
  exact integrable_finsetSum Finset.univ fun i _ => integrable_grad_coord_test u hφ hc i

theorem integrable_second_test (u : H1Function S) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    Integrable (fun x => u x * euclideanCoordLaplacian φ x) (volume.restrict S) :=
  integrable_mul_test u.memL2 (contDiff_euclideanCoordLaplacian hφ).continuous
    (hasCompactSupport_euclideanCoordLaplacian hc)

/-- The weak first-derivative identities yield the ordinary second-test identity.
All finite-sum exchanges use the actual L² and compact-test integrability proofs. -/
theorem h1_integral_grad_test_eq_neg_integral_laplacian (u : H1Function S)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ S) :
    (∫ x in S, vecDot (u.grad x) (euclideanGradient φ x)) =
      -(∫ x in S, u x * euclideanCoordLaplacian φ x) := by
  have hsecond (i : Fin d) :
      Integrable (fun x => u x * euclideanCoordSecondDeriv i i φ x)
        (volume.restrict S) :=
    integrable_mul_test u.memL2 (contDiff_euclideanCoordSecondDeriv hφ i i).continuous
      (hasCompactSupport_euclideanCoordSecondDeriv hc i i)
  have hcoord (i : Fin d) :
      (∫ x in S, u.grad x i * euclideanCoordDeriv i φ x) =
        -(∫ x in S, u x * euclideanCoordSecondDeriv i i φ x) := by
    have h := u.hasWeakGradient i (euclideanCoordDeriv i φ)
      (contDiff_euclideanCoordDeriv hφ i) (hasCompactSupport_euclideanCoordDeriv hc i)
      ((tsupport_euclideanCoordDeriv_subset_tsupport i φ).trans hs)
    change (∫ x in S, u x * euclideanCoordSecondDeriv i i φ x) =
      -(∫ x in S, u.grad x i * euclideanCoordDeriv i φ x) at h
    linarith
  calc
    (∫ x in S, vecDot (u.grad x) (euclideanGradient φ x)) =
        ∑ i : Fin d, ∫ x in S, u.grad x i * euclideanCoordDeriv i φ x :=
      integral_finsetSum Finset.univ fun i _ => integrable_grad_coord_test u hφ hc i
    _ = ∑ i : Fin d, -(∫ x in S, u x * euclideanCoordSecondDeriv i i φ x) := by
      simp_rw [hcoord]
    _ = -(∫ x in S, ∑ i : Fin d, u x * euclideanCoordSecondDeriv i i φ x) := by
      rw [integral_finsetSum Finset.univ (fun i _ => hsecond i), Finset.sum_neg_distrib]
    _ = -(∫ x in S, u x * euclideanCoordLaplacian φ x) := by
      simp only [euclideanCoordLaplacian, Finset.mul_sum]

/-- A distributional second-test equation for an actual H¹ function is the
vendor's weak Poisson equation. The left and right integrands are integrable. -/
theorem weakPoissonEquationOn_of_second_test (u : H1Function S) {f : Vec d → ℝ}
    (hf : MemLp f 2 (volume.restrict S))
    (hsecond : ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ S → -(∫ x in S, u x * euclideanCoordLaplacian φ x) =
        ∫ x in S, f x * φ x) :
    WeakPoissonEquationOn S u f ∧
      ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        Integrable (fun x => vecDot (u.grad x) (euclideanGradient φ x)) (volume.restrict S) ∧
        Integrable (fun x => f x * φ x) (volume.restrict S) := by
  constructor
  · intro φ hφ hc hs
    exact (h1_integral_grad_test_eq_neg_integral_laplacian u hφ hc hs).trans
      (hsecond φ hφ hc hs)
  · intro φ hφ hc
    exact ⟨integrable_grad_test u hφ hc, integrable_mul_test hf hφ.continuous hc⟩

end GapFamily.Analytic.H1SecondTest
