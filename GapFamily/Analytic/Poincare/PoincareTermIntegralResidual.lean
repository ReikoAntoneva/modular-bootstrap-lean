import GapFamily.Analytic.Geometry.LaplacianSeedResidual
import GapFamily.Analytic.Poincare.Continuation.PoincareCompactLaplacianIntegral

noncomputable section
namespace GapFamily.Analytic.PoincareWeak
open Set MeasureTheory UpperHalfPlane LaplacianCovariance
open scoped ContDiff

/-- The literal quotient summand is smooth at every point of the upper plane. -/
theorem contDiffAt_complexPoincareTerm_zero (J : ℤ) (s : ℂ) (q : CuspCoset)
    (τ : UpperHalfPlane) :
    ContDiffAt ℝ ∞
      (fun z : ℂ => complexPoincareTerm 0 J s (UpperHalfPlane.ofComplex z) q) τ :=
  (contDiffAt_zeroEnergyRepresentative J s q τ).congr_of_eventuallyEq
    (zeroEnergyRepresentative_germ J s q τ).symm

/-- The actual summand has ordinary real derivatives of every order throughout H. -/
theorem contDiffOn_complexPoincareTerm_zero (J : ℤ) (s : ℂ) (q : CuspCoset) :
    ContDiffOn ℝ ∞
      (fun z : ℂ => complexPoincareTerm 0 J s (UpperHalfPlane.ofComplex z) q)
      upperHalfPlaneSet := by
  intro z hz
  exact (contDiffAt_complexPoincareTerm_zero J s q (⟨z, hz⟩ : UpperHalfPlane)).contDiffWithinAt

/-- A single actual term is integrable against the exact hyperbolic test density,
for every complex spectral parameter. -/
theorem integrable_hyperbolic_testTerm (ψ : ℂ → ℂ) (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ upperHalfPlaneSet)
    (J : ℤ) (s : ℂ) (q : CuspCoset) :
    Integrable (fun z : ℂ => star (ψ z) *
      complexPoincareTerm 0 J s (UpperHalfPlane.ofComplex z) q / (z.im : ℂ) ^ 2) := by
  have h := integrable_star_test_complexPoincareTerm (fun z => ψ z / (z.im : ℂ) ^ 2)
    (testDivideHeightSquare_continuous hψ hψU) (testDivideHeightSquare_hasCompactSupport hc)
    ((testDivideHeightSquare_tsupport_subset ψ).trans hψU) J s q
  simpa [div_mul_eq_mul_div] using h

/-- Compact testing extends the actual pointwise equation by zero off the test support. -/
theorem hyperbolic_testTerm_residual_pointwise (ψ : ℂ → ℂ)
    (hψU : tsupport ψ ⊆ upperHalfPlaneSet) (J : ℤ) (s : ℂ) (q : CuspCoset) (z : ℂ) :
    star (ψ z) * ordinaryHyperbolicLaplacian
      (fun w : ℂ => complexPoincareTerm 0 J s (UpperHalfPlane.ofComplex w) q) z /
        (z.im : ℂ) ^ 2 =
      s * (1 - s) * (star (ψ z) *
        complexPoincareTerm 0 J s (UpperHalfPlane.ofComplex z) q / (z.im : ℂ) ^ 2) +
      (2 * (Real.pi : ℂ) * (J : ℂ)) ^ 2 * (star (ψ z) *
        complexPoincareTerm 0 J (s + 2) (UpperHalfPlane.ofComplex z) q /
          (z.im : ℂ) ^ 2) := by
  by_cases hz : ψ z = 0
  · simp [hz]
  have hy : 0 < z.im := hψU (subset_tsupport ψ hz)
  have heq : ordinaryHyperbolicLaplacian
      (fun w : ℂ => complexPoincareTerm 0 J s (UpperHalfPlane.ofComplex w) q) z -
      s * (1 - s) * complexPoincareTerm 0 J s (UpperHalfPlane.ofComplex z) q =
      (2 * (Real.pi : ℂ) * (J : ℂ)) ^ 2 *
        complexPoincareTerm 0 J (s + 2) (UpperHalfPlane.ofComplex z) q := by
    simpa only [UpperHalfPlane.ofComplex_apply_of_im_pos hy] using
      ordinaryHyperbolicLaplacian_complexPoincareTerm_zero J s q (⟨z, hy⟩ : UpperHalfPlane)
  rw [sub_eq_iff_eq_add] at heq
  rw [heq]
  ring

/-- The Laplacian side is a genuine integrable function, by its exact residual decomposition. -/
theorem integrable_hyperbolic_testTerm_laplacian (ψ : ℂ → ℂ) (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ upperHalfPlaneSet)
    (J : ℤ) (s : ℂ) (q : CuspCoset) :
    Integrable (fun z : ℂ => star (ψ z) * ordinaryHyperbolicLaplacian
      (fun w : ℂ => complexPoincareTerm 0 J s (UpperHalfPlane.ofComplex w) q) z /
        (z.im : ℂ) ^ 2) := by
  have h0 := (integrable_hyperbolic_testTerm ψ hψ hc hψU J s q).const_mul (s * (1 - s))
  have h2 := (integrable_hyperbolic_testTerm ψ hψ hc hψU J (s + 2) q).const_mul
    ((2 * (Real.pi : ℂ) * (J : ℂ)) ^ 2)
  apply (h0.add h2).congr
  filter_upwards [] with z
  exact (hyperbolic_testTerm_residual_pointwise ψ hψU J s q z).symm

/-- Every individual actual quotient term obeys the residual identity in ordinary
convergent compact-test integrals, without a half-plane restriction on s. -/
theorem integral_hyperbolic_testTerm_residual (ψ : ℂ → ℂ) (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ upperHalfPlaneSet)
    (J : ℤ) (s : ℂ) (q : CuspCoset) :
    (∫ z : ℂ, star (ψ z) * ordinaryHyperbolicLaplacian
      (fun w : ℂ => complexPoincareTerm 0 J s (UpperHalfPlane.ofComplex w) q) z /
        (z.im : ℂ) ^ 2) =
      s * (1 - s) * (∫ z : ℂ, star (ψ z) *
        complexPoincareTerm 0 J s (UpperHalfPlane.ofComplex z) q / (z.im : ℂ) ^ 2) +
      (2 * (Real.pi : ℂ) * (J : ℂ)) ^ 2 * (∫ z : ℂ, star (ψ z) *
        complexPoincareTerm 0 J (s + 2) (UpperHalfPlane.ofComplex z) q /
          (z.im : ℂ) ^ 2) := by
  simp_rw [hyperbolic_testTerm_residual_pointwise ψ hψU J s q]
  rw [integral_add
    ((integrable_hyperbolic_testTerm ψ hψ hc hψU J s q).const_mul _)
    ((integrable_hyperbolic_testTerm ψ hψ hc hψU J (s + 2) q).const_mul _),
    integral_const_mul, integral_const_mul]

end GapFamily.Analytic.PoincareWeak
