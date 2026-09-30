import GapFamily.Analytic.Elliptic.LocalSecondGreen
import GapFamily.Analytic.Poincare.PoincareLaplacianTest

/-! Ordinary compact-test Green identity for the negative hyperbolic Laplacian. -/
noncomputable section
namespace GapFamily.Analytic.PoincareGreen
open Set MeasureTheory UpperHalfPlane LaplacianCovariance PoincareWeak
open scoped ContDiff

/-- Both Euclidean Green pairings are ordinary convergent integrals. -/
theorem euclidean_green_test_integrable {U : Set ℂ} {f ψ : ℂ → ℂ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ U) :
    Integrable (fun z : ℂ => star (euclideanLaplacian ψ z) * f z) volume ∧
    Integrable (fun z : ℂ => star (ψ z) * euclideanLaplacian f z) volume := by
  have hx := local_star_secondDirectional_integrable hU hf hψ hc hs 1
  have hy := local_star_secondDirectional_integrable hU hf hψ hc hs Complex.I
  constructor
  · apply (hx.1.add hy.1).congr
    filter_upwards [] with z
    simp only [Pi.add_apply, euclideanLaplacian, secondDirectional, star_add, add_mul]
  · apply (hx.2.add hy.2).congr
    filter_upwards [] with z
    simp only [Pi.add_apply, euclideanLaplacian, secondDirectional, mul_add]

/-- The ordinary complex Euclidean Green identity, with only the test conjugated. -/
theorem integral_euclidean_green_test {U : Set ℂ} {f ψ : ℂ → ℂ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ U) :
    (∫ z : ℂ, star (euclideanLaplacian ψ z) * f z) =
      ∫ z : ℂ, star (ψ z) * euclideanLaplacian f z := by
  have hx := local_integral_star_secondDirectional_eq hU hf hψ hc hs 1
  have hy := local_integral_star_secondDirectional_eq hU hf hψ hc hs Complex.I
  have hix := local_star_secondDirectional_integrable hU hf hψ hc hs 1
  have hiy := local_star_secondDirectional_integrable hU hf hψ hc hs Complex.I
  change (∫ z : ℂ, star (secondDirectional ψ z 1 + secondDirectional ψ z Complex.I) * f z) =
    ∫ z : ℂ, star (ψ z) * (secondDirectional f z 1 + secondDirectional f z Complex.I)
  simp only [star_add, add_mul, mul_add]
  rw [integral_add hix.1 hiy.1, integral_add hix.2 hiy.2, hx, hy]

/-- The inverse-square height density cancels on the test support; outside it,
the test and its Laplacian vanish, including on the real axis. -/
theorem hyperbolic_green_left_density_eq (ψ f : ℂ → ℂ)
    (hs : tsupport ψ ⊆ upperHalfPlaneSet) (z : ℂ) :
    star (ordinaryHyperbolicLaplacian ψ z) * f z / (z.im : ℂ)^2 =
      -(star (euclideanLaplacian ψ z) * f z) := by
  by_cases hz : z ∈ tsupport ψ
  · have hy : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (hs hz))
    simp only [ordinaryHyperbolicLaplacian, Complex.real_smul, Complex.ofReal_neg,
      Complex.ofReal_pow, map_mul, map_neg, map_pow, Complex.star_def, Complex.conj_ofReal]
    field_simp
  · have hE : euclideanLaplacian ψ z = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hz (euclideanLaplacian_tsupport_subset ψ h))
    simp [ordinaryHyperbolicLaplacian, hE]

/-- The same exact cancellation for the Laplacian on the unrestricted field. -/
theorem hyperbolic_green_right_density_eq (ψ f : ℂ → ℂ)
    (hs : tsupport ψ ⊆ upperHalfPlaneSet) (z : ℂ) :
    star (ψ z) * ordinaryHyperbolicLaplacian f z / (z.im : ℂ)^2 =
      -(star (ψ z) * euclideanLaplacian f z) := by
  by_cases hz : z ∈ tsupport ψ
  · have hy : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (hs hz))
    simp only [ordinaryHyperbolicLaplacian, Complex.real_smul,
      Complex.ofReal_neg, Complex.ofReal_pow]
    field_simp
  · simp [image_eq_zero_of_notMem_tsupport hz]

/-- Both literal hyperbolic-density pairings are integrable for a compact upper test. -/
theorem hyperbolic_green_test_integrable (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ upperHalfPlaneSet)
    (f : ℂ → ℂ) (hf : ContDiffOn ℝ ∞ f upperHalfPlaneSet) :
    Integrable (fun z : ℂ => star (ordinaryHyperbolicLaplacian ψ z) * f z /
      (z.im : ℂ)^2) volume ∧
    Integrable (fun z : ℂ => star (ψ z) * ordinaryHyperbolicLaplacian f z /
      (z.im : ℂ)^2) volume := by
  have hi := euclidean_green_test_integrable isOpen_upperHalfPlaneSet hf hψ hc hs
  constructor
  · apply hi.1.neg.congr
    filter_upwards [] with z
    exact (hyperbolic_green_left_density_eq ψ f hs z).symm
  · apply hi.2.neg.congr
    filter_upwards [] with z
    exact (hyperbolic_green_right_density_eq ψ f hs z).symm

/-- Genuine compact-test Green identity for arbitrary complex fields smooth only
on the upper half-plane. No modularity or operator-domain hypothesis is used. -/
theorem integral_hyperbolic_green_test (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ upperHalfPlaneSet)
    (f : ℂ → ℂ) (hf : ContDiffOn ℝ ∞ f upperHalfPlaneSet) :
    (∫ z : ℂ, star (ordinaryHyperbolicLaplacian ψ z) * f z / (z.im : ℂ)^2) =
      ∫ z : ℂ, star (ψ z) * ordinaryHyperbolicLaplacian f z / (z.im : ℂ)^2 := by
  simp only [hyperbolic_green_left_density_eq ψ f hs,
    hyperbolic_green_right_density_eq ψ f hs, integral_neg]
  rw [integral_euclidean_green_test isOpen_upperHalfPlaneSet hf hψ hc hs]

end GapFamily.Analytic.PoincareGreen
