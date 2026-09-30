import GapFamily.Analytic.Spatial.SpatialPointKernelRecurrence
import GapFamily.Analytic.Elliptic.HyperbolicGreenTest
import GapFamily.Analytic.Spatial.SpatialTestMeasure

/-! Genuine compact-test recurrence for each literal spatial point kernel. -/
noncomputable section
namespace GapFamily.Analytic.SpatialPoint

open Set Filter MeasureTheory UpperHalfPlane LaplacianCovariance
open PoincareGreen PoincareWeak
open scoped ContDiff

theorem pointKernel_contDiffOn_upper (s : ℂ) (w : UpperHalfPlane) :
    ContDiffOn ℝ ∞ (fun z : ℂ => pointKernel s z w) upperHalfPlaneSet := by
  intro z hz
  exact (pointKernel_contDiffAt_left s hz w.im_pos).contDiffWithinAt

/-- A compact upper test supplies convergence for every exponent, independently of
the whole-plane convergence half-plane of the untested kernel. -/
theorem integrable_pointKernel_test_density (s : ℂ) (w : UpperHalfPlane)
    (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ upperHalfPlaneSet) :
    Integrable (fun z : ℂ => star (ψ z) * pointKernel s z w / (z.im : ℂ) ^ 2) := by
  have hstar : Continuous (fun z : ℂ => star (ψ z)) := hψ.continuous.star
  have hcstar : HasCompactSupport (fun z : ℂ => star (ψ z)) :=
    hc.comp_left (star_zero ℂ)
  have hsstar : tsupport (fun z : ℂ => star (ψ z)) ⊆ upperHalfPlaneSet :=
    (tsupport_comp_subset (star_zero ℂ) ψ).trans hs
  have hi := Dirichlet.local_mul_test_integrable (pointKernel_contDiffOn_upper s w).continuousOn
    (testDivideHeightSquare_continuous hstar hsstar)
    (testDivideHeightSquare_hasCompactSupport hcstar)
    ((testDivideHeightSquare_tsupport_subset (fun z : ℂ => star (ψ z))).trans hsstar)
  simpa only [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hi

theorem integrable_pointKernel_laplacian_test_density (s : ℂ) (w : UpperHalfPlane)
    (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ upperHalfPlaneSet) :
    Integrable (fun z : ℂ => star (ordinaryHyperbolicLaplacian ψ z) *
      pointKernel s z w / (z.im : ℂ) ^ 2) :=
  (hyperbolic_green_test_integrable ψ hψ hc hs (fun z : ℂ => pointKernel s z w)
    (pointKernel_contDiffOn_upper s w)).1

private theorem pointKernel_test_recurrence_density (s : ℂ) (w : UpperHalfPlane)
    (ψ : ℂ → ℂ) (hs : tsupport ψ ⊆ upperHalfPlaneSet) (z : ℂ) :
    star (ψ z) * ordinaryHyperbolicLaplacian (fun v : ℂ => pointKernel s v w) z /
        (z.im : ℂ) ^ 2 -
      s * (1 - s) * (star (ψ z) * pointKernel s z w / (z.im : ℂ) ^ 2) =
      s ^ 2 * (star (ψ z) * pointKernel (s + 1) z w / (z.im : ℂ) ^ 2) := by
  by_cases hz : 0 < z.im
  · have hrec := pointKernel_laplacian_recurrence s hz w.im_pos
    calc
      _ = (star (ψ z) / (z.im : ℂ) ^ 2) *
          (ordinaryHyperbolicLaplacian (fun v : ℂ => pointKernel s v w) z -
            s * (1 - s) * pointKernel s z w) := by ring
      _ = _ := by rw [hrec]; ring
  · have hzero : ψ z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (hs h))
    simp [hzero]

/-- The point recurrence tested against a compact upper function, in literal
Euclidean coordinates with the prescribed inverse-square height density. -/
theorem integral_pointKernel_weak_recurrence_density (s : ℂ) (w : UpperHalfPlane)
    (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ upperHalfPlaneSet) :
    (∫ z : ℂ, star (ordinaryHyperbolicLaplacian ψ z) * pointKernel s z w /
      (z.im : ℂ) ^ 2) -
      s * (1 - s) * (∫ z : ℂ, star (ψ z) * pointKernel s z w / (z.im : ℂ) ^ 2) =
      s ^ 2 * (∫ z : ℂ, star (ψ z) * pointKernel (s + 1) z w / (z.im : ℂ) ^ 2) := by
  rw [integral_hyperbolic_green_test ψ hψ hc hs (fun z : ℂ => pointKernel s z w)
    (pointKernel_contDiffOn_upper s w)]
  have hleft := (hyperbolic_green_test_integrable ψ hψ hc hs
    (fun z : ℂ => pointKernel s z w) (pointKernel_contDiffOn_upper s w)).2
  have hlow := integrable_pointKernel_test_density s w ψ hψ hc hs
  calc
    _ = ∫ z : ℂ,
        star (ψ z) * ordinaryHyperbolicLaplacian (fun v : ℂ => pointKernel s v w) z /
          (z.im : ℂ) ^ 2 -
        s * (1 - s) * (star (ψ z) * pointKernel s z w / (z.im : ℂ) ^ 2) := by
      rw [integral_sub hleft (hlow.const_mul _), integral_const_mul]
    _ = ∫ z : ℂ, s ^ 2 *
        (star (ψ z) * pointKernel (s + 1) z w / (z.im : ℂ) ^ 2) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (pointKernel_test_recurrence_density s w ψ hs)
    _ = _ := integral_const_mul _ _

private theorem pointKernel_test_zero_outside_upper (s : ℂ) (w : UpperHalfPlane)
    (ψ : ℂ → ℂ) (hs : tsupport ψ ⊆ upperHalfPlaneSet) :
    ∀ z ∉ upperHalfPlaneSet, star (ψ z) * pointKernel s z w = 0 := by
  intro z hz
  have hzero : ψ z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (hs h))
  simp [hzero]

private theorem pointKernel_laplacian_test_zero_outside_upper (s : ℂ) (w : UpperHalfPlane)
    (ψ : ℂ → ℂ) (hs : tsupport ψ ⊆ upperHalfPlaneSet) :
    ∀ z ∉ upperHalfPlaneSet,
      star (ordinaryHyperbolicLaplacian ψ z) * pointKernel s z w = 0 := by
  intro z hz
  have hzero : ordinaryHyperbolicLaplacian ψ z = 0 :=
    image_eq_zero_of_notMem_tsupport
      (fun h => hz (hs (ordinaryHyperbolicLaplacian_tsupport_subset ψ h)))
  simp [hzero]

theorem integrable_pointKernel_test (s : ℂ) (w : UpperHalfPlane)
    (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ upperHalfPlaneSet) :
    Integrable (fun z : UpperHalfPlane => star (ψ z) * pointKernel s z w) := by
  apply (integrable_upperHalfPlane_iff_complex_density
    (fun z : ℂ => star (ψ z) * pointKernel s z w)
    (pointKernel_test_zero_outside_upper s w ψ hs)).mpr
  exact integrable_pointKernel_test_density s w ψ hψ hc hs

theorem integrable_pointKernel_laplacian_test (s : ℂ) (w : UpperHalfPlane)
    (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ upperHalfPlaneSet) :
    Integrable (fun z : UpperHalfPlane =>
      star (ordinaryHyperbolicLaplacian ψ z) * pointKernel s z w) := by
  apply (integrable_upperHalfPlane_iff_complex_density
    (fun z : ℂ => star (ordinaryHyperbolicLaplacian ψ z) * pointKernel s z w)
    (pointKernel_laplacian_test_zero_outside_upper s w ψ hs)).mpr
  exact integrable_pointKernel_laplacian_test_density s w ψ hψ hc hs

/-- Every integral in the literal whole-H distribution recurrence genuinely converges. -/
theorem pointKernel_weak_integrable (s : ℂ) (w : UpperHalfPlane)
    (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ upperHalfPlaneSet) :
    Integrable (fun z : UpperHalfPlane =>
      star (ordinaryHyperbolicLaplacian ψ z) * pointKernel s z w) ∧
    Integrable (fun z : UpperHalfPlane => star (ψ z) * pointKernel s z w) ∧
    Integrable (fun z : UpperHalfPlane => star (ψ z) * pointKernel (s + 1) z w) :=
  ⟨integrable_pointKernel_laplacian_test s w ψ hψ hc hs,
    integrable_pointKernel_test s w ψ hψ hc hs,
    integrable_pointKernel_test (s + 1) w ψ hψ hc hs⟩

/-- The normalized point kernel satisfies its actual whole-hyperbolic-plane
compact-test recurrence at every complex exponent, with only the test conjugated. -/
theorem integral_pointKernel_weak_recurrence (s : ℂ) (w : UpperHalfPlane)
    (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ upperHalfPlaneSet) :
    (∫ z : UpperHalfPlane, star (ordinaryHyperbolicLaplacian ψ z) * pointKernel s z w) -
      s * (1 - s) * (∫ z : UpperHalfPlane, star (ψ z) * pointKernel s z w) =
      s ^ 2 * (∫ z : UpperHalfPlane, star (ψ z) * pointKernel (s + 1) z w) := by
  rw [integral_upperHalfPlane_eq_complex_density
    (fun z : ℂ => star (ordinaryHyperbolicLaplacian ψ z) * pointKernel s z w)
    (pointKernel_laplacian_test_zero_outside_upper s w ψ hs),
    integral_upperHalfPlane_eq_complex_density
      (fun z : ℂ => star (ψ z) * pointKernel s z w)
      (pointKernel_test_zero_outside_upper s w ψ hs),
    integral_upperHalfPlane_eq_complex_density
      (fun z : ℂ => star (ψ z) * pointKernel (s + 1) z w)
      (pointKernel_test_zero_outside_upper (s + 1) w ψ hs)]
  exact integral_pointKernel_weak_recurrence_density s w ψ hψ hc hs

end GapFamily.Analytic.SpatialPoint
