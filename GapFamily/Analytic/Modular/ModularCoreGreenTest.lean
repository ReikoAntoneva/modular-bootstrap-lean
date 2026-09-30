import GapFamily.Analytic.Elliptic.HyperbolicGreenTest
import GapFamily.Analytic.Modular.Periodization.ModularPeriodizationGradientEuclidean
import GapFamily.Analytic.Modular.Periodization.ModularPeriodizationValueEuclidean

noncomputable section
namespace GapFamily.Analytic.PoincareGreen
open Set MeasureTheory UpperHalfPlane ModularGradient LaplacianCovariance
open scoped ContDiff ComplexConjugate

/-- One local integration by parts retains the actual test-first energy pairing. -/
theorem local_integral_star_directional_mul_eq {U : Set ℂ} {f ψ : ℂ → ℂ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ U) (v : ℂ) :
    (∫ z : ℂ, star (fderiv ℝ ψ z v) * fderiv ℝ f z v) =
      -(∫ z : ℂ, star (secondDirectional ψ z v) * f z) := by
  let g : ℂ → ℂ := fun z => star (fderiv ℝ ψ z v)
  have hg : ContDiff ℝ ∞ g := contDiff_star (contDiff_directional hψ v)
  have hgc : HasCompactSupport g := (hc.fderiv_apply ℝ v).comp_left (star_zero ℂ)
  have hgs : tsupport g ⊆ U :=
    (tsupport_comp_subset (star_zero ℂ) _).trans ((tsupport_fderiv_apply_subset ℝ v).trans hs)
  have he := Dirichlet.local_integral_mul_fderiv_eq_neg hU
    (hf.of_le (by simp)) (hg.of_le (by simp)) hgc hgs v
  have hder (z : ℂ) : fderiv ℝ g z v = star (secondDirectional ψ z v) := by
    simp only [g, fderiv_star, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, starL'_apply, secondDirectional]
  simp only [hder, g] at he
  simpa only [mul_comm] using (neg_eq_iff_eq_neg.mpr he).symm

/-- The two first-order products against a compact test are genuinely integrable. -/
theorem local_star_directional_mul_integrable {U : Set ℂ} {f ψ : ℂ → ℂ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ U) (v : ℂ) :
    Integrable (fun z : ℂ => star (fderiv ℝ ψ z v) * fderiv ℝ f z v) volume := by
  have hi := Dirichlet.local_mul_test_integrable
    (contDiffOn_directional hU hf v).continuousOn
    (contDiff_star (contDiff_directional hψ v)).continuous
    ((hc.fderiv_apply ℝ v).comp_left (star_zero ℂ))
    ((tsupport_comp_subset (star_zero ℂ) _).trans
      ((tsupport_fderiv_apply_subset ℝ v).trans hs))
  simpa only [mul_comm] using hi

/-- The literal smooth-core energy against every compact upper test is the
ordinary test-Laplacian pairing, including across fundamental-domain seams. -/
theorem coreGradient_periodizedUpperCore_eq_hyperbolic_test
    (F : smoothCore) {ψ : ℂ → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ upperHalfPlaneSet) :
    inner ℂ (coreGradient (periodizedUpperCore ψ hψ hc hs)) (coreGradient F) =
      ∫ z : ℂ, star (ordinaryHyperbolicLaplacian ψ z) * F.val z / (z.im : ℂ)^2 := by
  have hx := local_integral_star_directional_mul_eq isOpen_upperHalfPlaneSet F.property.1 hψ hc hs 1
  have hy := local_integral_star_directional_mul_eq isOpen_upperHalfPlaneSet F.property.1 hψ hc hs Complex.I
  have hix := local_star_directional_mul_integrable isOpen_upperHalfPlaneSet F.property.1 hψ hc hs 1
  have hiy := local_star_directional_mul_integrable isOpen_upperHalfPlaneSet F.property.1 hψ hc hs Complex.I
  have hisx := (local_star_secondDirectional_integrable isOpen_upperHalfPlaneSet F.property.1 hψ hc hs 1).1
  have hisy := (local_star_secondDirectional_integrable isOpen_upperHalfPlaneSet F.property.1 hψ hc hs Complex.I).1
  calc
    _ = ∫ z : ℂ, star (fderiv ℝ ψ z 1) * fderiv ℝ F.val z 1 +
        star (fderiv ℝ ψ z Complex.I) * fderiv ℝ F.val z Complex.I := by
      calc
        _ = conj (inner ℂ (coreGradient F) (coreGradient (periodizedUpperCore ψ hψ hc hs))) :=
          (inner_conj_symm _ _).symm
        _ = _ := by
          rw [inner_coreGradient_periodizedUpperCore_eq_euclideanIntegral F hψ hc hs, ← integral_conj]
          apply integral_congr_ae
          filter_upwards [] with z
          simp only [map_add, map_mul, ← Complex.star_def, star_star, mul_comm]
    _ = -(∫ z : ℂ, star (secondDirectional ψ z 1) * F.val z) -
        (∫ z : ℂ, star (secondDirectional ψ z Complex.I) * F.val z) := by
      rw [integral_add hix hiy, hx, hy, sub_eq_add_neg]
    _ = ∫ z : ℂ, -(star (euclideanLaplacian ψ z) * F.val z) := by
      rw [integral_neg]
      change -(∫ z : ℂ, star (secondDirectional ψ z 1) * F.val z) -
          (∫ z : ℂ, star (secondDirectional ψ z Complex.I) * F.val z) =
        -(∫ z : ℂ, star (secondDirectional ψ z 1 + secondDirectional ψ z Complex.I) * F.val z)
      simp only [star_add, add_mul]
      rw [integral_add hisx hisy]
      ring
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with z
      exact (hyperbolic_green_left_density_eq ψ F.val hs z).symm

end GapFamily.Analytic.PoincareGreen
