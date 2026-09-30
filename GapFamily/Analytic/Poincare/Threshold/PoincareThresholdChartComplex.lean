import GapFamily.Analytic.Poincare.Threshold.PoincareThresholdWeak
import GapFamily.Analytic.Poincare.Threshold.PoincareThresholdChartTest
import GapFamily.Analytic.Poincare.Threshold.PoincareThresholdSourceH1
import GapFamily.Analytic.Modular.Elliptic.ModularUpperEllipticH1
import GapFamily.Analytic.Elliptic.ChartComplexIntegrability

noncomputable section
namespace GapFamily.Analytic.PoincareThresholdChartComplex
open Set MeasureTheory UpperHalfPlane Homogenization ModularGradient
  PoincareCanonical PoincareThresholdWeak LaplacianCovariance
  PoincareThresholdChartTest PoincareThresholdSourceH1
  ChartComplexIntegrability
open scoped ContDiff

/-- Both chart pairings are ordinary integrable functions, and they satisfy the
literal second-test Poisson identity for the actual threshold seed and source. -/
theorem thresholdSeed_chart_second_test_data (J : ℤ) (z : ℂ) (S : Set (Fin 2 → ℝ))
    (φ : (Fin 2 → ℝ) → ℝ) (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ S) (hSH : ellipticChart z '' S ⊆ upperHalfPlaneSet) :
    Integrable (fun v => (euclideanCoordLaplacian φ v : ℂ) *
      thresholdSeed J (ofComplex (ellipticChart z v))) (volume.restrict S) ∧
    Integrable (fun v => (φ v : ℂ) * thresholdSource J (ellipticChart z v))
      (volume.restrict S) ∧
    -(∫ v in S, (euclideanCoordLaplacian φ v : ℂ) *
      thresholdSeed J (ofComplex (ellipticChart z v))) =
      ∫ v in S, (φ v : ℂ) * thresholdSource J (ellipticChart z v) := by
  let ψ : ℂ → ℂ := fun w => (ellipticChartTest z φ w : ℂ)
  have hψ : ContDiff ℝ ∞ ψ :=
    Complex.ofRealCLM.contDiff.comp (ellipticChartTest_contDiff z hφ)
  have hcψ : HasCompactSupport ψ :=
    (ellipticChartTest_hasCompactSupport z hcφ).comp_left Complex.ofReal_zero
  have hsψ : tsupport ψ ⊆ upperHalfPlaneSet :=
    (tsupport_comp_subset Complex.ofReal_zero (ellipticChartTest z φ)).trans
      (upperEllipticChartTest_tsupport z hsφ hSH)
  let a : ℂ → ℂ := fun w => star (ordinaryHyperbolicLaplacian ψ w) *
    thresholdSeed J (ofComplex w) / (w.im : ℂ)^2
  let b : ℂ → ℂ := fun w => star (ψ w) *
    thresholdSeed J (ofComplex w) / (w.im : ℂ)^2
  let c : ℂ → ℂ := fun w => star (ψ w) *
    complexPoincareSeries 0 J (5 / 2 : ℂ) (ofComplex w) / (w.im : ℂ)^2
  let r : ℂ → ℂ := fun w => (1 / 4 : ℂ) * b w +
    (2 * (Real.pi : ℂ) * (J : ℂ))^2 * c w
  have htriple := thresholdSeed_weak_equation_integrable ψ hψ hcψ hsψ J
  have ha : Integrable a := htriple.1
  have hb : Integrable b := htriple.2.1
  have hc : Integrable c := htriple.2.2
  have hr : Integrable r := (hb.const_mul _).add (hc.const_mul _)
  have hzero : ∀ v, v ∉ S → euclideanCoordLaplacian φ v = 0 := by
    intro v hv
    exact image_eq_zero_of_notMem_tsupport
      (fun ht => hv (hsφ (tsupport_euclideanCoordLaplacian_subset_tsupport φ ht)))
  have ha_chart : ∀ v, a (ellipticChart z v) =
      -((euclideanCoordLaplacian φ v : ℂ) *
        thresholdSeed J (ofComplex (ellipticChart z v))) := by
    intro v
    dsimp only [a, ψ]
    rw [ordinaryHyperbolicLaplacian, euclideanLaplacian_ellipticChartTest z hφ]
    by_cases hv : v ∈ S
    · have hy : (ellipticChart z v).im ≠ 0 :=
        ne_of_gt (hSH (mem_image_of_mem _ hv))
      have hyC : ((ellipticChart z v).im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy
      simp only [Complex.real_smul, Complex.ofReal_neg, Complex.ofReal_pow,
        Complex.star_def, map_mul, map_neg, map_pow, Complex.conj_ofReal]
      field_simp
    · simp only [hzero v hv, Complex.ofReal_zero, smul_zero, star_zero, zero_mul,
        zero_div, neg_zero]
  have hr_chart : ∀ v, r (ellipticChart z v) =
      (φ v : ℂ) * thresholdSource J (ellipticChart z v) := by
    intro v
    dsimp only [r, b, c, ψ]
    simp only [ellipticChartTest_apply, Complex.star_def, Complex.conj_ofReal]
    unfold thresholdSource shiftedThresholdSource
    ring
  have ha_support : ∀ v, v ∉ S → a (ellipticChart z v) = 0 := by
    intro v hv
    rw [ha_chart, hzero v hv]
    simp
  have hr_support : ∀ v, v ∉ S → r (ellipticChart z v) = 0 := by
    intro v hv
    rw [hr_chart, image_eq_zero_of_notMem_tsupport (fun ht => hv (hsφ ht))]
    simp
  have hia := integrable_comp_ellipticChart_restrict z S ha
  have hir := integrable_comp_ellipticChart_restrict z S hr
  have hFi : Integrable (fun v => (euclideanCoordLaplacian φ v : ℂ) *
      thresholdSeed J (ofComplex (ellipticChart z v))) (volume.restrict S) := by
    apply hia.neg.congr
    filter_upwards with v
    change -(a (ellipticChart z v)) = _
    rw [ha_chart, neg_neg]
  have hRi : Integrable (fun v => (φ v : ℂ) * thresholdSource J (ellipticChart z v))
      (volume.restrict S) := by
    simpa only [hr_chart] using hir
  refine ⟨hFi, hRi, ?_⟩
  have ea := integral_comp_ellipticChart_restrict_of_support z S a ha_support
  have er := integral_comp_ellipticChart_restrict_of_support z S r hr_support
  simp_rw [ha_chart] at ea
  rw [integral_neg] at ea
  simp_rw [hr_chart] at er
  rw [ea, er]
  change (∫ w, a w) = ∫ w, (1 / 4 : ℂ) * b w +
    (2 * (Real.pi : ℂ) * (J : ℂ))^2 * c w
  rw [integral_add (hb.const_mul _) (hc.const_mul _), integral_const_mul, integral_const_mul]
  exact thresholdSeed_weak_equation ψ hψ hcψ hsψ J

end GapFamily.Analytic.PoincareThresholdChartComplex
