import GapFamily.Analytic.Poincare.Threshold.PoincareThresholdSourceH1
import GapFamily.Analytic.Elliptic.H1SecondTest
import GapFamily.Analytic.Poincare.Threshold.PoincareThresholdChartComplex

/-! Actual threshold Poisson equation in ordinary affine chart coordinates. -/
noncomputable section
namespace GapFamily.Analytic.PoincareThresholdChartPoisson
open Set MeasureTheory UpperHalfPlane Homogenization
  PoincareCanonical PoincareThresholdSourceH1
  PoincareThresholdChartComplex
open scoped ContDiff

private theorem integral_real_pairing {S : Set (Fin 2 → ℝ)}
    (L : ℂ →L[ℝ] ℝ) (T : (Fin 2 → ℝ) → ℂ) (a : (Fin 2 → ℝ) → ℝ)
    (hi : Integrable (fun v => (a v : ℂ) * T v) (volume.restrict S)) :
    (∫ v in S, L (T v) * a v) = L (∫ v in S, (a v : ℂ) * T v) := by
  calc
    (∫ v in S, L (T v) * a v) = ∫ v in S, L ((a v : ℂ) * T v) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun v => by
        dsimp only
        rw [← Complex.real_smul, map_smul]
        simp only [smul_eq_mul, mul_comm]
    _ = L (∫ v in S, (a v : ℂ) * T v) := L.integral_comp_comm hi

private theorem real_second_test_of_complex {S : Set (Fin 2 → ℝ)}
    (L : ℂ →L[ℝ] ℝ) (T F : (Fin 2 → ℝ) → ℂ)
    (u f : H1Function S)
    (hu : (u : (Fin 2 → ℝ) → ℝ) =ᵐ[volume.restrict S] fun v => L (T v))
    (hf : (f : (Fin 2 → ℝ) → ℝ) =ᵐ[volume.restrict S] fun v => L (F v))
    (φ : (Fin 2 → ℝ) → ℝ)
    (hiT : Integrable (fun v => (euclideanCoordLaplacian φ v : ℂ) * T v)
      (volume.restrict S))
    (hiF : Integrable (fun v => (φ v : ℂ) * F v) (volume.restrict S))
    (heq : -(∫ v in S, (euclideanCoordLaplacian φ v : ℂ) * T v) =
      ∫ v in S, (φ v : ℂ) * F v) :
    -(∫ v in S, u v * euclideanCoordLaplacian φ v) = ∫ v in S, f v * φ v := by
  have huI : (∫ v in S, u v * euclideanCoordLaplacian φ v) =
      L (∫ v in S, (euclideanCoordLaplacian φ v : ℂ) * T v) := by
    rw [← integral_real_pairing L T _ hiT]
    exact integral_congr_ae (hu.mono fun v hv =>
      congrArg (fun r : ℝ => r * euclideanCoordLaplacian φ v) hv)
  have hfI : (∫ v in S, f v * φ v) = L (∫ v in S, (φ v : ℂ) * F v) := by
    rw [← integral_real_pairing L F _ hiF]
    exact integral_congr_ae (hf.mono fun v hv =>
      congrArg (fun r : ℝ => r * φ v) hv)
  rw [huI, hfI, ← map_neg, heq]

/-- The actual canonical threshold second-test equation becomes the vendor's
ordinary weak Poisson equation for every actual chart H1 representative. The
source is exactly the positive inverse-height forcing prescribed by that PDE. -/
theorem thresholdSeed_chart_weakPoisson (J : ℤ) (L : ℂ →L[ℝ] ℝ) (z : ℂ)
    (S : Set (Fin 2 → ℝ)) (hSH : ellipticChart z '' S ⊆ upperHalfPlaneSet)
    (u : H1Function S)
    (hu : u.toFun =ᵐ[volume.restrict S]
      fun v => L (thresholdSeed J (ofComplex (ellipticChart z v))))
    (f : H1Function S)
    (hf : f.toFun =ᵐ[volume.restrict S]
      fun v => L (thresholdSource J (ellipticChart z v))) :
    WeakPoissonEquationOn S u f := by
  intro φ hφ hc hs
  have hφ' : ContDiff ℝ ∞ φ := hφ
  obtain ⟨hiT, hiF, heq⟩ := thresholdSeed_chart_second_test_data J z S φ hφ' hc hs hSH
  rw [H1SecondTest.h1_integral_grad_test_eq_neg_integral_laplacian u hφ hc hs]
  exact real_second_test_of_complex L _ _ u f hu hf φ hiT hiF heq

/-- The weak equation uses genuine integrable gradient and source pairings. -/
theorem thresholdSeed_chart_weakPoisson_integrable
    {S : Set (Fin 2 → ℝ)} (u f : H1Function S) (φ : (Fin 2 → ℝ) → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    Integrable (fun v => vecDot (u.grad v) (euclideanGradient φ v)) (volume.restrict S) ∧
    Integrable (fun v => f v * φ v) (volume.restrict S) :=
  ⟨H1SecondTest.integrable_grad_test u hφ hc,
    H1SecondTest.integrable_mul_test f.memL2 hφ.continuous hc⟩

/-- On a relatively compact positive-height chart domain, the source H1
representative is constructed and its actual weak Poisson equation is proved. -/
theorem exists_thresholdSeed_chart_weakPoisson (J : ℤ) (L : ℂ →L[ℝ] ℝ)
    (z : ℂ) (S : Set (Fin 2 → ℝ)) (hS : IsOpen S)
    (hSc : IsCompact (closure S))
    (hSH : ellipticChart z '' closure S ⊆ upperHalfPlaneSet)
    (u : H1Function S)
    (hu : u.toFun =ᵐ[volume.restrict S]
      fun v => L (thresholdSeed J (ofComplex (ellipticChart z v)))) :
    ∃ f : H1Function S,
      (f.toFun =ᵐ[volume.restrict S]
        fun v => L (thresholdSource J (ellipticChart z v))) ∧
      WeakPoissonEquationOn S u f := by
  obtain ⟨f, hf⟩ := exists_thresholdSource_chartH1 J L z S hS hSc hSH u hu
  exact ⟨f, hf, thresholdSeed_chart_weakPoisson J L z S
    ((image_mono subset_closure).trans hSH) u hu f hf⟩

end GapFamily.Analytic.PoincareThresholdChartPoisson
