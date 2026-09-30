import GapFamily.Analytic.Poincare.Threshold.PoincareThresholdTest
import GapFamily.Analytic.Poincare.Continuation.PoincareShiftedContinuation
import GapFamily.Analytic.Poincare.Seed.PoincareSeriesWeakEquation

/-! The actual compact-test Poisson equation for the canonical full threshold seed. -/
noncomputable section
namespace GapFamily.Analytic.PoincareThresholdWeak
open Set MeasureTheory UpperHalfPlane PoincareCanonical PoincareWeak
  CuspFourierCutoff LaplacianCovariance
open scoped ContDiff

/-- Analytic continuation of the genuine ordinary test identity, including its
literal convergent shifted source, on the complete connected parameter region. -/
theorem continuation_weak_equation (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (D : Continuation K) (ψ : ℂ → ℂ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (hψK : tsupport ψ ⊆ K) (J : ℤ) :
    let T := hyperbolicCompactTest K ψ hψ.continuous hc (hψK.trans hKH) hψK
    let S := hyperbolicCompactTest K (ordinaryHyperbolicLaplacian ψ)
      (ordinaryHyperbolicLaplacian_continuous hψ)
      (ordinaryHyperbolicLaplacian_hasCompactSupport hc)
      ((ordinaryHyperbolicLaplacian_tsupport_subset ψ).trans (hψK.trans hKH))
      ((ordinaryHyperbolicLaplacian_tsupport_subset ψ).trans hψK)
    ∀ κ : ℂ, κ ∈ continuationRegion D.radius →
      S (D.family J κ) = exponent κ * (1 - exponent κ) * T (D.family J κ) +
        (2 * (Real.pi : ℂ) * (J : ℂ)) ^ 2 * T (shiftedFamily D J κ) := by
  let T := hyperbolicCompactTest K ψ hψ.continuous hc (hψK.trans hKH) hψK
  let S := hyperbolicCompactTest K (ordinaryHyperbolicLaplacian ψ)
    (ordinaryHyperbolicLaplacian_continuous hψ)
    (ordinaryHyperbolicLaplacian_hasCompactSupport hc)
    ((ordinaryHyperbolicLaplacian_tsupport_subset ψ).trans (hψK.trans hKH))
    ((ordinaryHyperbolicLaplacian_tsupport_subset ψ).trans hψK)
  change ∀ κ : ℂ, κ ∈ continuationRegion D.radius →
    S (D.family J κ) = exponent κ * (1 - exponent κ) * T (D.family J κ) +
      (2 * (Real.pi : ℂ) * (J : ℂ)) ^ 2 * T (shiftedFamily D J κ)
  have hS : AnalyticOnNhd ℂ (fun κ => S (D.family J κ)) (continuationRegion D.radius) :=
    fun κ hκ => (S.analyticAt _).comp (D.analytic_family J κ hκ)
  have hT : AnalyticOnNhd ℂ (fun κ => T (D.family J κ)) (continuationRegion D.radius) :=
    fun κ hκ => (T.analyticAt _).comp (D.analytic_family J κ hκ)
  have hshift : AnalyticOnNhd ℂ (fun κ => T (shiftedFamily D J κ))
      (continuationRegion D.radius) :=
    fun κ hκ => (T.analyticAt _).comp (analyticOnNhd_shiftedFamily D J κ hκ)
  have hright : AnalyticOnNhd ℂ (fun κ =>
      exponent κ * (1 - exponent κ) * T (D.family J κ) +
        (2 * (Real.pi : ℂ) * (J : ℂ)) ^ 2 * T (shiftedFamily D J κ))
      (continuationRegion D.radius) := by
    intro κ hκ
    have he : AnalyticAt ℂ exponent κ := analyticAt_const.add analyticAt_id
    exact ((he.mul (analyticAt_const.sub he)).mul (hT κ hκ)).add
      (analyticAt_const.mul (hshift κ hκ))
  have hid := eqOn_continuationRegion_of_common D.radius_pos hS hright
  apply hid
  intro κ hκ
  have hm : κ ∈ continuationRegion D.radius := by
    right
    refine ⟨by linarith, ?_⟩
    intro he
    rw [he] at hκ
    norm_num at hκ
  have hs : 1 < (exponent κ).re := by
    simp only [exponent, Complex.add_re]
    norm_num
    linarith
  have eS := hyperbolicCompactTest_apply K (ordinaryHyperbolicLaplacian ψ)
    (ordinaryHyperbolicLaplacian_continuous hψ)
    (ordinaryHyperbolicLaplacian_hasCompactSupport hc)
    ((ordinaryHyperbolicLaplacian_tsupport_subset ψ).trans (hψK.trans hKH))
    ((ordinaryHyperbolicLaplacian_tsupport_subset ψ).trans hψK)
    (D.family J κ) (fun z => complexPoincareSeries 0 J (exponent κ) (ofComplex z))
    (D.common_region J κ hκ)
  have eT := hyperbolicCompactTest_apply K ψ hψ.continuous hc (hψK.trans hKH) hψK
    (D.family J κ) (fun z => complexPoincareSeries 0 J (exponent κ) (ofComplex z))
    (D.common_region J κ hκ)
  have eShift := hyperbolicCompactTest_apply K ψ hψ.continuous hc (hψK.trans hKH) hψK
    (shiftedFamily D J κ)
    (fun z => complexPoincareSeries 0 J (exponent κ + 2) (ofComplex z))
    (shiftedFamily_apply D J hm)
  change S (D.family J κ) = _
  rw [eS, eT, eShift]
  exact integral_poincare_weak_equation ψ hψ hc (hψK.trans hKH) J hs

/-- Every term in the threshold weak equation is a genuinely integrable ordinary
function; the source is the original convergent Poincaré series at exponent 5/2. -/
theorem thresholdSeed_weak_equation_integrable (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) (hψH : tsupport ψ ⊆ upperHalfPlaneSet) (J : ℤ) :
    Integrable (fun z : ℂ => star (ordinaryHyperbolicLaplacian ψ z) *
      thresholdSeed J (ofComplex z) / (z.im : ℂ) ^ 2) ∧
    Integrable (fun z : ℂ => star (ψ z) *
      thresholdSeed J (ofComplex z) / (z.im : ℂ) ^ 2) ∧
    Integrable (fun z : ℂ => star (ψ z) *
      complexPoincareSeries 0 J (5 / 2 : ℂ) (ofComplex z) / (z.im : ℂ) ^ 2) := by
  let K := tsupport ψ
  let : CompactSpace K := isCompact_iff_compactSpace.mp hc
  let D := chosenContinuation K hψH
  refine ⟨?_, ?_, ?_⟩
  · exact hyperbolicCompactTest_integrable K (ordinaryHyperbolicLaplacian ψ)
      (ordinaryHyperbolicLaplacian_continuous hψ)
      (ordinaryHyperbolicLaplacian_hasCompactSupport hc)
      ((ordinaryHyperbolicLaplacian_tsupport_subset ψ).trans hψH)
      (ordinaryHyperbolicLaplacian_tsupport_subset ψ)
      (D.family J 0) (fun z => thresholdSeed J (ofComplex z))
      (thresholdSeed_ofComplex_eq_continuation hψH D J)
  · exact hyperbolicCompactTest_integrable K ψ hψ.continuous hc hψH Subset.rfl
      (D.family J 0) (fun z => thresholdSeed J (ofComplex z))
      (thresholdSeed_ofComplex_eq_continuation hψH D J)
  · exact integrable_hyperbolic_testSeries ψ hψ.continuous hc hψH J (by norm_num)

/-- The canonical global full threshold seed satisfies the actual hyperbolic
weak Poisson equation with its literal shifted Poincaré source. No weak equation
or spatial differentiability of the seed is assumed. -/
theorem thresholdSeed_weak_equation (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) (hψH : tsupport ψ ⊆ upperHalfPlaneSet) (J : ℤ) :
    (∫ z : ℂ, star (ordinaryHyperbolicLaplacian ψ z) *
      thresholdSeed J (ofComplex z) / (z.im : ℂ) ^ 2) =
      (1 / 4 : ℂ) * (∫ z : ℂ, star (ψ z) *
        thresholdSeed J (ofComplex z) / (z.im : ℂ) ^ 2) +
      (2 * (Real.pi : ℂ) * (J : ℂ)) ^ 2 * (∫ z : ℂ, star (ψ z) *
        complexPoincareSeries 0 J (5 / 2 : ℂ) (ofComplex z) / (z.im : ℂ) ^ 2) := by
  let K := tsupport ψ
  let : CompactSpace K := isCompact_iff_compactSpace.mp hc
  let D := chosenContinuation K hψH
  have hz : (0 : ℂ) ∈ continuationRegion D.radius := by
    left
    simpa only [Metric.mem_ball, dist_self] using D.radius_pos
  have h := continuation_weak_equation K hψH D ψ hψ hc Subset.rfl J 0 hz
  have eS := hyperbolicCompactTest_apply K (ordinaryHyperbolicLaplacian ψ)
    (ordinaryHyperbolicLaplacian_continuous hψ)
    (ordinaryHyperbolicLaplacian_hasCompactSupport hc)
    ((ordinaryHyperbolicLaplacian_tsupport_subset ψ).trans hψH)
    (ordinaryHyperbolicLaplacian_tsupport_subset ψ)
    (D.family J 0) (fun z => thresholdSeed J (ofComplex z))
    (thresholdSeed_ofComplex_eq_continuation hψH D J)
  have eT := hyperbolicCompactTest_apply K ψ hψ.continuous hc hψH Subset.rfl
    (D.family J 0) (fun z => thresholdSeed J (ofComplex z))
    (thresholdSeed_ofComplex_eq_continuation hψH D J)
  have eShift := hyperbolicCompactTest_apply K ψ hψ.continuous hc hψH Subset.rfl
    (shiftedFamily D J 0) (fun z => complexPoincareSeries 0 J (5 / 2 : ℂ) (ofComplex z))
    (shiftedFamily_zero_apply D J)
  rw [eS, eT, eShift] at h
  norm_num [exponent] at h
  exact h

end GapFamily.Analytic.PoincareThresholdWeak
