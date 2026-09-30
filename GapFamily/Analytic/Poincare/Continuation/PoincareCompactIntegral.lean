import GapFamily.Analytic.Poincare.Continuation.PoincareCompactMultiplier
import GapFamily.Analytic.Poincare.Continuation.PoincareCompactMajorant
import Mathlib.MeasureTheory.Constructions.Polish.Basic

noncomputable section
namespace GapFamily.Analytic.PoincareWeak
open Set MeasureTheory

/-- The literal ordinary compact-test integrand for a single actual quotient term. -/
def testTerm (ψ : ℂ → ℂ) (J : ℤ) (s : ℂ) (q : CuspCoset) (z : ℂ) : ℂ :=
  star (ψ z) * complexPoincareTerm 0 J s (UpperHalfPlane.ofComplex z) q

/-- The actual infinite series multiplied by the same test, in ordinary coordinates. -/
def testSeries (ψ : ℂ → ℂ) (J : ℤ) (s : ℂ) (z : ℂ) : ℂ :=
  star (ψ z) * complexPoincareSeries 0 J s (UpperHalfPlane.ofComplex z)

theorem summable_norm_testTerm (ψ : ℂ → ℂ) (J : ℤ) {s : ℂ}
    (hs : 1 < s.re) (z : ℂ) : Summable (fun q : CuspCoset => ‖testTerm ψ J s q z‖) := by
  simpa only [testTerm, norm_mul, norm_star] using
    (summable_norm_complexPoincareTerm 0 J hs (UpperHalfPlane.ofComplex z)).mul_left ‖ψ z‖

theorem testSeries_eq_tsum (ψ : ℂ → ℂ) (J : ℤ) (s : ℂ) (z : ℂ) :
    testSeries ψ J s z = ∑' q : CuspCoset, testTerm ψ J s q z := by
  simp only [testSeries, testTerm, complexPoincareSeries, tsum_mul_left]

/-- The whole nonnegative norm sum is an ordinary integrable function. -/
theorem integrable_norm_tsum_testTerm (ψ : ℂ → ℂ) (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ UpperHalfPlane.upperHalfPlaneSet)
    (J : ℤ) {s : ℂ} (hs : 1 < s.re) :
    Integrable (fun z : ℂ => ∑' q : CuspCoset, ‖testTerm ψ J s q z‖) := by
  let : Countable CuspCoset := cuspBottomRow_injective.countable
  obtain ⟨u, hu, hu0, hb⟩ := exists_test_term_majorant J hs ψ hc hψU
  have hi := (hψ.integrable_of_hasCompactSupport (μ := (volume : Measure ℂ)) hc).norm.mul_const (∑' q, u q)
  apply hi.mono'
    (Measurable.tsum (fun q =>
      (continuous_star_test_complexPoincareTerm ψ hψ hψU J s q).norm.measurable)).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg (fun _ => norm_nonneg _))]
  calc
    _ ≤ ∑' q : CuspCoset, ‖ψ z‖ * u q :=
      (summable_norm_testTerm ψ J hs z).tsum_le_tsum (fun q => hb q z) (hu.mul_left _)
    _ = ‖ψ z‖ * ∑' q : CuspCoset, u q := tsum_mul_left

/-- The integral of the single-term norms is itself summable over actual cusp cosets. -/
theorem summable_integral_norm_testTerm (ψ : ℂ → ℂ) (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ UpperHalfPlane.upperHalfPlaneSet)
    (J : ℤ) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun q : CuspCoset => ∫ z : ℂ, ‖testTerm ψ J s q z‖) := by
  obtain ⟨u, hu, hu0, hb⟩ := exists_test_term_majorant J hs ψ hc hψU
  apply (hu.mul_left (∫ z : ℂ, ‖ψ z‖)).of_nonneg_of_le
    (fun _ => integral_nonneg (fun _ => norm_nonneg _))
  intro q
  calc
    _ ≤ ∫ z : ℂ, ‖ψ z‖ * u q :=
      integral_mono (integrable_star_test_complexPoincareTerm ψ hψ hc hψU J s q).norm
        ((hψ.integrable_of_hasCompactSupport hc).norm.mul_const _)
        (fun z => hb q z)
    _ = (∫ z : ℂ, ‖ψ z‖) * u q := integral_mul_const _ _

/-- Compact testing of the actual Poincaré sum is genuinely integrable. -/
theorem integrable_testSeries (ψ : ℂ → ℂ) (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ UpperHalfPlane.upperHalfPlaneSet)
    (J : ℤ) {s : ℂ} (hs : 1 < s.re) : Integrable (testSeries ψ J s) := by
  let : Countable CuspCoset := cuspBottomRow_injective.countable
  have hm : Measurable (testSeries ψ J s) := by
    simp only [show testSeries ψ J s = fun z => ∑' q : CuspCoset, testTerm ψ J s q z from
      funext (testSeries_eq_tsum ψ J s)]
    exact Measurable.tsum (fun q =>
      (continuous_star_test_complexPoincareTerm ψ hψ hψU J s q).measurable)
  apply (integrable_norm_tsum_testTerm ψ hψ hc hψU J hs).mono' hm.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  rw [testSeries_eq_tsum]
  exact norm_tsum_le_tsum_norm (summable_norm_testTerm ψ J hs z)

/-- A true convergent sum of ordinary integrals, not an identity of totalized integrals. -/
theorem hasSum_integral_testTerm (ψ : ℂ → ℂ) (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ UpperHalfPlane.upperHalfPlaneSet)
    (J : ℤ) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun q : CuspCoset => ∫ z : ℂ, testTerm ψ J s q z)
      (∫ z : ℂ, testSeries ψ J s z) := by
  let : Countable CuspCoset := cuspBottomRow_injective.countable
  have h := hasSum_integral_of_summable_integral_norm
    (fun q => integrable_star_test_complexPoincareTerm ψ hψ hc hψU J s q)
    (summable_integral_norm_testTerm ψ hψ hc hψU J hs)
  change HasSum (fun q : CuspCoset => ∫ z : ℂ, testTerm ψ J s q z)
    (∫ z : ℂ, ∑' q : CuspCoset, testTerm ψ J s q z) at h
  simpa only [← testSeries_eq_tsum] using h

/-- The ordinary compact-test integral interchanges with the actual cusp-coset sum. -/
theorem integral_testSeries_eq_tsum (ψ : ℂ → ℂ) (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ UpperHalfPlane.upperHalfPlaneSet)
    (J : ℤ) {s : ℂ} (hs : 1 < s.re) :
    (∫ z : ℂ, testSeries ψ J s z) =
      ∑' q : CuspCoset, ∫ z : ℂ, testTerm ψ J s q z :=
  (hasSum_integral_testTerm ψ hψ hc hψU J hs).tsum_eq.symm

/-- The shifted series needed by the literal zero-energy residual has the same
ordinary integral interchange throughout its own convergence region. -/
theorem integral_shifted_testSeries_eq_tsum (ψ : ℂ → ℂ) (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ UpperHalfPlane.upperHalfPlaneSet)
    (J : ℤ) {s : ℂ} (hs : -1 < s.re) :
    (∫ z : ℂ, testSeries ψ J (s + 2) z) =
      ∑' q : CuspCoset, ∫ z : ℂ, testTerm ψ J (s + 2) q z := by
  apply integral_testSeries_eq_tsum ψ hψ hc hψU J
  norm_num [Complex.add_re]
  linarith

end GapFamily.Analytic.PoincareWeak
