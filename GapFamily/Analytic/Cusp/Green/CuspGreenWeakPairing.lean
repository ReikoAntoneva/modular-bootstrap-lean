import GapFamily.Analytic.Cusp.Green.CuspGreenOperatorWeakHalfline
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Test-first weak pairing for the actual cusp Green response

The literal collar integral satisfies the half-line weak equation for every
`L²` source. Ordinary integrability is proved and the spectral coefficient
remains in the linear response slot.
-/

noncomputable section
namespace GapFamily.Analytic
open Set MeasureTheory

theorem cuspGreenCollarResponse_test_first_integrable (a T D : ℝ)
    (haT : a ≤ T) (hTD : T ≤ D) (κ : ℂ)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure a T))
    {ψ : ℝ → ℂ} (hψ : ContDiff ℝ 2 ψ) :
    IntervalIntegrable (fun t : ℝ =>
      inner ℂ (-deriv (deriv ψ) t) (cuspGreenCollarResponse a T κ f t) +
        κ ^ 2 * inner ℂ (ψ t) (cuspGreenCollarResponse a T κ f t)) volume a D ∧
      Integrable (fun u : CuspGreenCollar a T => inner ℂ (ψ u) (f u))
        (cuspGreenCollarMeasure a T) := by
  have hc : ContDiff ℝ 2 (fun t => star (ψ t)) :=
    Complex.conjCLE.contDiff.comp hψ
  have heq : (fun t : ℝ =>
      inner ℂ (-deriv (deriv ψ) t) (cuspGreenCollarResponse a T κ f t) +
        κ ^ 2 * inner ℂ (ψ t) (cuspGreenCollarResponse a T κ f t)) =
      (fun t => cuspGreenCollarResponse a T κ f t *
        (-deriv (deriv (fun t => star (ψ t))) t + κ ^ 2 * star (ψ t))) := by
    funext t
    simp only [deriv.star', RCLike.inner_apply, starRingEnd_apply, star_neg]
    ring
  refine ⟨?_, ?_⟩
  · rw [heq]
    exact cuspGreenCollarResponse_test_intervalIntegrable a T D haT hTD κ f hc
  · have h := cuspGreenCollar_sourceTest_integrable a T f
      ⟨fun u => star (ψ u), hψ.continuous.star.comp continuous_subtype_val⟩
    change Integrable (fun u : CuspGreenCollar a T => star (ψ u) * f u)
      (cuspGreenCollarMeasure a T) at h
    simpa only [RCLike.inner_apply', starRingEnd_apply] using h

/-- Actual test-first weak pairing, with the complex spectral coefficient in the
linear response slot and with no smoothness assumption on the collar source. -/
theorem cuspGreenCollarResponse_test_first_weakODE (a T D : ℝ)
    (haT : a ≤ T) (hTD : T ≤ D) (κ : ℂ)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure a T))
    {ψ : ℝ → ℂ} (hψ : ContDiff ℝ 2 ψ) (hs : tsupport ψ ⊆ Ioo a D) :
    (∫ t : ℝ in a..D,
      inner ℂ (-deriv (deriv ψ) t) (cuspGreenCollarResponse a T κ f t) +
        κ ^ 2 * inner ℂ (ψ t) (cuspGreenCollarResponse a T κ f t)) =
      ∫ u : CuspGreenCollar a T, inner ℂ (ψ u) (f u)
        ∂cuspGreenCollarMeasure a T := by
  have hc : ContDiff ℝ 2 (fun t => star (ψ t)) :=
    Complex.conjCLE.contDiff.comp hψ
  have hcs : tsupport (fun t => star (ψ t)) ⊆ Ioo a D :=
    (tsupport_comp_subset (g := star) (by simp) ψ).trans hs
  have h := cuspGreenCollarResponse_weak_halflineODE a T D haT hTD κ f hc hcs
  convert h using 1
  · apply intervalIntegral.integral_congr
    intro t _
    simp only [deriv.star', RCLike.inner_apply, starRingEnd_apply, star_neg]
    ring
  · apply integral_congr_ae
    filter_upwards with u
    simp only [RCLike.inner_apply, starRingEnd_apply]
    ring

/-- The actual half-line test-first equation, with both ordinary integrals certified. -/
theorem cuspGreenCollarResponse_test_first_halfline (a T : ℝ)
    (haT : a ≤ T) (κ : ℂ) (f : Lp ℂ 2 (cuspGreenCollarMeasure a T))
    {ψ : ℝ → ℂ} (hψ : ContDiff ℝ 2 ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ Ioi a) :
    IntegrableOn (fun t : ℝ =>
      inner ℂ (-deriv (deriv ψ) t) (cuspGreenCollarResponse a T κ f t) +
        κ ^ 2 * inner ℂ (ψ t) (cuspGreenCollarResponse a T κ f t)) (Ioi a) ∧
    Integrable (fun u : CuspGreenCollar a T => inner ℂ (ψ u) (f u))
      (cuspGreenCollarMeasure a T) ∧
    (∫ t : ℝ in Ioi a,
      inner ℂ (-deriv (deriv ψ) t) (cuspGreenCollarResponse a T κ f t) +
        κ ^ 2 * inner ℂ (ψ t) (cuspGreenCollarResponse a T κ f t)) =
      ∫ u : CuspGreenCollar a T, inner ℂ (ψ u) (f u)
        ∂cuspGreenCollarMeasure a T := by
  obtain ⟨B, hB⟩ := hc.isCompact.bddAbove
  let D : ℝ := max B T + 1
  have hTD : T ≤ D := by dsimp [D]; linarith [le_max_right B T]
  have hψD : tsupport ψ ⊆ Ioo a D := by
    intro t ht
    exact ⟨hs ht, by dsimp [D]; linarith [hB ht, le_max_left B T]⟩
  let F : ℝ → ℂ := fun t =>
    inner ℂ (-deriv (deriv ψ) t) (cuspGreenCollarResponse a T κ f t) +
      κ ^ 2 * inner ℂ (ψ t) (cuspGreenCollarResponse a T κ f t)
  have hFψ : Function.support F ⊆ tsupport ψ := by
    intro t ht
    by_contra hn
    have hzero := image_eq_zero_of_notMem_tsupport hn
    have hdzero : deriv (deriv ψ) t = 0 :=
      image_eq_zero_of_notMem_tsupport
        (fun h => hn ((tsupport_deriv_subset.trans tsupport_deriv_subset) h))
    exact ht (by simp [F, hzero, hdzero])
  have hFD : Function.support F ⊆ Ioc a D :=
    hFψ.trans (hψD.trans Ioo_subset_Ioc_self)
  have hi := cuspGreenCollarResponse_test_first_integrable a T D haT hTD κ f hψ
  have hFi : Integrable F :=
    (integrableOn_iff_integrable_of_support_subset hFD).mp
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le (haT.trans hTD)).mp hi.1)
  refine ⟨hFi.integrableOn, hi.2, ?_⟩
  have hhalf : (∫ t in Ioi a, F t) = ∫ t, F t :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun t ht => by
      by_contra hn
      exact ht (hs (hFψ hn)))
  change (∫ t in Ioi a, F t) = _
  rw [hhalf, ← intervalIntegral.integral_eq_integral_of_support_subset hFD]
  exact cuspGreenCollarResponse_test_first_weakODE a T D haT hTD κ f hψ hψD

end GapFamily.Analytic
