import GapFamily.Analytic.Poincare.Continuation.PoincareFiniteSuperposition
import GapFamily.Analytic.Poincare.Continuation.PoincareCompactEnergyEntire
import GapFamily.Analytic.Foundation.SignedAnalyticIntegral
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! Norm analytic ordinary signed input superposition on compact observations. -/
noncomputable section
namespace GapFamily.Analytic.PoincareEnergyContinuation
open Set Filter MeasureTheory UpperHalfPlane CuspFourierCutoff PoincareCanonical
open PoincareEnergyConvergentAnalytic DominatedAnalytic
open scoped Topology

/-- The actual compact family is norm continuous in real energy whenever
the convergent correction has positive real exponent. -/
theorem continuous_continuedSeedOn_realEnergy (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (J : ℤ) {κ : ℂ} (hκ : (-1 / 2 : ℝ) < κ.re) :
    Continuous (fun E : ℝ => continuedSeedOn K hKH E J κ) := by
  have hs : 0 < (exponent κ).re := by norm_num [exponent, Complex.add_re]; linarith
  exact continuous_const.add (compactEnergySeries_continuous_realEnergy K hKH J hs)

/-- The compact-valued ordinary signed integral of the actual continued family. -/
def rowContinuationOn (K : Set ℂ) [CompactSpace K] (hKH : K ⊆ upperHalfPlaneSet)
    (ν : SignedMeasure ℝ) (J : ℤ) (κ : ℂ) : C(K, ℂ) :=
  ∫ᵛ E : ℝ, continuedSeedOn K hKH E J κ ∂<•ν

/-- Actual variation integrability follows from continuity on the bounded
physical input interval, with no measurable-family premise supplied. -/
theorem rowContinuationOn_integrable (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (ν : SignedMeasure ℝ) (J : ℤ) (B : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ B)
    {κ : ℂ} (hκ : (-1 / 2 : ℝ) < κ.re) :
    ν.Integrable (fun E : ℝ => continuedSeedOn K hKH E J κ) := by
  let := signedMeasure_isFiniteMeasure_variation ν
  have hi : IntegrableOn (fun E : ℝ => continuedSeedOn K hKH E J κ)
      (Icc 0 B) ν.variation :=
    (continuous_continuedSeedOn_realEnergy K hKH J hκ).continuousOn.integrableOn_compact
      isCompact_Icc
  have hm : ∀ᵐ E ∂ν.variation, E ∈ Icc 0 B := by
    filter_upwards [hs] with E hE
    exact ⟨(abs_nonneg (J : ℝ)).trans hE.1, hE.2⟩
  simpa only [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hm] using hi

/-- Compact evaluation commutes with the genuine ordinary signed integral. -/
theorem signedIntegral_apply_compact (K : Set ℂ) [CompactSpace K]
    (ν : SignedMeasure ℝ) {F : ℝ → C(K, ℂ)} (hf : ν.Integrable F) (z : K) :
    (∫ᵛ E, F E ∂<•ν) z = ∫ᵛ E, F E z ∂<•ν := by
  let ev : C(K, ℂ) →L[ℂ] ℂ := ContinuousMap.evalCLM ℂ z
  have hi : Integrable F
      (ν.toJordanDecomposition.posPart + ν.toJordanDecomposition.negPart) := by
    simpa only [VectorMeasure.Integrable, ← SignedMeasure.totalVariation_eq_variation,
      SignedMeasure.totalVariation] using hf
  have he : ν.Integrable (fun E => ev (F E)) := ev.integrable_comp hf
  change ev (∫ᵛ E, F E ∂<•ν) = ∫ᵛ E, ev (F E) ∂<•ν
  rw [signedIntegral_eq_jordan hf, signedIntegral_eq_jordan he, map_sub,
    ev.integral_comp_comm hi.left_of_add_measure, ev.integral_comp_comm hi.right_of_add_measure]

/-- The compact signed family evaluates to the literal scalar signed integral. -/
theorem rowContinuationOn_apply (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (ν : SignedMeasure ℝ) (J : ℤ) (B : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ B)
    {κ : ℂ} (hκ : (-1 / 2 : ℝ) < κ.re) (z : K) :
    rowContinuationOn K hKH ν J κ z =
      ∫ᵛ E : ℝ, continuedSeedOn K hKH E J κ z ∂<•ν :=
  signedIntegral_apply_compact K ν (rowContinuationOn_integrable K hKH ν J B hs hκ) z

/-- Its threshold value is exactly the previously constructed ordinary row output. -/
theorem rowContinuationOn_zero (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (ν : SignedMeasure ℝ) (J : ℤ) (B : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ B)
    (τ : UpperHalfPlane) (hτ : (τ : ℂ) ∈ K) :
    rowContinuationOn K hKH ν J 0 ⟨τ, hτ⟩ = rowSeedSuperposition ν J τ := by
  rw [rowContinuationOn_apply K hKH ν J B hs (by norm_num)]
  apply VectorMeasure.integral_congr_ae
  exact Eventually.of_forall fun E => (generalThresholdSeed_eq_compact K hKH E J τ hτ).symm

/-- The same compact signed family agrees with the original general-energy
Poincaré superposition throughout the full original convergence region. -/
theorem rowContinuationOn_eq_original (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (ν : SignedMeasure ℝ) (J : ℤ) (B : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ B)
    {κ : ℂ} (hκ : (1 / 2 : ℝ) < κ.re) (z : K) :
    rowContinuationOn K hKH ν J κ z =
      ∫ᵛ E : ℝ, complexPoincareSeries E J (exponent κ) (ofComplex z) ∂<•ν := by
  rw [rowContinuationOn_apply K hKH ν J B hs (by linarith)]
  apply VectorMeasure.integral_congr_ae
  exact Eventually.of_forall fun E => continuedSeedOn_eq_series_full_convergence K hKH E J hκ z

/-- The compact ordinary signed superposition is norm analytic through threshold.
All slice measurability, analyticity and domination inputs are proved here. -/
theorem analyticAt_rowContinuationOn_zero (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (ν : SignedMeasure ℝ) (J : ℤ) (B : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ B) :
    AnalyticAt ℂ (rowContinuationOn K hKH ν J) 0 := by
  let := signedMeasure_isFiniteMeasure_variation ν
  let D := chosenContinuation K hKH
  obtain ⟨C, hC, hb⟩ := exists_continuedSeedOn_norm_bound K hKH B
  apply analyticAt_signedIntegral_of_dominated (r := D.radius)
    (bound := fun _ : ℝ => C * (1 + (J : ℝ) ^ 2 + B)) D.radius_pos
  · intro κ hκ
    exact (continuous_continuedSeedOn_realEnergy K hKH J
      (re_gt_neg_half_of_mem_continuation D (Or.inl hκ))).aestronglyMeasurable
  · exact Eventually.of_forall fun E =>
      (analyticOnNhd_continuedSeedOn K hKH E J).mono subset_union_left
  · filter_upwards [hs] with E hE
    have hE0 : 0 ≤ E := (abs_nonneg (J : ℝ)).trans hE.1
    have hnorm : ‖(E : ℂ)‖ = E := by simp [Complex.norm_real, abs_of_nonneg hE0]
    intro κ hκ
    have hn : ‖κ‖ ≤ D.radius := by
      exact le_of_lt (by simpa only [Metric.mem_ball, dist_zero_right] using hκ)
    have hh := hb E (by simpa only [hnorm] using hE.2) J κ hn
    rw [hnorm] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (by linarith [hE.2]) hC.le)
  · exact integrable_const _

end GapFamily.Analytic.PoincareEnergyContinuation
