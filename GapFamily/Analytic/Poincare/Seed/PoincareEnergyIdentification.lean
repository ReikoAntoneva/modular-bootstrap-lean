import GapFamily.Analytic.Poincare.Seed.PoincareGeneralThreshold
import GapFamily.Analytic.Poincare.PoincareFullConvergenceIdentification
import GapFamily.Analytic.Poincare.PoincareScalarIdentification

/-! Identification on the full convergence region and in the scalar channel. -/
noncomputable section
namespace GapFamily.Analytic.PoincareEnergyContinuation
open Set UpperHalfPlane CuspFourierCutoff PoincareCanonical
open PoincareEnergyConvergentAnalytic

/-- Every compact continuation agrees with the original zero-energy series on
its full convergence half-plane; the constructed family fixes all choices. -/
theorem continuation_eq_series_full_convergence (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (D : Continuation K) (J : ℤ) {κ : ℂ}
    (hκ : (1 / 2 : ℝ) < κ.re) (z : K) :
    D.family J κ z = complexPoincareSeries 0 J (exponent κ) (ofComplex z) := by
  obtain ⟨P, r, C, hr, hr8, hC, ha, hb, he⟩ :=
    PoincareCompactContinuation.exists_compactPoincareContinuation_full_convergence K hKH
  let D' : Continuation K :=
    ⟨P, r, C, hr, hr8, hC, ha, hb, fun J κ hκ z => he J κ (by linarith) z⟩
  have hp : κ ∈ continuationRegion (min D.radius D'.radius) := by
    right
    refine ⟨by linarith, ?_⟩
    intro hh
    subst κ
    norm_num at hκ
  have hh := congrArg (fun f : C(K, ℂ) => f z)
    (continuation_restrict_eqOn D D' (Subset.refl K) J hp)
  change D.family J κ z = P J κ z at hh
  exact hh.trans (he J κ hκ z)

/-- The actual general-energy family recovers the original Poincaré sum
throughout Re s>1, for every complex energy and integer spin. -/
theorem continuedSeedOn_eq_series_full_convergence (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (E : ℂ) (J : ℤ) {κ : ℂ}
    (hκ : (1 / 2 : ℝ) < κ.re) (z : K) :
    continuedSeedOn K hKH E J κ z =
      complexPoincareSeries E J (exponent κ) (ofComplex z) := by
  have hs : 1 < (exponent κ).re := by
    norm_num [exponent, Complex.add_re]
    linarith
  change (chosenContinuation K hKH).family J κ z +
    compactEnergySeries K hKH E J (exponent κ) z = _
  rw [continuation_eq_series_full_convergence K hKH (chosenContinuation K hKH) J hκ z,
    compactEnergySeries_apply K hKH E J (by linarith),
    complexPoincareEnergyDifference_eq_sub E J hs]
  ring

/-- The newly constructed full family agrees exactly with the existing scalar
continuation, including its zero-energy vanishing normalization. -/
theorem generalThresholdSeed_zero_spin (E : ℂ) (τ : UpperHalfPlane) :
    generalThresholdSeed E 0 τ = continuedScalarSeed E τ := by
  rw [generalThresholdSeed, thresholdSeed_zero, zero_add, continuedScalarSeed_eq_difference]

/-- Physical support E≥|J| converts the compact spin/energy estimate into a
single quadratic energy bound, uniform on the entire physical cone. -/
theorem generalThresholdSeed_physical_bound (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) :
    ∃ C : ℝ, 0 < C ∧ ∀ (E : ℝ) (J : ℤ), |(J : ℝ)| ≤ E →
      ∀ (τ : UpperHalfPlane), (τ : ℂ) ∈ K →
        ‖generalThresholdSeed E J τ‖ ≤ C * (1 + E) ^ 2 := by
  obtain ⟨C, hC, hb⟩ := generalThresholdSeed_nonneg_energy_bound K hKH
  refine ⟨C, hC, ?_⟩
  intro E J hE τ hτ
  have hE0 : 0 ≤ E := (abs_nonneg (J : ℝ)).trans hE
  have hsq : (J : ℝ) ^ 2 ≤ E ^ 2 := by
    have := mul_self_le_mul_self (abs_nonneg (J : ℝ)) hE
    nlinarith [sq_abs (J : ℝ)]
  exact (hb E hE0 J τ hτ).trans
    (mul_le_mul_of_nonneg_left (by nlinarith) hC.le)

end GapFamily.Analytic.PoincareEnergyContinuation
