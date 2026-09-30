import GapFamily.Analytic.Poincare.Seed.PoincareEnergyContinuation
import GapFamily.Analytic.Poincare.Threshold.PoincareThresholdModular
import GapFamily.Analytic.Poincare.Seed.PoincareEnergySeriesSmooth

/-! A canonical full threshold seed at arbitrary complex input energy. -/
noncomputable section
namespace GapFamily.Analytic.PoincareEnergyContinuation
open Set UpperHalfPlane CuspFourierCutoff PoincareCanonical
open PoincareEnergyConvergentAnalytic
open scoped ContDiff MatrixGroups

/-- The constructed zero-energy threshold seed plus the actual convergent
energy-difference series at exponent one half. -/
def generalThresholdSeed (E : ℂ) (J : ℤ) (τ : UpperHalfPlane) : ℂ :=
  thresholdSeed J τ + complexPoincareEnergyDifference E J (1 / 2) τ

/-- Zero energy recovers the canonical base exactly. -/
theorem generalThresholdSeed_zero_energy (J : ℤ) (τ : UpperHalfPlane) :
    generalThresholdSeed 0 J τ = thresholdSeed J τ := by
  simp [generalThresholdSeed, complexPoincareEnergyDifference, complexPoincareDifferenceTerm]

/-- Every compact observation gives the same actual general-energy threshold value. -/
theorem generalThresholdSeed_eq_compact (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (E : ℂ) (J : ℤ) (τ : UpperHalfPlane)
    (hτ : (τ : ℂ) ∈ K) :
    generalThresholdSeed E J τ = continuedSeedOn K hKH E J 0 ⟨τ, hτ⟩ := by
  unfold generalThresholdSeed continuedSeedOn
  change thresholdSeed J τ + _ = (chosenContinuation K hKH).family J 0 ⟨τ, hτ⟩ + _
  rw [thresholdSeed_eq_continuation (chosenContinuation K hKH) J τ hτ,
    compactEnergySeries_apply K hKH E J (by norm_num [exponent]), ofComplex_apply]
  simp [exponent]

/-- Continuity on the entire upper half-plane, including modular seams. -/
theorem continuous_generalThresholdSeed (E : ℂ) (J : ℤ) :
    Continuous (generalThresholdSeed E J) := by
  have hc := (PoincareEnergySeriesSmooth.contDiffOn_complexPoincareEnergyDifference
    E J (s := (1 / 2 : ℂ)) (by norm_num)).continuousOn
  have he : Continuous (fun τ : UpperHalfPlane => complexPoincareEnergyDifference E J (1 / 2) τ) := by
    simpa only [Function.comp_def, ofComplex_apply] using
      hc.comp_continuous UpperHalfPlane.continuous_coe (fun τ => τ.im_pos)
  exact (continuous_thresholdSeed J).add he

/-- The actual canonical general-energy threshold seed is modular invariant. -/
theorem generalThresholdSeed_smul (E : ℂ) (J : ℤ) (τ : UpperHalfPlane) (g : SL(2, ℤ)) :
    generalThresholdSeed E J (g • τ) = generalThresholdSeed E J τ := by
  unfold generalThresholdSeed
  rw [thresholdSeed_smul, complexPoincareEnergyDifference_smul]

/-- At each upper point, the full continued seed is entire in complex energy. -/
theorem analyticAt_generalThresholdSeed_energy (E : ℂ) (J : ℤ) (τ : UpperHalfPlane) :
    AnalyticAt ℂ (fun F : ℂ => generalThresholdSeed F J τ) E := by
  exact analyticAt_const.add
    (complexPoincareEnergyDifference_analyticAt_energy J (s := (1 / 2 : ℂ))
      (by norm_num) τ E)

/-- Uniform compact bounds for bounded complex energies and arbitrary integer spins. -/
theorem generalThresholdSeed_compact_bound (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (B : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (E : ℂ), ‖E‖ ≤ B → ∀ (J : ℤ) (τ : UpperHalfPlane),
      (τ : ℂ) ∈ K → ‖generalThresholdSeed E J τ‖ ≤ C * (1 + (J : ℝ) ^ 2 + ‖E‖) := by
  obtain ⟨C, hC, hb⟩ := exists_continuedSeedOn_norm_bound K hKH B
  refine ⟨C, hC, ?_⟩
  intro E hE J τ hτ
  rw [generalThresholdSeed_eq_compact K hKH E J τ hτ]
  exact ((continuedSeedOn K hKH E J 0).norm_coe_le_norm ⟨τ, hτ⟩).trans
    (hb E hE J 0 (by simpa using (chosenContinuation K hKH).radius_pos.le))

/-- The physical positive-energy ray has a global linear energy bound on every
compact set; no bounded-energy hypothesis is needed. -/
theorem generalThresholdSeed_nonneg_energy_bound (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) :
    ∃ C : ℝ, 0 < C ∧ ∀ (E : ℝ), 0 ≤ E → ∀ (J : ℤ) (τ : UpperHalfPlane),
      (τ : ℂ) ∈ K → ‖generalThresholdSeed E J τ‖ ≤ C * (1 + (J : ℝ) ^ 2 + E) := by
  let i : K → UpperHalfPlane := fun z => ⟨z, hKH z.property⟩
  have hi : Continuous i := continuous_subtype_val.upperHalfPlaneMk (fun z => hKH z.property)
  obtain ⟨C₀, hC₀, hb₀⟩ := thresholdSeed_compact_bound K hKH
  obtain ⟨C₁, hC₁, hb₁⟩ := exists_poincareEnergyDifference_compact_linear
    (isCompact_range hi) (s := (1 / 2 : ℝ)) (by norm_num)
  refine ⟨C₀ + C₁, add_pos hC₀ hC₁, ?_⟩
  intro E hE J τ hτ
  have he : ‖complexPoincareEnergyDifference (E : ℂ) J (1 / 2) τ‖ ≤ C₁ * E := by
    have ht : τ ∈ range i := ⟨⟨τ, hτ⟩, rfl⟩
    have hc : complexPoincareEnergyDifference (E : ℂ) J (1 / 2) τ =
        poincareEnergyDifference E J (1 / 2) τ := by
      simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
        complexPoincareEnergyDifference_ofReal E J (1 / 2) τ
    rw [hc]
    exact hb₁ J τ ht E hE
  calc
    _ ≤ ‖thresholdSeed J τ‖ + ‖complexPoincareEnergyDifference (E : ℂ) J (1 / 2) τ‖ :=
      norm_add_le _ _
    _ ≤ C₀ * (1 + (J : ℝ) ^ 2) + C₁ * E := add_le_add (hb₀ J τ hτ) he
    _ ≤ _ := by nlinarith [mul_nonneg hC₀.le hE, mul_nonneg hC₁.le (sq_nonneg (J : ℝ))]

end GapFamily.Analytic.PoincareEnergyContinuation
