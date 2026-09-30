import GapFamily.Analytic.Cusp.Threshold.CuspConstrainedUpperNorm

noncomputable section
namespace GapFamily.Analytic.CuspConstrainedSourceNorm
open Set MeasureTheory UpperHalfPlane ModularGradient
open CuspConstrainedUpperNorm CuspConstrainedThreshold CuspConstrainedPoissonJet
open scoped ContDiff

/-- Genuine continuity of the constructed source and form gives simultaneous
bounds for the energy and for the actual projected Poisson source. -/
theorem exists_effective_source_energy_bound (α : ℝ) (hα : 0 ≤ α) :
    ∃ A D : ℝ, 0 < A ∧ 0 ≤ D ∧ ∀ F : ModularHilbert,
      ‖formGradient (constrainedForm α hα F : FormDomain)‖ ≤ A * ‖F‖ ∧
      ‖constrainedPoissonSource (effectiveSource α hα F)‖ ≤ D * ‖F‖ := by
  obtain ⟨A, hA, ha⟩ := exists_constrainedForm_tail_bound α hα
  let B : ℝ := ‖effectiveSource α hα‖
  have hB : 0 ≤ B := norm_nonneg _
  refine ⟨A, 2 * B + A, hA, by positivity, fun F => ?_⟩
  have hu := (ha F).1
  have he : ‖meanZeroCuspEmbedding (constrainedForm α hα F)‖ ≤ A * ‖F‖ :=
    (meanZeroCuspEmbedding_norm_le _).trans hu
  have hf : ‖effectiveSource α hα F‖ ≤ B * ‖F‖ := (effectiveSource α hα).le_opNorm F
  refine ⟨(Dirichlet.gradientValue_norm_le closedGradient
    (constrainedForm α hα F : FormDomain)).trans hu, ?_⟩
  have hquarter : ‖(1 / 4 : ℂ)‖ ≤ 1 := by norm_num
  have hpart : ‖(1 / 4 : ℂ) • meanZeroCuspEmbedding (constrainedForm α hα F)‖ ≤ A * ‖F‖ := by
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_right hquarter (norm_nonneg _)).trans (by simpa using he)
  change ‖effectiveSource α hα F - cuspScalarProjection (effectiveSource α hα F) +
    (1 / 4 : ℂ) • meanZeroCuspEmbedding (constrainedForm α hα F)‖ ≤ _
  calc
    _ ≤ ‖effectiveSource α hα F - cuspScalarProjection (effectiveSource α hα F)‖ +
        ‖(1 / 4 : ℂ) • meanZeroCuspEmbedding (constrainedForm α hα F)‖ := norm_add_le _ _
    _ ≤ (‖effectiveSource α hα F‖ + ‖cuspScalarProjection (effectiveSource α hα F)‖) +
        A * ‖F‖ := add_le_add (norm_sub_le _ _) hpart
    _ ≤ (B * ‖F‖ + B * ‖F‖) + A * ‖F‖ :=
      add_le_add (add_le_add hf ((cuspScalarProjection_norm_le _).trans hf)) le_rfl
    _ = _ := by ring

/-- One constant, chosen before the height, cutoff and input, bounds all four
actual constrained Poisson fields for every admissible unit cusp window. -/
theorem exists_constrainedJet_uniform_field_bound (α : ℝ) (hα : 0 ≤ α) :
    ∃ C : ℝ, 0 < C ∧ ∀ (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ)
      (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ upperHalfPlaneSet)
      (H : ℝ), 1 ≤ H →
      (∀ z ∈ tsupport χ, |z.re| ≤ 1 ∧ H < z.im ∧ z.im ≤ H + 1) →
      (∀ z ∈ tsupport χ, ‖χ z‖ ≤ 1) → ∀ F : ModularHilbert,
      let j := constrainedJet χ hχ hc hs (effectiveSource α hα F)
      ‖j.1‖ ^ 2 + ‖j.2.1‖ ^ 2 + ‖j.2.2.1‖ ^ 2 + ‖j.2.2.2‖ ^ 2 ≤ C * ‖F‖ ^ 2 := by
  obtain ⟨A, D, hA, hD, hb⟩ := exists_effective_source_energy_bound α hα
  refine ⟨24 * A ^ 2 + 3 * D ^ 2, by positivity, ?_⟩
  intro χ hχ hc hs H hH hwindow hamp F
  have he := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hA.le (norm_nonneg F))).mpr (hb F).1
  have hf := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hD (norm_nonneg F))).mpr (hb F).2
  have hj := constrainedJet_field_mass_bound χ hχ hc hs H hH hwindow hamp (effectiveSource α hα F)
  change (let j := constrainedJet χ hχ hc hs (effectiveSource α hα F); _) ≤ _ at hj ⊢
  change (let j := constrainedJet χ hχ hc hs (effectiveSource α hα F); _) ≤
    24 * ‖formGradient (constrainedForm α hα F : FormDomain)‖ ^ 2 +
      3 * ‖constrainedPoissonSource (effectiveSource α hα F)‖ ^ 2 at hj
  exact hj.trans (by nlinarith)

end GapFamily.Analytic.CuspConstrainedSourceNorm
