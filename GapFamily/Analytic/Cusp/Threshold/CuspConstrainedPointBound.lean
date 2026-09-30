import GapFamily.Analytic.Cusp.Threshold.CuspConstrainedSourceNorm
import GapFamily.Analytic.Cusp.CuspUniformBump
import GapFamily.Analytic.Elliptic.LocalPoissonTranslate

noncomputable section
namespace GapFamily.Analytic.CuspConstrainedPointBound
open Set MeasureTheory UpperHalfPlane ModularGradient LocalPoisson
open CuspConstrainedSourceNorm CuspConstrainedThreshold CuspConstrainedPoissonJet
  CuspUniformBump FixedPoissonPointBound LocalPoissonTranslate
open scoped ContDiff

/-- A genuine height-independent point bound for every continuous representative
of the actual constrained response. The local representative equality is literal
ordinary Lebesgue AE equality to the existing cutoff value operator. -/
theorem exists_constrained_point_bound (α : ℝ) (hα : 0 ≤ α) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℂ) (_hp : |p.re| ≤ (1 / 2 : ℝ)) (hpy : 2 ≤ p.im)
      (F : ModularHilbert) (g : ℂ → ℂ),
      ContinuousOn g {z : ℂ | z - p ∈ referenceSquare} →
      g =ᵐ[volume.restrict {z : ℂ | z - p ∈ referenceSquare}]
        (upperCutoffValueOperator (bump p) (contDiff_bump p) (hasCompactSupport_bump p)
          (tsupport_bump_subset_upperHalfPlane hpy) (constrainedForm α hα F : FormDomain)) →
      ‖g p‖ ≤ C * ‖F‖ := by
  obtain ⟨A, hA, ha⟩ := exists_translated_point_sq_bound
  obtain ⟨B, hB, hb⟩ := exists_constrainedJet_uniform_field_bound α hα
  refine ⟨A * B + 1, by positivity, ?_⟩
  intro p hp hpy F g hg hga
  let U : Set ℂ := {z : ℂ | z - p ∈ referenceSquare}
  let j : JetSpace U := ⟨constrainedJet (bump p) (contDiff_bump p) (hasCompactSupport_bump p)
      (tsupport_bump_subset_upperHalfPlane hpy) (effectiveSource α hα F),
    constrainedJet_mem (bump p) (contDiff_bump p) (hasCompactSupport_bump p)
      (tsupport_bump_subset_upperHalfPlane hpy) U (isOpen_translatedReferenceSquare p)
      (bump_eq_one_on_referenceSquare p) (translatedReferenceSquare_subset_high hpy) _⟩
  have hga' : g =ᵐ[volume.restrict U] (fun z => valueCLM U j z) := hga
  have hpoint := ha p j g hg hga'
  have hfield := hb (bump p) (contDiff_bump p) (hasCompactSupport_bump p)
    (tsupport_bump_subset_upperHalfPlane hpy) (p.im - 1 / 2) (one_le_lowerHeight hpy)
    (fun z hz => tsupport_bump_coordinate_bounds hp hz) (fun z _ => norm_bump_le_one p z) F
  change ‖valueCLM U j‖ ^ 2 + ‖dxCLM U j‖ ^ 2 + ‖dyCLM U j‖ ^ 2 +
    ‖sourceCLM U j‖ ^ 2 ≤ B * ‖F‖ ^ 2 at hfield
  have hsq : ‖g p‖ ^ 2 ≤ (A * B) * ‖F‖ ^ 2 := by
    calc
      _ ≤ A * (‖valueCLM U j‖ ^ 2 + ‖dxCLM U j‖ ^ 2 + ‖dyCLM U j‖ ^ 2 +
        ‖sourceCLM U j‖ ^ 2) := hpoint
      _ ≤ A * (B * ‖F‖ ^ 2) := mul_le_mul_of_nonneg_left hfield hA.le
      _ = _ := by ring
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ (A * B + 1) * ‖F‖)).mp
  calc
    _ ≤ (A * B) * ‖F‖ ^ 2 := hsq
    _ ≤ (A * B + 1) ^ 2 * ‖F‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg (A * B), mul_nonneg hA.le hB.le])
        (sq_nonneg _)
    _ = _ := by ring

end GapFamily.Analytic.CuspConstrainedPointBound
