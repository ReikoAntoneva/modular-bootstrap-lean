import BTZEntropy.Analytic.IntegerReferenceInversionData
import BTZEntropy.Analytic.ReferenceInversionMeasure
import BTZEntropy.Comparison.ReferenceTestDefinition
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! The integer-spin physical reference count and its exact descendant disintegration. -/

noncomputable section

namespace BTZEntropy

open Set MeasureTheory GapFamily.Analytic

/-- Compact smoothing of the complete integer-spin reference distribution. -/
def integerReferenceSmoothCount (φ : SmoothKernel) (a E : ℝ) : ℝ :=
  weightedSmoothCount φ integerReferenceMeasure integerReferenceEnergy
    (integerReferenceWeight a) E

theorem integerReferenceSmoothCount_nonneg (φ : SmoothKernel) {a : ℝ}
    (ha : 2 ≤ a) (E : ℝ) : 0 ≤ integerReferenceSmoothCount φ a E := by
  apply integral_nonneg_of_ae
  filter_upwards [integerReferenceWeight_nonneg ha] with p hp
  exact mul_nonneg hp (φ.nonneg _)

theorem integrable_integerReferenceSmoothTerm (φ : SmoothKernel) {a : ℝ}
    (ha : 2 ≤ a) (E : ℝ) :
    Integrable (fun p => integerReferenceWeight a p *
      φ (integerReferenceEnergy p - E)) integerReferenceMeasure := by
  exact integrable_weightedSmoothCount φ 1 E integerReferenceEnergy
    (integerReferenceWeight a) measurable_integerReferenceEnergy
    (measurable_integerReferenceWeight a)
    (integrable_integerReferenceThermal ha (by norm_num))

private theorem integerReferenceSmooth_inner_eq_module (φ : SmoothKernel) (a E : ℝ)
    (q : ℤ × ℝ)
    (hi : Integrable (fun v : ℕ × ℕ => integerReferenceWeight a (q, v) *
      φ (integerReferenceEnergy (q, v) - E)) Measure.count) :
    (∫ v : ℕ × ℕ, integerReferenceWeight a (q, v) *
      φ (integerReferenceEnergy (q, v) - E) ∂Measure.count) =
      spinReferenceWeight a q * Comparison.moduleSmoothCount φ
        (fun n => (partitionCount n : ℝ)) (spinReferenceEnergy q - 1 / 12) E := by
  rw [integral_countable hi]
  simp only [count_real_singleton, one_smul, Comparison.moduleSmoothCount,
    ← tsum_mul_left]
  apply tsum_congr
  intro v
  unfold integerReferenceWeight integerReferenceEnergy Comparison.moduleSmoothTerm
  dsimp only
  rw [show spinReferenceEnergy q + (v.1 : ℝ) + (v.2 : ℝ) - 1 / 12 - E =
    spinReferenceEnergy q - 1 / 12 + (v.1 : ℝ) + (v.2 : ℝ) - E by ring]
  ring

theorem integrable_integerReferenceModule (φ : SmoothKernel) {a : ℝ}
    (ha : 2 ≤ a) (E : ℝ) :
    Integrable (fun q => spinReferenceWeight a q * Comparison.moduleSmoothCount φ
      (fun n => (partitionCount n : ℝ)) (spinReferenceEnergy q - 1 / 12) E)
        spinReferenceMeasure := by
  have hi := integrable_integerReferenceSmoothTerm φ ha E
  apply hi.integral_prod_left.congr
  filter_upwards [hi.prod_right_ae] with q hq
  exact integerReferenceSmooth_inner_eq_module φ a E q hq

/-- Fubini retains all descendant levels of every actual integer-spin primary. -/
theorem integerReferenceSmoothCount_eq_modules (φ : SmoothKernel) {a : ℝ}
    (ha : 2 ≤ a) (E : ℝ) :
    integerReferenceSmoothCount φ a E =
      ∫ q, spinReferenceWeight a q * Comparison.moduleSmoothCount φ
        (fun n => (partitionCount n : ℝ)) (spinReferenceEnergy q - 1 / 12) E
          ∂spinReferenceMeasure := by
  have hi := integrable_integerReferenceSmoothTerm φ ha E
  unfold integerReferenceSmoothCount weightedSmoothCount integerReferenceMeasure
  rw [integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [hi.prod_right_ae] with q hq
  exact integerReferenceSmooth_inner_eq_module φ a E q hq

/-- The weighted physical measure is exactly the all-descendant leading reference,
with every physical spin row and no positive-energy cutoff. -/
theorem integerReferenceSmoothCount_eq_leading (φ : SmoothKernel) {a : ℝ}
    (ha : 2 ≤ a) (E : ℝ) :
    integerReferenceSmoothCount φ a E = Comparison.integerLeadingSmoothCount φ a 0 E := by
  have hi := integrable_integerReferenceModule φ ha E
  rw [integerReferenceSmoothCount_eq_modules φ ha E]
  unfold spinReferenceMeasure at hi ⊢
  rw [integral_sum_measure hi]
  unfold Comparison.integerLeadingSmoothCount Comparison.integerLeadingTest
  apply tsum_congr
  intro j
  rw [(measurableEmbedding_prodMk_left j).integral_map]
  unfold Comparison.leadingRowTest
  rw [max_eq_right (abs_nonneg (j : ℝ))]
  have hr : (referenceMeasure j).restrict (Ioi |(j : ℝ)|) = referenceMeasure j :=
    Measure.restrict_eq_self_of_ae_mem (referenceMeasure_ae_above_edge j)
  rw [hr]
  apply integral_congr_ae
  filter_upwards [referenceMeasure_ae_above_edge j] with u hu
  simp only [spinReferenceWeight, spinReferenceEnergy,
    max_eq_right ((abs_nonneg _).trans hu.le), Comparison.fullPrimaryDescendantTest]

end BTZEntropy
