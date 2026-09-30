import BTZEntropy.Comparison.SpinReferenceMeasure
import BTZEntropy.Descendant

/-! The actual integer-spin primary reference with every descendant level. -/

noncomputable section

namespace BTZEntropy

open Set MeasureTheory

/-- An integer-spin primary state and a pair of descendant levels. -/
abbrev IntegerReferenceState := (ℤ × ℝ) × (ℕ × ℕ)

/-- The physical integer-spin measure and counting measure on descendant levels. -/
def integerReferenceMeasure : Measure IntegerReferenceState :=
  spinReferenceMeasure.prod Measure.count

instance instSFiniteIntegerReferenceMeasure : SFinite integerReferenceMeasure := by
  unfold integerReferenceMeasure
  infer_instance

/-- Cylinder energy retains the exact residual central-charge shift. -/
def integerReferenceEnergy (p : IntegerReferenceState) : ℝ :=
  spinReferenceEnergy p.1 + (p.2.1 : ℝ) + (p.2.2 : ℝ) - 1 / 12

/-- The genuine integer-spin numerator with both partition multiplicities. -/
def integerReferenceWeight (a : ℝ) (p : IntegerReferenceState) : ℝ :=
  spinReferenceWeight a p.1 *
    (partitionCount p.2.1 : ℝ) * (partitionCount p.2.2 : ℝ)

@[fun_prop] theorem measurable_integerReferenceEnergy :
    Measurable integerReferenceEnergy := by
  unfold integerReferenceEnergy
  have hn : Measurable (fun n : ℕ => (n : ℝ)) := measurable_of_countable _
  exact (((measurable_spinReferenceEnergy.comp measurable_fst).add
    (hn.comp (measurable_fst.comp measurable_snd))).add
      (hn.comp (measurable_snd.comp measurable_snd))).sub measurable_const

@[fun_prop] theorem measurable_integerReferenceWeight (a : ℝ) :
    Measurable (integerReferenceWeight a) := by
  have hp : Measurable (fun n : ℕ => (partitionCount n : ℝ)) :=
    measurable_of_countable _
  exact (((measurable_spinReferenceWeight a).comp measurable_fst).mul
    (hp.comp (measurable_fst.comp measurable_snd))).mul
      (hp.comp (measurable_snd.comp measurable_snd))

theorem integerReferenceWeight_nonneg {a : ℝ} (ha : 2 ≤ a) :
    ∀ᵐ p ∂integerReferenceMeasure, 0 ≤ integerReferenceWeight a p := by
  apply (Measure.ae_prod_iff_ae_ae
    (measurableSet_le measurable_const (measurable_integerReferenceWeight a))).mpr
  filter_upwards [spinReferenceWeight_nonneg ha] with q hq
  exact Filter.Eventually.of_forall fun v =>
    mul_nonneg (mul_nonneg hq (Nat.cast_nonneg (partitionCount v.1)))
      (Nat.cast_nonneg (partitionCount v.2))

theorem integerReferenceEnergy_lower_bound (p : IntegerReferenceState) :
    -(1 / 12 : ℝ) ≤ integerReferenceEnergy p := by
  unfold integerReferenceEnergy
  have hq := spinReferenceEnergy_nonneg p.1
  have hL : 0 ≤ (p.2.1 : ℝ) := Nat.cast_nonneg _
  have hR : 0 ≤ (p.2.2 : ℝ) := Nat.cast_nonneg _
  linarith

/-- Exact separation of thermal weight into primary and descendant factors. -/
theorem integerReferenceThermal_factorization (a β : ℝ) (p : IntegerReferenceState) :
    integerReferenceWeight a p * Real.exp (-β * integerReferenceEnergy p) =
      Real.exp (β / 12) *
        (spinReferenceWeight a p.1 * Real.exp (-β * spinReferenceEnergy p.1)) *
        (partitionThermalTerm β p.2.1 * partitionThermalTerm β p.2.2) := by
  unfold integerReferenceWeight integerReferenceEnergy partitionThermalTerm
  rw [show -β * (spinReferenceEnergy p.1 + (p.2.1 : ℝ) + (p.2.2 : ℝ) - 1 / 12) =
      β / 12 + -β * spinReferenceEnergy p.1 + -β * (p.2.1 : ℝ) +
        -β * (p.2.2 : ℝ) by ring]
  simp only [Real.exp_add]
  ring

/-- The same literal factorization at an arbitrary complex inverse temperature. -/
theorem integerReferenceComplexThermal_factorization (a : ℝ) (z : ℂ)
    (p : IntegerReferenceState) :
    (integerReferenceWeight a p : ℂ) * Complex.exp (-z * (integerReferenceEnergy p : ℂ)) =
      Complex.exp (z / 12) *
        ((spinReferenceWeight a p.1 : ℂ) *
          Complex.exp (-z * (spinReferenceEnergy p.1 : ℂ))) *
        (((partitionCount p.2.1 : ℂ) * Complex.exp (-z * (p.2.1 : ℂ))) *
          ((partitionCount p.2.2 : ℂ) * Complex.exp (-z * (p.2.2 : ℂ)))) := by
  unfold integerReferenceWeight integerReferenceEnergy
  push_cast
  rw [show -z * ((spinReferenceEnergy p.1 : ℂ) + (p.2.1 : ℂ) + (p.2.2 : ℂ) - 1 / 12) =
      z / 12 + -z * (spinReferenceEnergy p.1 : ℂ) + -z * (p.2.1 : ℂ) +
        -z * (p.2.2 : ℂ) by ring]
  simp only [Complex.exp_add]
  ring

/-- Full thermal integrability for every positive real inverse temperature. -/
theorem integrable_integerReferenceThermal {a β : ℝ} (ha : 2 ≤ a) (hβ : 0 < β) :
    Integrable (fun p => integerReferenceWeight a p *
      Real.exp (-β * integerReferenceEnergy p)) integerReferenceMeasure := by
  have hp := integrable_spinReferenceThermal ha hβ
  have hs := (summable_partitionThermalTerm hβ).mul_of_nonneg
    (summable_partitionThermalTerm hβ) (partitionThermalTerm_nonneg β)
    (partitionThermalTerm_nonneg β)
  have hn : Integrable (fun v : ℕ × ℕ =>
      partitionThermalTerm β v.1 * partitionThermalTerm β v.2) Measure.count := by
    apply integrable_count_iff.mpr
    simpa only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
      (partitionThermalTerm_nonneg β _) (partitionThermalTerm_nonneg β _))] using hs
  have hi := (hp.mul_prod hn).const_mul (Real.exp (β / 12))
  apply hi.congr
  filter_upwards [] with p
  rw [integerReferenceThermal_factorization]
  ring

end BTZEntropy
