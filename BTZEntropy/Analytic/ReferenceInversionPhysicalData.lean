import BTZEntropy.Analytic.ReferenceTransform
import BTZEntropy.Descendant

/-! The literal continuous primary reference with every descendant level. -/

noncomputable section

namespace BTZEntropy

open Set MeasureTheory

/-- A continuous energy-spin primary and a pair of descendant levels. -/
abbrev PhysicalReferenceState := (ℝ × ℝ) × (ℕ × ℕ)

/-- Lebesgue measure on the physical primary cone and counting measure on levels. -/
def physicalReferenceMeasure : Measure PhysicalReferenceState :=
  (volume.restrict referenceCone).prod Measure.count

/-- Cylinder energy includes the exact residual central-charge shift. -/
def physicalReferenceEnergy (p : PhysicalReferenceState) : ℝ :=
  p.1.1 + (p.2.1 : ℝ) + (p.2.2 : ℝ) - 1 / 12

/-- Reference density times the actual left and right partition multiplicities. -/
def physicalReferenceWeight (a : ℝ) (p : PhysicalReferenceState) : ℝ :=
  referencePrimaryDensity a p.1.1 p.1.2 *
    (partitionCount p.2.1 : ℝ) * (partitionCount p.2.2 : ℝ)

@[fun_prop] theorem measurable_physicalReferenceEnergy :
    Measurable physicalReferenceEnergy := by
  unfold physicalReferenceEnergy
  fun_prop

@[fun_prop] theorem measurable_physicalReferenceWeight (a : ℝ) :
    Measurable (physicalReferenceWeight a) := by
  have hp : Measurable (fun n : ℕ => (partitionCount n : ℝ)) :=
    measurable_of_countable _
  exact (((measurable_referencePrimaryDensity a).comp measurable_fst).mul
    (hp.comp (measurable_fst.comp measurable_snd))).mul
      (hp.comp (measurable_snd.comp measurable_snd))

theorem physicalReferenceWeight_nonneg {a : ℝ} (ha : 2 ≤ a)
    (p : PhysicalReferenceState) : 0 ≤ physicalReferenceWeight a p := by
  exact mul_nonneg
    (mul_nonneg (referencePrimaryDensity_nonneg ha _ _) (Nat.cast_nonneg _))
    (Nat.cast_nonneg _)

/-- Exact separation of thermal weight into primary and descendant factors. -/
theorem physicalReferenceThermal_factorization (a β : ℝ) (p : PhysicalReferenceState) :
    physicalReferenceWeight a p * Real.exp (-β * physicalReferenceEnergy p) =
      Real.exp (β / 12) *
        (referencePrimaryDensity a p.1.1 p.1.2 * Real.exp (-β * p.1.1)) *
        (partitionThermalTerm β p.2.1 * partitionThermalTerm β p.2.2) := by
  unfold physicalReferenceWeight physicalReferenceEnergy partitionThermalTerm
  rw [show -β * (p.1.1 + (p.2.1 : ℝ) + (p.2.2 : ℝ) - 1 / 12) =
      β / 12 + -β * p.1.1 + -β * (p.2.1 : ℝ) + -β * (p.2.2 : ℝ) by ring]
  simp only [Real.exp_add]
  ring

/-- The same literal factorization holds at any complex inverse temperature. -/
theorem physicalReferenceComplexThermal_factorization (a : ℝ) (z : ℂ)
    (p : PhysicalReferenceState) :
    (physicalReferenceWeight a p : ℂ) * Complex.exp (-z * (physicalReferenceEnergy p : ℂ)) =
      Complex.exp (z / 12) *
        ((referencePrimaryDensity a p.1.1 p.1.2 : ℂ) *
          Complex.exp (-z * (p.1.1 : ℂ))) *
        (((partitionCount p.2.1 : ℂ) * Complex.exp (-z * (p.2.1 : ℂ))) *
          ((partitionCount p.2.2 : ℂ) * Complex.exp (-z * (p.2.2 : ℂ)))) := by
  unfold physicalReferenceWeight physicalReferenceEnergy
  push_cast
  rw [show -z * ((p.1.1 : ℂ) + (p.2.1 : ℂ) + (p.2.2 : ℂ) - 1 / 12) =
      z / 12 + -z * (p.1.1 : ℂ) + -z * (p.2.1 : ℂ) + -z * (p.2.2 : ℂ) by ring]
  simp only [Complex.exp_add]
  ring

/-- Absolute convergence of the full physical reference thermal weight. -/
theorem integrable_physicalReferenceThermal {a β : ℝ} (ha : 2 ≤ a) (hβ : 0 < β) :
    Integrable (fun p => physicalReferenceWeight a p *
      Real.exp (-β * physicalReferenceEnergy p)) physicalReferenceMeasure := by
  have hp : Integrable (fun p : ℝ × ℝ => referencePrimaryDensity a p.1 p.2 *
      Real.exp (-β * p.1)) (volume.restrict referenceCone) := by
    simpa only [IntegrableOn, mul_comm] using integrableOn_referencePrimaryThermal ha hβ
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
  rw [physicalReferenceThermal_factorization]
  ring

end BTZEntropy
