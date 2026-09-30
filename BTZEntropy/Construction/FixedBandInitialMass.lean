import GapFamily.Construction.FixedCutoffInitialRepair

/-! Uniform mass of the actual fixed-band initial packet. Every bound applies
to any moment-matched cell, independently of its selector and marker position. -/

noncomputable section

open Set MeasureTheory Real
open GapFamily.Analytic GapFamily.Construction
open scoped BigOperators

namespace BTZEntropy.Construction

/-- The absolute mass on any actual initial cell has a fixed-endpoint
exponential rate. The coefficient is uniform over the marker interval. -/
theorem fixedBand_initial_abs_mass_le
    {a b δ U : ℝ} {j : ℤ} {k : ℕ} {ha : 2 ≤ a} {hb : 1 ≤ b}
    (cell : InitialReferenceCell j (max b |(j : ℝ)|) U k
      (fixedCutoffReferenceDensity a b δ ha hb j))
    (hδ : 0 ≤ δ) (hδb : δ ≤ b)
    (Q : ℝ) (hQ : 1 ≤ Q) (hba : b ≤ a) (hQU : U = Q * b) :
    (∫ E in Ioo (max b |(j : ℝ)|) cell.right,
      |fixedCutoffReferenceDensity a b δ ha hb j E| ∂referenceMeasure j) ≤
      fixedCutoffReferenceCompactMassCoefficient (Q + 1) * (1 + a) ^ 9 *
        exp (fixedCutoffReferenceCompactMassExponent 2 * sqrt (a * U)) := by
  have hright : cell.right ≤ (Q + 1) * b := by
    have hr := cell.right_mem.2
    nlinarith
  have hq := fixedCutoffReferenceDensity_integrable a b δ ha hb hδ hδb ((Q + 1) * b) j
  have hmass : (∫ E in Ioo (max b |(j : ℝ)|) cell.right,
      |fixedCutoffReferenceDensity a b δ ha hb j E| ∂referenceMeasure j) ≤
      fixedCutoffReferenceCompactMassCoefficient (Q + 1) * (1 + a) ^ 9 *
        exp (fixedCutoffReferenceCompactMassExponent (Q + 1) * sqrt (a * b)) := by
    calc
      _ ≤ ∫ E in Ioo |(j : ℝ)| ((Q + 1) * b),
          |fixedCutoffReferenceDensity a b δ ha hb j E| ∂referenceMeasure j := by
        apply setIntegral_mono_set hq.abs (Filter.Eventually.of_forall fun _ => abs_nonneg _)
        exact Filter.Eventually.of_forall fun E hE =>
          ⟨(le_max_right b |(j : ℝ)|).trans_lt hE.1, hE.2.trans_le hright⟩
      _ ≤ _ := integral_abs_fixedCutoffReferenceDensity_le
        (Q + 1) a b δ (by linarith) ha hb hδ hδb hba j
  refine hmass.trans ?_
  have hC := fixedCutoffReferenceCompactMassCoefficient_pos (Q + 1) (by linarith)
  have hexp := exp_le_exp.mpr (fixedCutoffReferenceCompactMassExponent_mul_sqrt_le
    (by linarith : 0 ≤ a) (by linarith : 0 ≤ b) hQ hQU)
  exact mul_le_mul_of_nonneg_left hexp (by positivity)

/-- The literal count of unit nodes is bounded by the absolute signed
continuum mass, uniformly over all allowed marker positions. -/
theorem fixedBand_initial_count_le
    {a b δ U : ℝ} {j : ℤ} {k : ℕ} {ha : 2 ≤ a} {hb : 1 ≤ b}
    (cell : InitialReferenceCell j (max b |(j : ℝ)|) U k
      (fixedCutoffReferenceDensity a b δ ha hb j))
    (hδ : 0 ≤ δ) (hδb : δ ≤ b)
    (Q : ℝ) (hQ : 1 ≤ Q) (hba : b ≤ a) (hQU : U = Q * b) :
    (cell.count : ℝ) ≤
      fixedCutoffReferenceCompactMassCoefficient (Q + 1) * (1 + a) ^ 9 *
        exp (fixedCutoffReferenceCompactMassExponent 2 * sqrt (a * U)) :=
  cell.count_le_abs_mass.trans
    (fixedBand_initial_abs_mass_le cell hδ hδb Q hQ hba hQU)

/-- Any finite initial packet has the same mass scale, multiplied only by
the number of spin rows in the packet. -/
theorem fixedBand_sum_initial_count_le
    {S : Finset ℤ} {a b δ U : ℝ} {k : ℕ} {ha : 2 ≤ a} {hb : 1 ≤ b}
    (cells : ∀ J : S, InitialReferenceCell J (max b |(J : ℝ)|) U k
      (fixedCutoffReferenceDensity a b δ ha hb J))
    (hδ : 0 ≤ δ) (hδb : δ ≤ b)
    (Q : ℝ) (hQ : 1 ≤ Q) (hba : b ≤ a) (hQU : U = Q * b) :
    (∑ J : S, ((cells J).count : ℝ)) ≤
      (S.card : ℝ) * fixedCutoffReferenceCompactMassCoefficient (Q + 1) * (1 + a) ^ 9 *
        exp (fixedCutoffReferenceCompactMassExponent 2 * sqrt (a * U)) := by
  calc
    _ ≤ ∑ _ : S, fixedCutoffReferenceCompactMassCoefficient (Q + 1) * (1 + a) ^ 9 *
        exp (fixedCutoffReferenceCompactMassExponent 2 * sqrt (a * U)) :=
      Finset.sum_le_sum fun J _ => fixedBand_initial_count_le (cells J) hδ hδb Q hQ hba hQU
    _ = _ := by simp [mul_assoc]

/-- With fixed processing endpoint, the initial packet exponent is a fixed
constant times the square root of charge. -/
theorem fixedBand_sum_initial_count_le_sqrtCharge
    {S : Finset ℤ} {a b δ U : ℝ} {k : ℕ} {ha : 2 ≤ a} {hb : 1 ≤ b}
    (cells : ∀ J : S, InitialReferenceCell J (max b |(J : ℝ)|) U k
      (fixedCutoffReferenceDensity a b δ ha hb J))
    (hδ : 0 ≤ δ) (hδb : δ ≤ b)
    (Q : ℝ) (hQ : 1 ≤ Q) (hba : b ≤ a) (hQU : U = Q * b) :
    (∑ J : S, ((cells J).count : ℝ)) ≤
      (S.card : ℝ) * fixedCutoffReferenceCompactMassCoefficient (Q + 1) * (1 + a) ^ 9 *
        exp ((fixedCutoffReferenceCompactMassExponent 2 * sqrt U) * sqrt a) := by
  have hroot : fixedCutoffReferenceCompactMassExponent 2 * sqrt (a * U) =
      (fixedCutoffReferenceCompactMassExponent 2 * sqrt U) * sqrt a := by
    rw [sqrt_mul (by linarith : 0 ≤ a)]
    ring
  simpa only [hroot] using fixedBand_sum_initial_count_le cells hδ hδb Q hQ hba hQU

/-- The natural packet cardinality has the same real mass bound after
casting; multiplicities remain the literal numbers of unit nodes. -/
theorem fixedBand_total_initial_count_le_sqrtCharge
    {S : Finset ℤ} {a b δ U : ℝ} {k : ℕ} {ha : 2 ≤ a} {hb : 1 ≤ b}
    (cells : ∀ J : S, InitialReferenceCell J (max b |(J : ℝ)|) U k
      (fixedCutoffReferenceDensity a b δ ha hb J))
    (hδ : 0 ≤ δ) (hδb : δ ≤ b)
    (Q : ℝ) (hQ : 1 ≤ Q) (hba : b ≤ a) (hQU : U = Q * b) :
    ((∑ J : S, (cells J).count : ℕ) : ℝ) ≤
      (S.card : ℝ) * fixedCutoffReferenceCompactMassCoefficient (Q + 1) * (1 + a) ^ 9 *
        exp ((fixedCutoffReferenceCompactMassExponent 2 * sqrt U) * sqrt a) := by
  simpa only [Nat.cast_sum] using
    fixedBand_sum_initial_count_le_sqrtCharge cells hδ hδb Q hQ hba hQU

end BTZEntropy.Construction
