import GapFamily.Construction.FixedCutoffInitialRepair

/-!
# Exterior repair estimate at a fixed processing endpoint

The clearing cutoff, processing endpoint, and Cauchy ratio are fixed before
the charge grows. All cells below the processing endpoint then share the
same normalized exterior estimate, uniformly in the marker position.
-/

noncomputable section

open Set MeasureTheory Real
open GapFamily.Analytic GapFamily.Construction
open scoped BigOperators

namespace BTZEntropy.Construction

/-- One frozen ratio absorbs the fixed endpoint mass exponent. Its choice
does not depend on the processing endpoint or the marker position. -/
def fixedBandRepairRatio : ℝ :=
  exp (2 * fixedCutoffReferenceCompactMassExponent 2 + 2)

theorem fixedBandRepairRatio_two_le : 2 ≤ fixedBandRepairRatio := by
  have hC := fixedCutoffReferenceCompactMassExponent_pos 2
  have h := add_one_le_exp (2 * fixedCutoffReferenceCompactMassExponent 2 + 2)
  unfold fixedBandRepairRatio
  linarith

theorem fixedBandRepairRatio_log_gain :
    2 * fixedCutoffReferenceCompactMassExponent 2 + 1 ≤ log fixedBandRepairRatio := by
  rw [fixedBandRepairRatio, log_exp]
  linarith

/-- A fixed processing band fits any fixed Cauchy ratio once the charge is
large enough. The threshold is independent of the row and left endpoint. -/
theorem fixedBand_cauchy_ratio_le {a U ρ L V : ℝ} (j : ℤ)
    (ha : 0 < a) (hU : 0 ≤ U) (hρ : 0 < ρ) (hV : V ≤ U + 1)
    (hcharge : 10000 * ρ ^ 2 * (U + 1) ≤ a) :
    sqrtInputWidth j L V / (sqrt a / 100) ≤ 1 / ρ := by
  have hwidth : sqrtInputWidth j L V ≤ sqrt (U + 1) := by
    unfold sqrtInputWidth
    have hroot := sqrt_le_sqrt (show V - |(j : ℝ)| ≤ U + 1 by
      linarith [abs_nonneg (j : ℝ)])
    linarith [sqrt_nonneg (L - |(j : ℝ)|)]
  have hroot : 100 * ρ * sqrt (U + 1) ≤ sqrt a := by
    have hsq := sq_sqrt (show 0 ≤ U + 1 by linarith)
    have hsq' := sq_sqrt ha.le
    have hpos : 0 ≤ 100 * ρ * sqrt (U + 1) := by positivity
    have hsquare : (100 * ρ * sqrt (U + 1)) ^ 2 ≤ a := by
      nlinarith [hcharge]
    nlinarith [sqrt_nonneg a]
  apply (div_le_div_iff₀ (by positivity) hρ).mpr
  have hm := mul_le_mul_of_nonneg_right hwidth hρ.le
  nlinarith

/-- Normalized exterior error of a single fixed-band initial cell. -/
def fixedBandRepairCellBudget (Q a U ρ B : ℝ) (k : ℕ) : ℝ :=
  2 * canonicalRepairCellCoefficient * fixedCutoffReferenceCompactMassCoefficient (Q + 1) *
    (1 + a + B) ^ 10 *
    exp (fixedCutoffReferenceCompactMassExponent 2 * sqrt (a * U) +
      canonicalRepairKernelExponent * B) / ρ ^ k

theorem fixedBandRepairCellBudget_nonneg {Q a U ρ B : ℝ} (k : ℕ)
    (hQ : 1 ≤ Q) (ha : 0 ≤ a) (hB : 0 ≤ B) (hρ : 0 < ρ) :
    0 ≤ fixedBandRepairCellBudget Q a U ρ B k := by
  have := canonicalRepairCellCoefficient_pos
  have := fixedCutoffReferenceCompactMassCoefficient_pos (Q + 1) (by linarith)
  unfold fixedBandRepairCellBudget
  positivity

/-- The estimate uses the actual residual and its exact moments; no choice
of atom selector or marker position enters the coefficient. -/
theorem fixedBand_abs_exteriorNumerator_le
    {a b δ U Q ρ : ℝ} {k : ℕ} {jin : ℤ} {ha : 2 ≤ a} {hb : 1 ≤ b}
    (cell : InitialReferenceCell jin (max b |(jin : ℝ)|) U k
      (fixedCutoffReferenceDensity a b δ ha hb jin))
    (hδ : 0 ≤ δ) (hδb : δ ≤ b) (hU : 1 ≤ U) (hρ : 2 ≤ ρ)
    (hQ : 1 ≤ Q) (hba : b ≤ a) (hQU : U = Q * b)
    (hcharge : 10000 * ρ ^ 2 * (U + 1) ≤ a)
    (B : ℝ) (hB : 1 ≤ B) (hcut : cell.right < B)
    (j : ℤ) (e : ℝ) (he : |(j : ℝ)| ≤ e) (hBe : B ≤ e) :
    |cell.exteriorNumerator B hB j e| ≤
      fixedBandRepairCellBudget Q a U ρ B k * exp (7 * sqrt (a * e)) := by
  have hwidth := fixedBand_cauchy_ratio_le (L := max b |(jin : ℝ)|) jin (by linarith : 0 < a)
    (by linarith : 0 ≤ U) (by linarith : 0 < ρ) cell.right_mem.2 hcharge
  have hbase := norm_initialRepairKernel_le_normalized B hB j jin e a ρ
    he hBe (by linarith) hρ cell.residual (max b |(jin : ℝ)|) cell.right k
    (le_max_right _ _) cell.left_le_right hcut.le hwidth
    cell.ae_mem_cell (fun m hm => cell.signedSqrtCoordinate_moment_zero m hm)
  rw [SignedMeasure.totalVariation_eq_variation] at hbase
  have htv : cell.residual.variation.real univ ≤
      2 * fixedCutoffReferenceCompactMassCoefficient (Q + 1) * (1 + a + B) ^ 9 *
        exp (fixedCutoffReferenceCompactMassExponent 2 * sqrt (a * U)) := by
    refine (cell.variation_le_fixedCutoff_endpoint hδ hδb Q hQ hba hQU).trans ?_
    have hpoly : (1 + a) ^ 9 ≤ (1 + a + B) ^ 9 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 9
    have := fixedCutoffReferenceCompactMassCoefficient_pos (Q + 1) (by linarith)
    gcongr
  have hcanonical : ‖canonicalRepairExteriorNumerator (singleSpinInput jin cell.residual)
      B hB j e‖ ≤ fixedBandRepairCellBudget Q a U ρ B k *
        exp (7 * sqrt (a * e)) := by
    rw [canonicalRepairExteriorNumerator_singleSpin jin cell.residual B hB
      (singleSpinInput_mem_lowBandSpinSet jin B (max b |(jin : ℝ)|) cell.right
        (le_max_right _ _) cell.left_le_right hcut)]
    refine hbase.trans ?_
    have := canonicalRepairCellCoefficient_pos
    have hρ0 : 0 < ρ := by linarith
    calc
      _ ≤ canonicalRepairCellCoefficient *
          (2 * fixedCutoffReferenceCompactMassCoefficient (Q + 1) * (1 + a + B) ^ 9 *
            exp (fixedCutoffReferenceCompactMassExponent 2 * sqrt (a * U))) *
          (1 + a + B) * exp (canonicalRepairKernelExponent * B) / ρ ^ k *
            exp (7 * sqrt (a * e)) := by gcongr
      _ = _ := by unfold fixedBandRepairCellBudget; rw [exp_add]; ring
  exact (Complex.abs_re_le_norm _).trans hcanonical

/-- Summing the actual fixed-band rows only multiplies the cell budget by
the cardinality of the finite row set. -/
theorem fixedBand_sum_abs_exteriorNumerator_le
    {S : Finset ℤ} {a b δ U Q ρ : ℝ} {k : ℕ} {ha : 2 ≤ a} {hb : 1 ≤ b}
    (cells : ∀ J : S, InitialReferenceCell J (max b |(J : ℝ)|) U k
      (fixedCutoffReferenceDensity a b δ ha hb J))
    (hδ : 0 ≤ δ) (hδb : δ ≤ b) (hU : 1 ≤ U) (hρ : 2 ≤ ρ)
    (hQ : 1 ≤ Q) (hba : b ≤ a) (hQU : U = Q * b)
    (hcharge : 10000 * ρ ^ 2 * (U + 1) ≤ a)
    (B : ℝ) (hB : 1 ≤ B) (hcut : ∀ J, (cells J).right < B)
    (j : ℤ) (e : ℝ) (he : |(j : ℝ)| ≤ e) (hBe : B ≤ e) :
    (∑ J, |(cells J).exteriorNumerator B hB j e|) ≤
      (S.card : ℝ) * fixedBandRepairCellBudget Q a U ρ B k *
        exp (7 * sqrt (a * e)) := by
  calc
    _ ≤ ∑ _ : S, fixedBandRepairCellBudget Q a U ρ B k *
        exp (7 * sqrt (a * e)) := Finset.sum_le_sum fun J _ =>
      fixedBand_abs_exteriorNumerator_le (cells J) hδ hδb hU hρ hQ hba hQU
        hcharge B hB (hcut J) j e he hBe
    _ = _ := by simp [mul_assoc]

/-- The common exterior indicator preserves the finite-row estimate also
below the repair band. -/
theorem fixedBand_sum_abs_exteriorIndicator_le
    {S : Finset ℤ} {a b δ U Q ρ : ℝ} {k : ℕ} {ha : 2 ≤ a} {hb : 1 ≤ b}
    (cells : ∀ J : S, InitialReferenceCell J (max b |(J : ℝ)|) U k
      (fixedCutoffReferenceDensity a b δ ha hb J))
    (hδ : 0 ≤ δ) (hδb : δ ≤ b) (hU : 1 ≤ U) (hρ : 2 ≤ ρ)
    (hQ : 1 ≤ Q) (hba : b ≤ a) (hQU : U = Q * b)
    (hcharge : 10000 * ρ ^ 2 * (U + 1) ≤ a)
    (j : ℤ) (e : ℝ) (he : |(j : ℝ)| ≤ e) :
    (∑ J, |if 2 * U + 4 < e then
      (cells J).exteriorNumerator (2 * U + 4) (by linarith) j e else 0|) ≤
      (S.card : ℝ) * fixedBandRepairCellBudget Q a U ρ (2 * U + 4) k *
        exp (7 * sqrt (a * e)) := by
  by_cases hBe : 2 * U + 4 < e
  · simp_rw [ite_eq_left hBe]
    exact fixedBand_sum_abs_exteriorNumerator_le cells hδ hδb hU hρ hQ hba hQU hcharge
      _ (by linarith) (fun J => by linarith [(cells J).right_mem.2]) j e he hBe.le
  · simp only [ite_eq_right hBe, abs_zero, Finset.sum_const_zero]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (fixedBandRepairCellBudget_nonneg k hQ (by linarith) (by linarith) (by linarith)))
      (exp_nonneg _)

end BTZEntropy.Construction
