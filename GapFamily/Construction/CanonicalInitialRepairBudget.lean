import GapFamily.Construction.InitialCellKernelBound
import GapFamily.Analytic.Poincare.Repair.PoincareSingleSpinRepair
import Mathlib.Analysis.Real.Pi.Bounds

/-! The actual initial repair kernel satisfies the normalized error estimate
used in the integer parameter choice. Its output-energy growth is fully
absorbed by the vacuum envelope, leaving only polynomial charge dependence. -/

noncomputable section
open Real Set MeasureTheory
open GapFamily.Analytic
namespace GapFamily.Construction

private theorem initial_output_growth_le {a e : ℝ} (ha : 1 ≤ a) (he : 0 ≤ e) :
    e * exp (2 * π * (1 / 100 : ℝ) * sqrt (a * e)) ≤ exp (7 * sqrt (a * e)) := by
  have hs : sqrt e ≤ exp (sqrt e) := by linarith [add_one_le_exp (sqrt e)]
  have heexp : e ≤ exp (2 * sqrt e) := by
    have h := pow_le_pow_left₀ (sqrt_nonneg e) hs 2
    simpa only [sq_sqrt he, ← exp_nat_mul, Nat.cast_ofNat] using h
  have hroot : sqrt e ≤ sqrt (a * e) := sqrt_le_sqrt (by nlinarith)
  have hγ : 2 * π * (1 / 100 : ℝ) ≤ 5 := by linarith [Real.pi_lt_four]
  have hγ' := mul_le_mul_of_nonneg_right hγ (sqrt_nonneg (a * e))
  calc
    _ ≤ exp (2 * sqrt e) * exp (2 * π * (1 / 100 : ℝ) * sqrt (a * e)) :=
      mul_le_mul_of_nonneg_right heexp (exp_nonneg _)
    _ ≤ _ := by rw [← exp_add]; apply exp_le_exp.mpr; linarith

/-- The actual C2 kernel estimate after division by the vacuum envelope.
The proved frozen ratio can be supplied directly as `ρ`. -/
theorem norm_initialRepairKernel_le_normalized
    (B : ℝ) (hB : 1 ≤ B) (j jin : ℤ) (e a ρ : ℝ)
    (he : |(j : ℝ)| ≤ e) (hBe : B ≤ e) (ha : 1 ≤ a) (hρ : 2 ≤ ρ)
    (ν : SignedMeasure ℝ) (L V : ℝ) (k : ℕ)
    (hL : |(jin : ℝ)| ≤ L) (hLV : L ≤ V) (hVB : V ≤ B)
    (hwidth : sqrtInputWidth jin L V / (sqrt a / 100) ≤ 1 / ρ)
    (hν : ∀ᵐ E ∂ν.variation, E ∈ Icc L V)
    (hm : ∀ n ≤ k, (∫ᵛ x : ℝ, x ^ n ∂<•signedSqrtCoordinate jin ν) = 0) :
    ‖∫ᵛ E, canonicalRepairKernelEnergy B hB j jin e E ∂<•ν‖ ≤
      canonicalRepairCellCoefficient * ν.totalVariation.real univ * (1 + a + B) *
        exp (canonicalRepairKernelExponent * B) / ρ^k * exp (7 * sqrt (a * e)) := by
  have ha0 : 0 < a := by linarith
  have hρ0 : 0 < ρ := by linarith
  have he0 : 0 ≤ e := (zero_le_one.trans hB).trans hBe
  have hden : (1 / 100 : ℝ) * sqrt a = sqrt a / 100 := by ring
  have hθ : 0 ≤ sqrtInputWidth jin L V / (sqrt a / 100) :=
    div_nonneg (sqrtInputWidth_nonneg jin L V hLV) (by positivity)
  have hhalf : 1 / ρ ≤ (1 / 2 : ℝ) := one_div_le_one_div_of_le (by norm_num) hρ
  have hwidth' : sqrtInputWidth jin L V / ((1 / 100 : ℝ) * sqrt a) ≤ 1 / 2 := by
    rw [hden]
    exact hwidth.trans hhalf
  have hbase := norm_signedIntegral_canonicalRepairKernelEnergy_initial_le
    B hB j jin e he hBe ν L V a (1 / 100) k hL hLV ha0 (by norm_num) hwidth' hν hm
  rw [hden] at hbase
  have hpoly := inputColumnStripPolynomial_initialDisk_le B a
    ((1 / 100 : ℝ) * sqrt a / 2) hB ha0.le (by positivity)
    (by nlinarith [sqrt_nonneg a]) jin L V hL hLV hVB
  have hpow := pow_le_pow_left₀ hθ hwidth k
  have hC := canonicalRepairCellCoefficient_pos.le
  have hP := (inputColumnStripPolynomial_pos jin
    (|sqrtInputCenter jin L V| + (1 / 100 : ℝ) * sqrt a / 2) (by positivity)).le
  have hgrowth := initial_output_growth_le ha he0
  calc
    _ ≤ ν.totalVariation.real univ * e *
        inputColumnStripPolynomial jin (|sqrtInputCenter jin L V| + (1 / 100 : ℝ) * sqrt a / 2) *
          exp (canonicalRepairKernelExponent * B + 2 * π * (1 / 100 : ℝ) * sqrt (a * e)) *
            (sqrtInputWidth jin L V / (sqrt a / 100))^k  := by simpa only [hden] using hbase
    _ ≤ ν.totalVariation.real univ * e * (canonicalRepairCellCoefficient * (1 + a + B)) *
          exp (canonicalRepairKernelExponent * B + 2 * π * (1 / 100 : ℝ) * sqrt (a * e)) *
            (1 / ρ)^k := by gcongr
    _ = (canonicalRepairCellCoefficient * ν.totalVariation.real univ * (1 + a + B) *
        exp (canonicalRepairKernelExponent * B) * (1 / ρ)^k) *
          (e * exp (2 * π * (1 / 100 : ℝ) * sqrt (a * e))) := by
      rw [exp_add]
      ring
    _ ≤ (canonicalRepairCellCoefficient * ν.totalVariation.real univ * (1 + a + B) *
        exp (canonicalRepairKernelExponent * B) * (1 / ρ)^k) *
          exp (7 * sqrt (a * e)) := mul_le_mul_of_nonneg_left hgrowth (by positivity)
    _ = _ := by rw [one_div_pow]; ring

/-- The literal actual single-row initial repair on the frozen schedule has
the normalized estimate used in the proved initial parameter budget. -/
theorem norm_canonicalInitialRepairExterior_le
    {R s n : ℕ} (hR : 1 ≤ R) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hρ : 2 ≤ initialRepairRatio s) (B : ℝ) (hB : 1 ≤ B)
    (j jin : ℤ) (e : ℝ) (he : |(j : ℝ)| ≤ e) (hBe : B ≤ e)
    (ν : SignedMeasure ℝ) (L V : ℝ) (hL : |(jin : ℝ)| ≤ L)
    (hLV : L ≤ V) (hVB : V < B) (hVU : V ≤ ((R * n : ℕ) : ℝ) + 1)
    (hν : ∀ᵐ E ∂ν.variation, E ∈ Icc L V)
    (hm : ∀ k ≤ R * s * n,
      (∫ᵛ x : ℝ, x ^ k ∂<•signedSqrtCoordinate jin ν) = 0) :
    ‖canonicalRepairExteriorNumerator (singleSpinInput jin ν) B hB j e‖ ≤
      canonicalRepairCellCoefficient * ν.totalVariation.real univ *
        (1 + ((R * s ^ 2 * n : ℕ) : ℝ) + B) * exp (canonicalRepairKernelExponent * B) /
          (initialRepairRatio s)^(R * s * n) *
            exp (7 * sqrt (((R * s ^ 2 * n : ℕ) : ℝ) * e)) := by
  rw [canonicalRepairExteriorNumerator_singleSpin jin ν B hB
    (singleSpinInput_mem_lowBandSpinSet jin B L V hL hLV hVB)]
  have ha : (1 : ℝ) ≤ ((R * s ^ 2 * n : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ R * s ^ 2 * n by
      have hs2 : 1 ≤ s ^ 2 := one_le_pow₀ hs
      have hRs : 1 ≤ R * s ^ 2 := by simpa using Nat.mul_le_mul hR hs2
      simpa using Nat.mul_le_mul hRs hn)
  apply norm_initialRepairKernel_le_normalized B hB j jin e _ (initialRepairRatio s)
    he hBe ha hρ ν L V (R * s * n) hL hLV hVB.le _ hν hm
  simpa only [sqrtInputWidth, cellCoordinateLength, rootCoord] using
    initial_cell_cauchy_ratio_le hR hn hs (abs_nonneg (jin : ℝ)) hVU

end GapFamily.Construction
