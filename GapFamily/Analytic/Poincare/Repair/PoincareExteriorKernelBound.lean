import GapFamily.Analytic.Poincare.Repair.PoincareExteriorKernel
import GapFamily.Analytic.Poincare.Repair.PoincareAnchorExteriorBound

/-! A universal exterior estimate for the actual canonical repair kernel.
The band factors are absorbed into a fixed exponential in the band width.
The exact coefficient `4 * π` of the imaginary input width is retained.
-/

noncomputable section

namespace GapFamily.Analytic

open Real

private theorem canonicalInputColumnStripSize_le (B : ℝ) (hB : 1 ≤ B)
    (jin : ℤ) (e R r : ℝ) (hBe : B ≤ e) (hR : 0 ≤ R) (hr : 0 ≤ r) :
    inputColumnStripSize (Fintype.card (LowBandSpin B)) jin B R r ≤
      15 * B ^ 2 * inputColumnStripPolynomial jin R * exp (4 * π * r * sqrt e) := by
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hP := (inputColumnStripPolynomial_pos jin R hR).le
  have hcard : (Fintype.card (LowBandSpin B) : ℝ) ≤ 5 * B := by
    simpa only [Fintype.card_coe] using lowBandSpinSet_card_le B hB
  have hs : sqrt B ≤ B := sqrt_le_self_iff.mpr (Or.inr hB)
  have hexp : exp (4 * π * r * sqrt B) ≤ exp (4 * π * r * sqrt e) := by
    apply exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (sqrt_le_sqrt hBe) (by positivity)
  unfold inputColumnStripSize
  calc
    _ ≤ (5 * B) * inputColumnStripPolynomial jin R * (B + 2 * B) *
        exp (4 * π * r * sqrt e) := by gcongr
    _ = _ := by ring

private theorem canonicalResponseStripCoefficient_le (B : ℝ) (hB : 1 ≤ B)
    (e : ℝ) (hBe : B ≤ e) :
    correctedKernelBound * (e * B + sqrt e * sqrt B) *
      sqrt (Fintype.card (LowBandSpin B) : ℝ) ≤
        10 * correctedKernelBound * e * B ^ 2 := by
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have he1 : 1 ≤ e := hB.trans hBe
  have he0 : 0 ≤ e := zero_le_one.trans he1
  have hC := correctedKernelBound_pos.le
  have hcard : (Fintype.card (LowBandSpin B) : ℝ) ≤ 5 * B := by
    simpa only [Fintype.card_coe] using lowBandSpinSet_card_le B hB
  have hs : sqrt (Fintype.card (LowBandSpin B) : ℝ) ≤ 5 * B :=
    (sqrt_le_sqrt hcard).trans (sqrt_le_self_iff.mpr (Or.inr (by linarith)))
  have hsB : sqrt B ≤ B := sqrt_le_self_iff.mpr (Or.inr hB)
  have hse : sqrt e ≤ e := sqrt_le_self_iff.mpr (Or.inr he1)
  calc
    _ ≤ correctedKernelBound * (e * B + e * B) * (5 * B) := by gcongr
    _ = _ := by ring

private theorem canonicalInverseThresholdStripCoefficient_le (B : ℝ) (hB : 1 ≤ B) :
    3 * B * (1 + (Fintype.card (LowBandSpin B) : ℝ) *
      (correctedSmoothingBound B * sqrt (Fintype.card (LowBandSpin B) : ℝ)) *
        ‖correctedLowBandInverse (fun J : LowBandSpin B => (J : ℤ)) B‖) ≤
      3 * (1 + 100 * correctedKernelBound) * B ^ 5 *
        exp (correctedLowBandCoercivityExponent * B) := by
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hC := correctedKernelBound_pos.le
  have hcard : (Fintype.card (LowBandSpin B) : ℝ) ≤ 5 * B := by
    simpa only [Fintype.card_coe] using lowBandSpinSet_card_le B hB
  have hs : sqrt (Fintype.card (LowBandSpin B) : ℝ) ≤ 5 * B :=
    (sqrt_le_sqrt hcard).trans (sqrt_le_self_iff.mpr (Or.inr (by linarith)))
  have hS := correctedSmoothingBound_le B hB
  have hS0 := correctedSmoothingBound_nonneg B hB0
  have hI := norm_correctedLowBandInverse_le_exp
    (fun J : LowBandSpin B => (J : ℤ)) (lowBandSpin_injective B) B hB
      (lowBandSpin_physical B)
  have hExp : 1 ≤ exp (correctedLowBandCoercivityExponent * B) :=
    one_le_exp (mul_nonneg correctedLowBandCoercivityExponent_pos.le hB0)
  have hpow : 1 ≤ B ^ 4 := one_le_pow₀ hB
  have hprod : (Fintype.card (LowBandSpin B) : ℝ) *
      (correctedSmoothingBound B * sqrt (Fintype.card (LowBandSpin B) : ℝ)) ≤
        100 * correctedKernelBound * B ^ 4 := by
    calc
      _ ≤ (5 * B) * ((4 * correctedKernelBound * B ^ 2) * (5 * B)) := by gcongr
      _ = _ := by ring
  calc
    _ ≤ 3 * B * (1 + (100 * correctedKernelBound * B ^ 4) *
        exp (correctedLowBandCoercivityExponent * B)) := by gcongr
    _ ≤ 3 * B * (B ^ 4 * exp (correctedLowBandCoercivityExponent * B) +
        (100 * correctedKernelBound * B ^ 4) *
          exp (correctedLowBandCoercivityExponent * B)) := by
      gcongr
      exact one_le_mul_of_one_le_of_one_le hpow hExp
    _ = _ := by ring

/-- A fixed positive rate for all canonical exterior kernels. -/
def canonicalRepairKernelExponent : ℝ :=
  (48 + 4650 * correctedKernelBound) +
    (correctedLowBandCoercivityExponent + canonicalAnchorExteriorExponent) + 7

theorem canonicalRepairKernelExponent_pos : 0 < canonicalRepairKernelExponent := by
  unfold canonicalRepairKernelExponent
  have := correctedKernelBound_pos
  have := correctedLowBandCoercivityExponent_pos
  have := canonicalAnchorExteriorExponent_pos
  positivity

private theorem exterior_polynomial_absorption {B C H T : ℝ}
    (hB : 1 ≤ B) (hC : 0 ≤ C) (hH : 0 ≤ H) (hT : 0 ≤ T) :
    3 + 150 * C * B ^ 4 * exp (H * B) +
        45 * (1 + 100 * C) * B ^ 7 * exp ((H + T) * B) ≤
      exp (((48 + 4650 * C) + (H + T) + 7) * B) := by
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hpow : B ^ 4 ≤ B ^ 7 := pow_le_pow_right₀ hB (by norm_num)
  have hpow1 : 1 ≤ B ^ 7 := one_le_pow₀ hB
  have hexp1 : 1 ≤ exp ((H + T) * B) :=
    one_le_exp (mul_nonneg (add_nonneg hH hT) hB0)
  have hexp : exp (H * B) ≤ exp ((H + T) * B) := by
    apply exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hT) hB0
  have hconst : (3 : ℝ) ≤ 3 * (B ^ 7 * exp ((H + T) * B)) := by
    have hprod : (1 : ℝ) ≤ B ^ 7 * exp ((H + T) * B) := by
      simpa using mul_le_mul hpow1 hexp1 zero_le_one (pow_nonneg hB0 7)
    nlinarith
  have hterm : 150 * C * B ^ 4 * exp (H * B) ≤
      150 * C * B ^ 7 * exp ((H + T) * B) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left hpow (by positivity)) hexp
      (exp_pos _).le (by positivity)
  calc
    _ ≤ 3 * (B ^ 7 * exp ((H + T) * B)) +
        150 * C * B ^ 7 * exp ((H + T) * B) +
        45 * (1 + 100 * C) * B ^ 7 * exp ((H + T) * B) :=
      add_le_add (add_le_add hconst hterm) le_rfl
    _ = (48 + 4650 * C) * B ^ 7 * exp ((H + T) * B) := by ring
    _ ≤ _ := polynomial_mul_exp_le_exp (by positivity) hB 7

/-- The full actual strip majorant has a universal band exponent and the sharp
imaginary-width exponent. Input spin and real radius occur only polynomially. -/
theorem canonicalRepairKernelStripSize_le_exp (B : ℝ) (hB : 1 ≤ B)
    (j jin : ℤ) (e R r : ℝ) (he : |(j : ℝ)| ≤ e) (hBe : B ≤ e)
    (hR : 0 ≤ R) (hr : 0 ≤ r) :
    canonicalRepairKernelStripSize B hB j jin e R r ≤
      e * inputColumnStripPolynomial jin R *
        exp (canonicalRepairKernelExponent * B + 4 * π * r * sqrt e) := by
  let P := inputColumnStripPolynomial jin R
  let X := exp (4 * π * r * sqrt e)
  let N : ℝ := Fintype.card (LowBandSpin B)
  let I := ‖correctedLowBandInverse (fun J : LowBandSpin B => (J : ℤ)) B‖
  let S := inputColumnStripSize (Fintype.card (LowBandSpin B)) jin B R r
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have he1 : 1 ≤ e := hB.trans hBe
  have he0 : 0 ≤ e := zero_le_one.trans he1
  have hC := correctedKernelBound_pos.le
  have hP : 0 ≤ P := (inputColumnStripPolynomial_pos jin R hR).le
  have hX : 0 ≤ X := (exp_pos _).le
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hI0 : 0 ≤ I := norm_nonneg _
  have hS0 : 0 ≤ S := inputColumnStripSize_nonneg _ jin B R r hB0 hR
  have hSmooth := correctedSmoothingBound_nonneg B hB0
  have hCol : S ≤ 15 * B ^ 2 * P * X :=
    canonicalInputColumnStripSize_le B hB jin e R r hBe hR hr
  have hInv : I ≤ exp (correctedLowBandCoercivityExponent * B) :=
    norm_correctedLowBandInverse_le_exp
      (fun J : LowBandSpin B => (J : ℤ)) (lowBandSpin_injective B) B hB
        (lowBandSpin_physical B)
  have hResponse : correctedKernelBound * (e * B + sqrt e * sqrt B) * sqrt N ≤
      10 * correctedKernelBound * e * B ^ 2 :=
    canonicalResponseStripCoefficient_le B hB e hBe
  have hThreshold : 3 * B * (1 + N * (correctedSmoothingBound B * sqrt N) * I) ≤
      3 * (1 + 100 * correctedKernelBound) * B ^ 5 *
        exp (correctedLowBandCoercivityExponent * B) :=
    canonicalInverseThresholdStripCoefficient_le B hB
  have hAnchor : |canonicalAnchorExteriorNumerator B hB j e| ≤
      e * exp (canonicalAnchorExteriorExponent * B) :=
    abs_canonicalAnchorExteriorNumerator_le_energy_mul_exp B hB j e he hBe
  have hpoint : P * (e + 2 * sqrt e) * X ≤ e * P * X * 3 := by
    have hs : sqrt e ≤ e := sqrt_le_self_iff.mpr (Or.inr he1)
    calc
      _ ≤ P * (e + 2 * e) * X := by gcongr
      _ = _ := by ring
  have hresponse : (correctedKernelBound * (e * B + sqrt e * sqrt B) * sqrt N) *
      (I * S) ≤ e * P * X * (150 * correctedKernelBound * B ^ 4 *
        exp (correctedLowBandCoercivityExponent * B)) := by
    calc
      _ ≤ (10 * correctedKernelBound * e * B ^ 2) *
          (exp (correctedLowBandCoercivityExponent * B) * (15 * B ^ 2 * P * X)) := by
        gcongr
      _ = _ := by ring
  have hthreshold : (3 * B * (1 + N * (correctedSmoothingBound B * sqrt N) * I) * S) *
      |canonicalAnchorExteriorNumerator B hB j e| ≤
      e * P * X * (45 * (1 + 100 * correctedKernelBound) * B ^ 7 *
        exp ((correctedLowBandCoercivityExponent + canonicalAnchorExteriorExponent) * B)) := by
    calc
      _ ≤ (3 * (1 + 100 * correctedKernelBound) * B ^ 5 *
          exp (correctedLowBandCoercivityExponent * B) * (15 * B ^ 2 * P * X)) *
            (e * exp (canonicalAnchorExteriorExponent * B)) := by gcongr
      _ = _ := by rw [add_mul, exp_add]; ring
  calc
    _ ≤ e * P * X * 3 +
        e * P * X * (150 * correctedKernelBound * B ^ 4 *
          exp (correctedLowBandCoercivityExponent * B)) +
        e * P * X * (45 * (1 + 100 * correctedKernelBound) * B ^ 7 *
          exp ((correctedLowBandCoercivityExponent + canonicalAnchorExteriorExponent) * B)) :=
      add_le_add (add_le_add hpoint hresponse) hthreshold
    _ = e * P * X * (3 + 150 * correctedKernelBound * B ^ 4 *
          exp (correctedLowBandCoercivityExponent * B) +
        45 * (1 + 100 * correctedKernelBound) * B ^ 7 *
          exp ((correctedLowBandCoercivityExponent + canonicalAnchorExteriorExponent) * B)) := by ring
    _ ≤ e * P * X * exp (canonicalRepairKernelExponent * B) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact exterior_polynomial_absorption hB hC
        correctedLowBandCoercivityExponent_pos.le canonicalAnchorExteriorExponent_pos.le
    _ = _ := by dsimp [P, X]; rw [exp_add]; ring

/-- A pointwise estimate for the actual entire exterior kernel, uniform in
all physical output spins and energies outside the repaired band. -/
theorem norm_canonicalRepairKernelHol_le_exp (B : ℝ) (hB : 1 ≤ B)
    (j jin : ℤ) (e R r : ℝ) (he : |(j : ℝ)| ≤ e) (hBe : B ≤ e)
    (hR : 0 ≤ R) (hr : 0 ≤ r) (z : ℂ) (hz : ‖z‖ ≤ R) (him : |z.im| ≤ r) :
    ‖canonicalRepairKernelHol B hB j jin e z‖ ≤
      e * inputColumnStripPolynomial jin R *
        exp (canonicalRepairKernelExponent * B + 4 * π * r * sqrt e) :=
  (norm_canonicalRepairKernelHol_strip_le B hB j jin e R r he hR hr z hz him).trans
    (canonicalRepairKernelStripSize_le_exp B hB j jin e R r he hBe hR hr)

/-- Real-centered disks retain the same sharp exponential rate. -/
theorem norm_canonicalRepairKernelHol_real_disk_le_exp (B : ℝ) (hB : 1 ≤ B)
    (j jin : ℤ) (e c r : ℝ) (he : |(j : ℝ)| ≤ e) (hBe : B ≤ e) (hr : 0 ≤ r)
    (z : ℂ) (hz : z ∈ Metric.closedBall (c : ℂ) r) :
    ‖canonicalRepairKernelHol B hB j jin e z‖ ≤
      e * inputColumnStripPolynomial jin (|c| + r) *
        exp (canonicalRepairKernelExponent * B + 4 * π * r * sqrt e) :=
  (norm_canonicalRepairKernelHol_real_disk_le B hB j jin e c r he hr z hz).trans
    (canonicalRepairKernelStripSize_le_exp B hB j jin e (|c| + r) r he hBe
      (by positivity) hr)

end GapFamily.Analytic
