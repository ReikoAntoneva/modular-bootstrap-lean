import BTZEntropy.Comparison.DensityErrorBand
import BTZEntropy.Comparison.DensityErrorTest

/-!
# Integrated density errors including every integer spin

The error is a numerator relative to the actual physical reference measure
`dE / sqrt (E^2 - j^2)`. A positive lower cutoff removes the scalar origin;
the proved reference-band bound still includes every nonzero-spin opening.
The descendant packet is arbitrary and its thermal bound is independent of
its size.
-/

noncomputable section

open Set MeasureTheory Real
open GapFamily.Analytic

namespace BTZEntropy.Comparison

/-- One spin row of the ordinary signed density error tested by a complete
finite descendant packet on an explicitly bounded physical band. -/
def densityErrorRow (φ : SmoothKernel) (E : ℝ) (F : Finset (ℕ × ℕ))
    (ε : ℤ → ℝ → ℝ) (lower : ℤ → ℝ) (V : ℝ) (j : ℤ) : ℝ :=
  ∫ e in Ioo (lower j) V, ε j e * primaryDescendantTest φ E F e ∂referenceMeasure j

/-- The actual compact-kernel convolution over the complete unprocessed
physical half-lines, summed over every integer spin. -/
def densityErrorFullPacket (φ : SmoothKernel) (E : ℝ) (F : Finset (ℕ × ℕ))
    (ε : ℤ → ℝ → ℝ) (lower : ℤ → ℝ) : ℝ :=
  ∑' j : ℤ, ∫ e in Ici (lower j),
    ε j e * primaryDescendantTest φ E F e ∂referenceMeasure j

/-- The all-integer-spin error for the same descendant packet and bands. -/
def densityErrorPacket (φ : SmoothKernel) (E : ℝ) (F : Finset (ℕ × ℕ))
    (ε : ℤ → ℝ → ℝ) (lower : ℤ → ℝ) (V : ℝ) : ℝ :=
  ∑' j : ℤ, densityErrorRow φ E F ε lower V j

private theorem densityError_integrand_bound (φ : SmoothKernel) (E R a M : ℝ)
    (F : Finset (ℕ × ℕ)) (ε : ℝ → ℝ) (L V : ℝ) (j : ℤ)
    (ha : 0 ≤ a) (hM : 0 ≤ M) (hL : 1 ≤ L)
    (hR : ∀ u, φ u ≠ 0 → u ≤ R)
    (hTest : ∀ e, 0 ≤ e → primaryDescendantTest φ E F e ≤ M)
    (hε : ∀ᵐ e ∂(referenceMeasure j).restrict (Ioo L V),
      |ε e| ≤ exp (7 * sqrt (a * e))) :
    ∀ᵐ e ∂(referenceMeasure j).restrict (Ioo L V),
      ‖ε e * primaryDescendantTest φ E F e‖ ≤
        exp (7 * sqrt (a * (E + R + 1 / 12))) * M := by
  filter_upwards [hε, ae_restrict_mem measurableSet_Ioo] with e hεe he
  have he0 : 0 ≤ e := by linarith [he.1]
  by_cases hzero : primaryDescendantTest φ E F e = 0
  · simp only [hzero, mul_zero, norm_zero]
    positivity
  have hsupport : e ≤ E + R + 1 / 12 := by
    by_contra hnot
    exact hzero (primaryDescendantTest_eq_zero_of_lt φ E R e F hR (lt_of_not_ge hnot))
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (primaryDescendantTest_nonneg φ E F e)]
  apply mul_le_mul
    (hεe.trans (exp_le_exp.mpr (mul_le_mul_of_nonneg_left
      (sqrt_le_sqrt (mul_le_mul_of_nonneg_left hsupport ha)) (by norm_num))))
    (hTest e he0) (primaryDescendantTest_nonneg φ E F e) (exp_pos _).le

/-- The density-error convolution is genuinely integrable on its finite
physical band; no totalized nonintegrable integral is used in the estimate. -/
theorem densityErrorRow_integrable (φ : SmoothKernel) (E R a M : ℝ)
    (F : Finset (ℕ × ℕ)) (ε : ℤ → ℝ → ℝ) (lower : ℤ → ℝ) (V : ℝ) (j : ℤ)
    (ha : 0 ≤ a) (hM : 0 ≤ M) (hL : 1 ≤ lower j) (hj : |(j : ℝ)| ≤ lower j)
    (hR : ∀ u, φ u ≠ 0 → u ≤ R)
    (hTest : ∀ e, 0 ≤ e → primaryDescendantTest φ E F e ≤ M)
    (hmeas : AEStronglyMeasurable (ε j) (referenceMeasure j))
    (hε : ∀ᵐ e ∂(referenceMeasure j).restrict (Ioo (lower j) V),
      |ε j e| ≤ exp (7 * sqrt (a * e))) :
    IntegrableOn (fun e => ε j e * primaryDescendantTest φ E F e)
      (Ioo (lower j) V) (referenceMeasure j) := by
  let _ := referenceBand_isFiniteMeasure j hL hj (V := V)
  exact Integrable.of_bound
    (hmeas.restrict.mul (continuous_primaryDescendantTest φ E F).aestronglyMeasurable)
    (exp (7 * sqrt (a * (E + R + 1 / 12))) * M)
    (densityError_integrand_bound φ E R a M F (ε j) (lower j) V j ha hM hL hR hTest hε)

/-- The full half-line integral is also genuinely integrable: compact
support makes its integrand the same finite-band integrable function. -/
theorem densityErrorFullRow_integrable (φ : SmoothKernel) (E R a M : ℝ)
    (F : Finset (ℕ × ℕ)) (ε : ℤ → ℝ → ℝ) (lower : ℤ → ℝ) (V : ℝ) (j : ℤ)
    (ha : 0 ≤ a) (hM : 0 ≤ M) (hL : 1 ≤ lower j) (hj : |(j : ℝ)| ≤ lower j)
    (hV : E + R + 1 / 12 < V) (hR : ∀ u, φ u ≠ 0 → u ≤ R)
    (hTest : ∀ e, 0 ≤ e → primaryDescendantTest φ E F e ≤ M)
    (hmeas : AEStronglyMeasurable (ε j) (referenceMeasure j))
    (hε : ∀ᵐ e ∂(referenceMeasure j).restrict (Ioo (lower j) V),
      |ε j e| ≤ exp (7 * sqrt (a * e))) :
    IntegrableOn (fun e => ε j e * primaryDescendantTest φ E F e)
      (Ici (lower j)) (referenceMeasure j) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  have hi := densityErrorRow_integrable φ E R a M F ε lower V j
    ha hM hL hj hR hTest hmeas hε
  have hset : Iio V ∩ Ioi (lower j) = Ioo (lower j) V := by
    ext e
    simp only [mem_inter_iff, mem_Iio, mem_Ioi, mem_Ioo, and_comm]
  have hi' : IntegrableOn (fun e => ε j e * primaryDescendantTest φ E F e)
      (Iio V) ((referenceMeasure j).restrict (Ioi (lower j))) := by
    simpa only [IntegrableOn, Measure.restrict_restrict measurableSet_Iio, hset] using hi
  have hind : Integrable
      ((Iio V).indicator (fun e => ε j e * primaryDescendantTest φ E F e))
      ((referenceMeasure j).restrict (Ioi (lower j))) :=
    (integrable_indicator_iff measurableSet_Iio).mpr hi'
  apply hind.congr
  exact Filter.Eventually.of_forall (fun e => by
    by_cases he : e < V
    · simp [he]
    · have hz := primaryDescendantTest_eq_zero_of_lt φ E R e F hR
        (hV.trans_le (le_of_not_gt he))
      simp [he, hz])

/-- The spin-opening singularity costs only the proved physical band mass. -/
theorem densityErrorRow_abs_le (φ : SmoothKernel) (E R a M : ℝ)
    (F : Finset (ℕ × ℕ)) (ε : ℤ → ℝ → ℝ) (lower : ℤ → ℝ) (V : ℝ) (j : ℤ)
    (ha : 0 ≤ a) (hM : 0 ≤ M) (hL : 1 ≤ lower j) (hj : |(j : ℝ)| ≤ lower j)
    (hV : 0 ≤ V) (hR : ∀ u, φ u ≠ 0 → u ≤ R)
    (hTest : ∀ e, 0 ≤ e → primaryDescendantTest φ E F e ≤ M)
    (hε : ∀ᵐ e ∂(referenceMeasure j).restrict (Ioo (lower j) V),
      |ε j e| ≤ exp (7 * sqrt (a * e))) :
    |densityErrorRow φ E F ε lower V j| ≤
      V * exp (7 * sqrt (a * (E + R + 1 / 12))) * M := by
  let _ := referenceBand_isFiniteMeasure j hL hj (V := V)
  have hb := norm_integral_le_of_norm_le_const
    (densityError_integrand_bound φ E R a M F (ε j) (lower j) V j ha hM hL hR hTest hε)
  change |densityErrorRow φ E F ε lower V j| ≤ _ at hb
  simp only [Measure.real, Measure.restrict_apply_univ] at hb
  calc
    _ ≤ (referenceMeasure j).real (Ioo (lower j) V) *
        (exp (7 * sqrt (a * (E + R + 1 / 12))) * M) := by simpa only [Measure.real, mul_comm, mul_left_comm, mul_assoc] using hb
    _ ≤ V * (exp (7 * sqrt (a * (E + R + 1 / 12))) * M) :=
      mul_le_mul_of_nonneg_right (referenceBand_mass_le j hL hj hV) (by positivity)
    _ = _ := by ring

/-- Compact support identifies the full half-line convolution with its
bounded band without an omitted high-energy or descendant tail. -/
theorem densityErrorFullPacket_eq_band (φ : SmoothKernel) (E R : ℝ)
    (F : Finset (ℕ × ℕ)) (ε : ℤ → ℝ → ℝ) (lower : ℤ → ℝ) (V : ℝ)
    (hR : ∀ u, φ u ≠ 0 → u ≤ R) (hV : E + R + 1 / 12 < V) :
    densityErrorFullPacket φ E F ε lower = densityErrorPacket φ E F ε lower V := by
  apply tsum_congr
  intro j
  rw [integral_Ici_eq_integral_Ioi]
  have heq := setIntegral_eq_integral_of_forall_compl_eq_zero
    (μ := (referenceMeasure j).restrict (Ioi (lower j))) (s := Iio V)
    (f := fun e => ε j e * primaryDescendantTest φ E F e) (fun e he => by
      have heV : V ≤ e := le_of_not_gt he
      rw [primaryDescendantTest_eq_zero_of_lt φ E R e F hR (hV.trans_le heV), mul_zero])
  rw [Measure.restrict_restrict measurableSet_Iio] at heq
  have hset : Iio V ∩ Ioi (lower j) = Ioo (lower j) V := by
    ext e
    simp only [mem_inter_iff, mem_Iio, mem_Ioi, mem_Ioo, and_comm]
  rw [hset] at heq
  exact heq.symm

/-- Only a finite integer-spin window can meet a bounded physical band. -/
theorem densityErrorPacket_eq_sum (φ : SmoothKernel) (E : ℝ) (F : Finset (ℕ × ℕ))
    (ε : ℤ → ℝ → ℝ) (lower : ℤ → ℝ) (V : ℝ) (N : ℕ)
    (hlower : ∀ j : ℤ, |(j : ℝ)| ≤ lower j) (hVN : V ≤ (N : ℝ)) :
    densityErrorPacket φ E F ε lower V =
      ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), densityErrorRow φ E F ε lower V j := by
  apply tsum_eq_sum
  intro j hj
  have hN : (N : ℝ) ≤ |(j : ℝ)| := by
    by_contra hnot
    have hab := abs_lt.mp (lt_of_not_ge hnot)
    apply hj
    rw [Finset.mem_Icc]
    constructor
    · exact (Int.cast_le (R := ℝ)).mp (by simpa using hab.1.le)
    · exact (Int.cast_le (R := ℝ)).mp (by simpa using hab.2.le)
  simp [densityErrorRow, Ioo_eq_empty_of_le (hVN.trans (hN.trans (hlower j)))]

/-- Uniform all-spin, all-descendant-packet density-error estimate. -/
theorem densityErrorPacket_abs_le (φ : SmoothKernel) (E R a M : ℝ)
    (F : Finset (ℕ × ℕ)) (ε : ℤ → ℝ → ℝ) (lower : ℤ → ℝ) (V : ℝ) (N : ℕ)
    (ha : 0 ≤ a) (hM : 0 ≤ M) (hL : ∀ j, 1 ≤ lower j)
    (hj : ∀ j : ℤ, |(j : ℝ)| ≤ lower j) (hV : 0 ≤ V) (hVN : V ≤ (N : ℝ))
    (hR : ∀ u, φ u ≠ 0 → u ≤ R)
    (hTest : ∀ e, 0 ≤ e → primaryDescendantTest φ E F e ≤ M)
    (hε : ∀ j, ∀ᵐ e ∂(referenceMeasure j).restrict (Ioo (lower j) V),
      |ε j e| ≤ exp (7 * sqrt (a * e))) :
    |densityErrorPacket φ E F ε lower V| ≤
      (2 * (N : ℝ) + 1) * V * exp (7 * sqrt (a * (E + R + 1 / 12))) * M := by
  rw [densityErrorPacket_eq_sum φ E F ε lower V N hj hVN]
  calc
    _ ≤ ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        |densityErrorRow φ E F ε lower V j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        V * exp (7 * sqrt (a * (E + R + 1 / 12))) * M := by
      exact Finset.sum_le_sum fun j _ =>
        densityErrorRow_abs_le φ E R a M F ε lower V j ha hM (hL j) (hj j)
          hV hR hTest (hε j)
    _ = _ := by rw [densityErrorBand_sum_const]; ring

/-- With the actual descendant estimate inserted, the only leading
exponential is the prescribed `7 sqrt (a E)` density-error envelope. -/
theorem densityErrorPacket_abs_le_sqrt (φ : SmoothKernel) (F : Finset (ℕ × ℕ))
    (ε : ℤ → ℝ → ℝ) (lower : ℤ → ℝ) {c x U R H a V : ℝ} (N : ℕ)
    (ha : 0 ≤ a) (hc : 1 ≤ c) (hx : x ≤ U) (hR0 : 0 ≤ R) (hH : 0 ≤ H)
    (hL : ∀ j, 1 ≤ lower j) (hj : ∀ j : ℤ, |(j : ℝ)| ≤ lower j)
    (hV : 0 ≤ V) (hVN : V ≤ (N : ℝ))
    (hR : ∀ u, φ u ≠ 0 → u ≤ R) (hφ : ∀ u, φ u ≤ H)
    (hε : ∀ j, ∀ᵐ e ∂(referenceMeasure j).restrict (Ioo (lower j) V),
      |ε j e| ≤ exp (7 * sqrt (a * e))) :
    |densityErrorPacket φ (x * c) F ε lower V| ≤
      (2 * (N : ℝ) + 1) * V * H *
        exp (7 * sqrt (a * (x * c + R + 1 / 12)) +
          (U + R + 1 / 12 + 4) * sqrt c) := by
  have h := densityErrorPacket_abs_le φ (x * c) R a
    (H * exp ((U + R + 1 / 12 + 4) * sqrt c)) F ε lower V N
    ha (by positivity) hL hj hV hVN hR
    (fun e he => primaryDescendantTest_le_sqrt φ F he hc hx hR0 hH hR hφ) hε
  convert h using 1
  rw [exp_add]
  ring

/-- A linear spin/energy cutoff produces only a quadratic prefactor. This
form is ready for the uniform exponential-advantage theorem. -/
theorem densityErrorPacket_abs_le_polynomial (φ : SmoothKernel)
    (F : Finset (ℕ × ℕ)) (ε : ℤ → ℝ → ℝ) (lower : ℤ → ℝ)
    {c x U R H a V Q : ℝ} (N : ℕ)
    (ha : 0 ≤ a) (hc : 1 ≤ c) (hx : x ≤ U) (hR0 : 0 ≤ R) (hH : 0 ≤ H)
    (hQ : 0 ≤ Q) (hL : ∀ j, 1 ≤ lower j)
    (hj : ∀ j : ℤ, |(j : ℝ)| ≤ lower j) (hV : 0 ≤ V) (hVN : V ≤ (N : ℝ))
    (hNQ : (N : ℝ) ≤ Q * (1 + c)) (hVQ : V ≤ Q * (1 + c))
    (hR : ∀ u, φ u ≠ 0 → u ≤ R) (hφ : ∀ u, φ u ≤ H)
    (hε : ∀ j, ∀ᵐ e ∂(referenceMeasure j).restrict (Ioo (lower j) V),
      |ε j e| ≤ exp (7 * sqrt (a * e))) :
    |densityErrorPacket φ (x * c) F ε lower V| ≤
      ((2 * Q + 1) * Q * H) * (1 + c) ^ 2 *
        exp (7 * sqrt (a * (x * c + R + 1 / 12)) +
          (U + R + 1 / 12 + 4) * sqrt c) := by
  have hspin : 2 * (N : ℝ) + 1 ≤ (2 * Q + 1) * (1 + c) := by nlinarith
  apply (densityErrorPacket_abs_le_sqrt φ F ε lower N ha hc hx hR0 hH
    hL hj hV hVN hR hφ hε).trans
  apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
  calc
    _ ≤ ((2 * Q + 1) * (1 + c)) * (Q * (1 + c)) * H :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hspin hVQ hV (by positivity)) hH
    _ = _ := by ring

/-- The natural kernel-support cutoff and its actual integer-spin ceiling
satisfy the required linear bounds, uniformly in a compact energy window. -/
theorem densityErrorFullPacket_abs_le_polynomial (φ : SmoothKernel)
    (F : Finset (ℕ × ℕ)) (ε : ℤ → ℝ → ℝ) (lower : ℤ → ℝ)
    {c x U R H a : ℝ} (ha : 0 ≤ a) (hc : 1 ≤ c) (hx0 : 0 ≤ x) (hx : x ≤ U)
    (hR0 : 0 ≤ R) (hH : 0 ≤ H) (hL : ∀ j, 1 ≤ lower j)
    (hj : ∀ j : ℤ, |(j : ℝ)| ≤ lower j)
    (hR : ∀ u, φ u ≠ 0 → u ≤ R) (hφ : ∀ u, φ u ≤ H)
    (hε : ∀ j, ∀ᵐ e ∂referenceMeasure j, lower j ≤ e →
      |ε j e| ≤ exp (7 * sqrt (a * e))) :
    |densityErrorFullPacket φ (x * c) F ε lower| ≤
      ((2 * (U + R + 3) + 1) * (U + R + 3) * H) * (1 + c) ^ 2 *
        exp (7 * sqrt (a * (x * c + R + 1 / 12)) +
          (U + R + 1 / 12 + 4) * sqrt c) := by
  let V : ℝ := x * c + R + 13 / 12
  let N : ℕ := ⌈V⌉₊
  have hc0 : 0 ≤ c := by linarith
  have hU : 0 ≤ U := hx0.trans hx
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hVN : V ≤ (N : ℝ) := Nat.le_ceil V
  have hNQ : (N : ℝ) ≤ (U + R + 3) * (1 + c) := by
    have hceil := (Nat.ceil_lt_add_one hV).le
    have hxc := mul_le_mul_of_nonneg_right hx hc0
    dsimp [N, V] at hceil ⊢
    nlinarith [mul_nonneg hR0 hc0, mul_nonneg hU hc0]
  rw [densityErrorFullPacket_eq_band φ (x * c) R F ε lower V hR
    (by dsimp [V]; linarith)]
  apply densityErrorPacket_abs_le_polynomial φ F ε lower N ha hc hx hR0 hH
    (by positivity) hL hj hV hVN hNQ (hVN.trans hNQ) hR hφ
  intro j
  filter_upwards [ae_restrict_of_ae (hε j), ae_restrict_mem measurableSet_Ioo] with e he heV
  exact he heV.1.le

end BTZEntropy.Comparison
