import BTZEntropy.Analytic.LogTaylor
import BTZEntropy.Analytic.LogPolynomial
import BTZEntropy.Analytic.LogPolynomialTail
import BTZEntropy.Analytic.LogComparison

/-! Finite count expansions pass to the designated entropy coefficients.
All bounds include truncation order zero. -/

noncomputable section

open Polynomial
open scoped BigOperators

namespace BTZEntropy

/-- Count errors near one imply positivity and a uniform logarithm error. -/
theorem pos_and_abs_log_sub_log_one_add_le_four {N z : ℝ}
    (hz : |z| ≤ 1 / 2) (herr : |N - (1 + z)| ≤ 1 / 4) :
    0 < N ∧ |Real.log N - Real.log (1 + z)| ≤ 4 * |N - (1 + z)| := by
  have hbase : 1 / 2 ≤ 1 + z := by have := (abs_le.mp hz).1; linarith
  have hpos : 0 < 1 + z := by linarith
  have hratio : |N / (1 + z) - 1| ≤ 2 * |N - (1 + z)| := by
    rw [div_sub_one hpos.ne', abs_div, abs_of_pos hpos]
    apply (div_le_iff₀ hpos).2
    nlinarith [abs_nonneg (N - (1 + z))]
  have h := count_pos_and_log_error hpos (hratio.trans (by linarith))
  refine ⟨h.1, h.2.trans ?_⟩
  nlinarith

theorem abs_log_countCorrection_sub_logarithmPolynomial_le
    (u : ℕ → ℝ) (P : ℕ) {M ε : ℝ}
    (hM : 0 ≤ M) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hu : ∀ n, 1 ≤ n → n ≤ P → |u n| ≤ M)
    (hsmall : (P * M) * ε ≤ 1 / 2) :
    |Real.log (1 + (correctionPolynomial u P).eval ε) -
        (logarithmPolynomial u P).eval ε| ≤
      (2 * (P * M) ^ (P + 1)) * ε ^ (P + 1) := by
  rw [logarithmPolynomial_eval]
  apply abs_log_one_add_sub_sum_le_power ?_ hsmall
  rw [correctionPolynomial_eval]
  exact abs_count_correction_sum_le u P hM hε hε1 hu

/-- A count expansion with a genuine next-order error stays positive and
has the same finite logarithm polynomial to that order. -/
theorem pos_and_abs_log_count_sub_logarithmPolynomial_le
    (u : ℕ → ℝ) (P : ℕ) {M D ε N : ℝ}
    (hM : 0 ≤ M) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hu : ∀ n, 1 ≤ n → n ≤ P → |u n| ≤ M)
    (hsmall : (P * M) * ε ≤ 1 / 2)
    (herr : |N - (1 + (correctionPolynomial u P).eval ε)| ≤ D * ε ^ (P + 1))
    (hDsmall : D * ε ^ (P + 1) ≤ 1 / 4) :
    0 < N ∧ |Real.log N - (logarithmPolynomial u P).eval ε| ≤
      (4 * D + 2 * (P * M) ^ (P + 1)) * ε ^ (P + 1) := by
  have hz : |(correctionPolynomial u P).eval ε| ≤ 1 / 2 := by
    rw [correctionPolynomial_eval]
    exact (abs_count_correction_sum_le u P hM hε hε1 hu).trans hsmall
  have hlog := pos_and_abs_log_sub_log_one_add_le_four hz (herr.trans hDsmall)
  refine ⟨hlog.1, ?_⟩
  calc
    _ ≤ |Real.log N - Real.log (1 + (correctionPolynomial u P).eval ε)| +
        |Real.log (1 + (correctionPolynomial u P).eval ε) -
          (logarithmPolynomial u P).eval ε| := by
      simpa only [sub_add_sub_cancel] using abs_add_le
        (Real.log N - Real.log (1 + (correctionPolynomial u P).eval ε))
        (Real.log (1 + (correctionPolynomial u P).eval ε) -
          (logarithmPolynomial u P).eval ε)
    _ ≤ 4 * |N - (1 + (correctionPolynomial u P).eval ε)| +
        (2 * (P * M) ^ (P + 1)) * ε ^ (P + 1) :=
      add_le_add hlog.2
        (abs_log_countCorrection_sub_logarithmPolynomial_le u P hM hε hε1 hu hsmall)
    _ ≤ 4 * (D * ε ^ (P + 1)) +
        (2 * (P * M) ^ (P + 1)) * ε ^ (P + 1) := by
      gcongr
    _ = _ := by ring

/-- The finite algorithm in `Coefficient.lean` is the actual logarithmic
asymptotic coefficient sequence, with an explicit polynomial remainder. -/
theorem abs_log_countCorrection_sub_entropy_le
    (φ : ℝ → ℝ) (x : ℝ) (P : ℕ) {M ε : ℝ}
    (hM : 0 ≤ M) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hu : ∀ n, 1 ≤ n → n ≤ P → |saddleCountCoefficient φ x n| ≤ M)
    (hsmall : (P * M) * ε ≤ 1 / 2) :
    |Real.log (1 + (countCorrectionPolynomial φ x P).eval ε) -
        ∑ j ∈ Finset.range P, entropyCoefficient φ x (j + 1) * ε ^ (j + 1)| ≤
      (2 * (P * M) ^ (P + 1) +
        (logarithmPolynomial (saddleCountCoefficient φ x) P).sum (fun _ a => |a|)) *
          ε ^ (P + 1) := by
  have ht := abs_log_countCorrection_sub_logarithmPolynomial_le
    (saddleCountCoefficient φ x) P hM hε hε1 hu hsmall
  have hp := logarithmPolynomial_eval_sub_entropy_le φ x P (ε := ε)
    (by simpa only [abs_of_nonneg hε] using hε1)
  simp only [abs_of_nonneg hε] at hp
  change |Real.log (1 + (correctionPolynomial (saddleCountCoefficient φ x) P).eval ε) - _| ≤ _
  calc
    _ ≤ |Real.log (1 + (correctionPolynomial (saddleCountCoefficient φ x) P).eval ε) -
          (logarithmPolynomial (saddleCountCoefficient φ x) P).eval ε| +
        |(logarithmPolynomial (saddleCountCoefficient φ x) P).eval ε -
          ∑ j ∈ Finset.range P, entropyCoefficient φ x (j + 1) * ε ^ (j + 1)| := by
      simpa only [sub_add_sub_cancel] using abs_add_le
        (Real.log (1 + (correctionPolynomial (saddleCountCoefficient φ x) P).eval ε) -
          (logarithmPolynomial (saddleCountCoefficient φ x) P).eval ε)
        ((logarithmPolynomial (saddleCountCoefficient φ x) P).eval ε -
          ∑ j ∈ Finset.range P, entropyCoefficient φ x (j + 1) * ε ^ (j + 1))
    _ ≤ _ := by nlinarith [ht, hp]

/-- This remainder constant depends only on the finite coefficient bound and
the order, hence is uniform on any compact parameter set with that bound. -/
theorem abs_log_countCorrection_sub_entropy_uniform_le
    (φ : ℝ → ℝ) (x : ℝ) (P : ℕ) {M ε : ℝ}
    (hM : 0 ≤ M) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hu : ∀ n, 1 ≤ n → n ≤ P → |saddleCountCoefficient φ x n| ≤ M)
    (hsmall : (P * M) * ε ≤ 1 / 2) :
    |Real.log (1 + (countCorrectionPolynomial φ x P).eval ε) -
        ∑ j ∈ Finset.range P, entropyCoefficient φ x (j + 1) * ε ^ (j + 1)| ≤
      (2 * (P * M) ^ (P + 1) + logarithmPolynomialCoeffBound P M) * ε ^ (P + 1) := by
  refine (abs_log_countCorrection_sub_entropy_le φ x P hM hε hε1 hu hsmall).trans ?_
  exact mul_le_mul_of_nonneg_right
    (add_le_add le_rfl (logarithmPolynomialCoeffNorm_le (saddleCountCoefficient φ x) P M hu))
    (pow_nonneg hε _)

/-- A genuine finite count asymptotic gives a positive count and its
designated logarithmic asymptotic, uniformly under coefficient and error bounds. -/
theorem pos_and_abs_log_count_sub_entropy_uniform_le
    (φ : ℝ → ℝ) (x : ℝ) (P : ℕ) {M D ε N : ℝ}
    (hM : 0 ≤ M) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hu : ∀ n, 1 ≤ n → n ≤ P → |saddleCountCoefficient φ x n| ≤ M)
    (hsmall : (P * M) * ε ≤ 1 / 2)
    (herr : |N - (1 + (countCorrectionPolynomial φ x P).eval ε)| ≤ D * ε ^ (P + 1))
    (hDsmall : D * ε ^ (P + 1) ≤ 1 / 4) :
    0 < N ∧ |Real.log N -
        ∑ j ∈ Finset.range P, entropyCoefficient φ x (j + 1) * ε ^ (j + 1)| ≤
      (4 * D + 2 * (P * M) ^ (P + 1) + logarithmPolynomialCoeffBound P M) *
        ε ^ (P + 1) := by
  have ht := pos_and_abs_log_count_sub_logarithmPolynomial_le
    (saddleCountCoefficient φ x) P hM hε hε1 hu hsmall herr hDsmall
  have hp := logarithmPolynomial_eval_sub_entropy_uniform_le φ x P M hu (ε := ε)
    (by simpa only [abs_of_nonneg hε] using hε1)
  simp only [abs_of_nonneg hε] at hp
  refine ⟨ht.1, ?_⟩
  calc
    _ ≤ |Real.log N - (logarithmPolynomial (saddleCountCoefficient φ x) P).eval ε| +
        |(logarithmPolynomial (saddleCountCoefficient φ x) P).eval ε -
          ∑ j ∈ Finset.range P, entropyCoefficient φ x (j + 1) * ε ^ (j + 1)| := by
      simpa only [sub_add_sub_cancel] using abs_add_le
        (Real.log N - (logarithmPolynomial (saddleCountCoefficient φ x) P).eval ε)
        ((logarithmPolynomial (saddleCountCoefficient φ x) P).eval ε -
          ∑ j ∈ Finset.range P, entropyCoefficient φ x (j + 1) * ε ^ (j + 1))
    _ ≤ _ := by nlinarith [ht.2, hp]

/-- One common finite coefficient bound gives one radius and one remainder
constant for the entire parameter set, in particular every compact interval. -/
theorem uniform_log_countCorrection_expansion
    (φ : ℝ → ℝ) (S : Set ℝ) (P : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hu : ∀ x ∈ S, ∀ n, 1 ≤ n → n ≤ P → |saddleCountCoefficient φ x n| ≤ M) :
    ∃ C > 0, ∃ η > 0, ∀ x ∈ S, ∀ ε : ℝ, 0 ≤ ε → ε ≤ η →
      |Real.log (1 + (countCorrectionPolynomial φ x P).eval ε) -
          ∑ j ∈ Finset.range P, entropyCoefficient φ x (j + 1) * ε ^ (j + 1)| ≤
        C * ε ^ (P + 1) := by
  have hA : 0 ≤ (P : ℝ) * M := mul_nonneg (Nat.cast_nonneg P) hM
  have hden : 0 < 2 * (P * M + 1) := by positivity
  have hC := logarithmPolynomialCoeffBound_nonneg P hM
  refine ⟨1 + (2 * (P * M) ^ (P + 1) + logarithmPolynomialCoeffBound P M),
    by positivity, min 1 (1 / (2 * (P * M + 1))),
    lt_min (by norm_num) (one_div_pos.mpr hden), ?_⟩
  intro x hx ε hε hη
  have hε1 : ε ≤ 1 := hη.trans (min_le_left _ _)
  have hεdiv : ε ≤ 1 / (2 * (P * M + 1)) := hη.trans (min_le_right _ _)
  have hprod := (le_div_iff₀ hden).mp hεdiv
  have hsmall : (P * M) * ε ≤ 1 / 2 := by nlinarith
  refine (abs_log_countCorrection_sub_entropy_uniform_le φ x P hM hε hε1
    (hu x hx) hsmall).trans ?_
  exact mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hε _)

end BTZEntropy
