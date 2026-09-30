import BTZEntropy.Comparison.CosineReconstruction
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! Derivative bounds for the cosine pullback used in polynomial approximation. -/

noncomputable section

open Set
open scoped ContDiff Real

namespace BTZEntropy

/-- The smooth map from the real line onto the unit interval. -/
def cosineCoordinate (t : ℝ) : ℝ :=
  (1 + Real.cos (2 * Real.pi * t)) / 2

theorem cosineCoordinate_mem (t : ℝ) : cosineCoordinate t ∈ Icc (0 : ℝ) 1 := by
  dsimp [cosineCoordinate]
  constructor
  · linarith [Real.neg_one_le_cos (2 * Real.pi * t)]
  · linarith [Real.cos_le_one (2 * Real.pi * t)]

theorem cosineCoordinate_contDiff {m : WithTop ℕ∞} :
    ContDiff ℝ m cosineCoordinate := by
  exact (contDiff_const.add
    (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id))).div_const 2

/-- Every positive derivative of the cosine coordinate has a geometric bound. -/
theorem abs_iteratedDeriv_cosineCoordinate_le {n : ℕ} (hn : 0 < n) (x : ℝ) :
    |iteratedDeriv n cosineCoordinate x| ≤ (2 * Real.pi) ^ n := by
  change |iteratedDeriv n (fun t : ℝ => (1 + Real.cos (2 * Real.pi * t)) / 2) x| ≤ _
  rw [iteratedDeriv_div_const, iteratedDeriv_const_add hn,
    iteratedDeriv_comp_const_mul Real.contDiff_cos]
  rw [abs_div, abs_mul, abs_of_nonneg (pow_nonneg (by positivity) n)]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hpow : 0 ≤ (2 * Real.pi) ^ n := by positivity
  have hcos := mul_le_mul_of_nonneg_left
    (Real.abs_iteratedDeriv_cos_le_one n (2 * Real.pi * x)) hpow
  nlinarith

/-- A finite common derivative bound on `[0,1]` controls the real cosine pullback. -/
theorem norm_iteratedDeriv_real_cosineLine_le {h : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (n : ℕ) {C : ℝ}
    (hC : ∀ i ≤ n, ∀ x ∈ Icc (0 : ℝ) 1, ‖iteratedDeriv i h x‖ ≤ C)
    (t : ℝ) :
    ‖iteratedDeriv n (h ∘ cosineCoordinate) t‖ ≤ n.factorial * C * (2 * Real.pi) ^ n := by
  have hb := norm_iteratedFDeriv_comp_le hh
    (cosineCoordinate_contDiff (m := ∞)) (by simp : (n : WithTop ℕ∞) ≤ ∞) t
    (C := C) (D := 2 * Real.pi) ?_ ?_
  · simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using hb
  · intro i hi
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact hC i hi _ (cosineCoordinate_mem t)
  · intro i hi _
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
    exact abs_iteratedDeriv_cosineCoordinate_le hi t

/-- The complex cosine pullback satisfies the same derivative bound as the real one. -/
theorem norm_iteratedDeriv_cosineLine_le {h : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (n : ℕ) {C : ℝ}
    (hC : ∀ i ≤ n, ∀ x ∈ Icc (0 : ℝ) 1, ‖iteratedDeriv i h x‖ ≤ C)
    (t : ℝ) :
    ‖iteratedDeriv n (cosineLine h) t‖ ≤ n.factorial * C * (2 * Real.pi) ^ n := by
  have hi := Complex.ofRealLI.norm_iteratedFDeriv_comp_left (x := t)
    (hh.comp (cosineCoordinate_contDiff (m := ∞))).contDiffAt
    (by simp : (n : WithTop ℕ∞) ≤ ∞)
  have heq : ‖iteratedDeriv n (cosineLine h) t‖ =
      ‖iteratedDeriv n (h ∘ cosineCoordinate) t‖ := by
    change ‖iteratedDeriv n (fun x : ℝ => (h ((1 + Real.cos (2 * Real.pi * x)) / 2) : ℂ)) t‖ = _
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, cosineCoordinate,
      Function.comp_def, Complex.ofRealLI_apply] using hi
  rw [heq]
  exact norm_iteratedDeriv_real_cosineLine_le hh n hC t

end BTZEntropy
