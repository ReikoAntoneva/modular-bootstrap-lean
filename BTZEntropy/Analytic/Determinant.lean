import BTZEntropy.Coefficient
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Convergence of the boundary-graviton determinant

On the positive real inverse-temperature axis the level-two exponential sequence
is summable. Its logarithmic product therefore converges to a strictly positive
number. This identifies the determinant in `Coefficient` with an actual
convergent product and provides its logarithmic series.
-/

noncomputable section

open scoped BigOperators

namespace BTZEntropy

theorem summable_levelExponential {u : ℝ} (hu : 0 < u) (L : ℕ) :
    Summable (fun m : ℕ => Real.exp (-((m + L : ℕ) : ℝ) * u)) := by
  have h := Real.summable_exp_nat_mul_of_ge (neg_neg_of_pos hu)
    (f := fun m : ℕ => ((m + L : ℕ) : ℝ)) (fun m => by exact_mod_cast Nat.le_add_right m L)
  simpa only [neg_mul, mul_neg, mul_comm] using h

theorem levelFactor_pos {u : ℝ} (hu : 0 < u) {L : ℕ} (hL : 0 < L) (m : ℕ) :
    0 < 1 - Real.exp (-((m + L : ℕ) : ℝ) * u) := by
  apply sub_pos.mpr
  apply Real.exp_lt_one_iff.mpr
  have hm : (0 : ℝ) < ((m + L : ℕ) : ℝ) := by exact_mod_cast Nat.add_pos_right m hL
  nlinarith

theorem summable_log_levelFactor {u : ℝ} (hu : 0 < u) (L : ℕ) :
    Summable (fun m : ℕ => Real.log (1 - Real.exp (-((m + L : ℕ) : ℝ) * u))) := by
  simpa only [sub_eq_add_neg] using
    Real.summable_log_one_add_of_summable (summable_levelExponential hu L).neg

theorem hasProd_levelFactor {u : ℝ} (hu : 0 < u) {L : ℕ} (hL : 0 < L) :
    HasProd (fun m : ℕ => 1 - Real.exp (-((m + L : ℕ) : ℝ) * u))
      (Real.exp (∑' m : ℕ, Real.log (1 - Real.exp (-((m + L : ℕ) : ℝ) * u)))) :=
  Real.hasProd_of_hasSum_log (levelFactor_pos hu hL)
    (summable_log_levelFactor hu L).hasSum

theorem multipliable_levelFactor {u : ℝ} (hu : 0 < u) {L : ℕ} (hL : 0 < L) :
    Multipliable (fun m : ℕ => 1 - Real.exp (-((m + L : ℕ) : ℝ) * u)) :=
  (hasProd_levelFactor hu hL).multipliable

theorem tprod_levelFactor_pos {u : ℝ} (hu : 0 < u) {L : ℕ} (hL : 0 < L) :
    0 < ∏' m : ℕ, (1 - Real.exp (-((m + L : ℕ) : ℝ) * u)) := by
  rw [(hasProd_levelFactor hu hL).tprod_eq]
  exact Real.exp_pos _

theorem summable_boundaryExponential {u : ℝ} (hu : 0 < u) :
    Summable (fun m : ℕ => Real.exp (-((m + 2 : ℕ) : ℝ) * u)) := by
  exact summable_levelExponential hu 2

theorem boundaryExponential_lt_one {u : ℝ} (hu : 0 < u) (m : ℕ) :
    Real.exp (-((m + 2 : ℕ) : ℝ) * u) < 1 := by
  apply Real.exp_lt_one_iff.mpr
  have hm : (0 : ℝ) < ((m + 2 : ℕ) : ℝ) := by positivity
  nlinarith

theorem boundaryFactor_pos {u : ℝ} (hu : 0 < u) (m : ℕ) :
    0 < ((1 - Real.exp (-((m + 2 : ℕ) : ℝ) * u)) ^ 2)⁻¹ := by
  exact inv_pos.mpr (sq_pos_of_pos (sub_pos.mpr (boundaryExponential_lt_one hu m)))

theorem summable_log_boundaryBase {u : ℝ} (hu : 0 < u) :
    Summable (fun m : ℕ => Real.log (1 - Real.exp (-((m + 2 : ℕ) : ℝ) * u))) := by
  simpa only [sub_eq_add_neg] using
    Real.summable_log_one_add_of_summable (summable_boundaryExponential hu).neg

theorem summable_log_boundaryFactor {u : ℝ} (hu : 0 < u) :
    Summable (fun m : ℕ =>
      Real.log (((1 - Real.exp (-((m + 2 : ℕ) : ℝ) * u)) ^ 2)⁻¹)) := by
  simpa only [Real.log_inv, Real.log_pow, Nat.cast_ofNat, neg_mul] using
    (summable_log_boundaryBase hu).mul_left (-2)

theorem hasProd_boundaryFactor {u : ℝ} (hu : 0 < u) :
    HasProd (fun m : ℕ => ((1 - Real.exp (-((m + 2 : ℕ) : ℝ) * u)) ^ 2)⁻¹)
      (Real.exp (∑' m : ℕ,
        Real.log (((1 - Real.exp (-((m + 2 : ℕ) : ℝ) * u)) ^ 2)⁻¹))) :=
  Real.hasProd_of_hasSum_log (boundaryFactor_pos hu)
    (summable_log_boundaryFactor hu).hasSum

theorem multipliable_boundaryFactor {u : ℝ} (hu : 0 < u) :
    Multipliable (fun m : ℕ => ((1 - Real.exp (-((m + 2 : ℕ) : ℝ) * u)) ^ 2)⁻¹) :=
  (hasProd_boundaryFactor hu).multipliable

theorem boundaryGravitonFactor_eq_exp_tsum {u : ℝ} (hu : 0 < u) :
    boundaryGravitonFactor u = Real.exp (∑' m : ℕ,
      Real.log (((1 - Real.exp (-((m + 2 : ℕ) : ℝ) * u)) ^ 2)⁻¹)) :=
  (hasProd_boundaryFactor hu).tprod_eq

theorem boundaryGravitonFactor_pos {u : ℝ} (hu : 0 < u) :
    0 < boundaryGravitonFactor u := by
  rw [boundaryGravitonFactor_eq_exp_tsum hu]
  exact Real.exp_pos _

theorem boundaryGravitonFactor_ne_zero {u : ℝ} (hu : 0 < u) :
    boundaryGravitonFactor u ≠ 0 := ne_of_gt (boundaryGravitonFactor_pos hu)

theorem log_boundaryGravitonFactor {u : ℝ} (hu : 0 < u) :
    Real.log (boundaryGravitonFactor u) =
      -2 * ∑' m : ℕ, Real.log (1 - Real.exp (-((m + 2 : ℕ) : ℝ) * u)) := by
  rw [boundaryGravitonFactor_eq_exp_tsum hu, Real.log_exp]
  simp only [Real.log_inv, Real.log_pow, Nat.cast_ofNat]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro m
  ring

end BTZEntropy
