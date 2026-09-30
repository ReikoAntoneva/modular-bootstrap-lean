import GapFamily.Analytic.Foundation.FullVacuum
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The complete vacuum remainder estimate

The weak central arithmetic estimate and the denominator-at-least-two estimate
combine into the uniform bound required in C5. The scalar row is included.
-/

noncomputable section

namespace GapFamily.Analytic

open scoped Real

private theorem eventually_absorb_vacuum_remainder (C : ℝ) (hC : 0 < C) :
    ∃ T : ℝ, 0 < T ∧ ∀ x ≥ T,
      C * x * Real.exp (2 * π * Real.sqrt x) ≤
        Real.exp (7 * Real.sqrt x) / 4 := by
  have hgap : 2 * π < 7 := by
    have hpi := Real.pi_lt_d2
    linarith
  have hsmall := (isLittleO_exp_mul_rpow_of_lt 2 hgap).bound
    (show 0 < (1 / (4 * C) : ℝ) by positivity)
  have hsqrt := Real.tendsto_sqrt_atTop.eventually hsmall
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.1 hsqrt
  refine ⟨max 1 T, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro x hx
  have hx0 : 0 ≤ x :=
    le_trans (by norm_num) (le_trans (le_max_left _ _) hx)
  have h := hT x (le_trans (le_max_right _ _) hx)
  have hsq : (Real.sqrt x) ^ (2 : ℝ) = x := by
    rw [Real.rpow_two, Real.sq_sqrt hx0]
  simp only [Real.norm_eq_abs, hsq,
    abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hx0),
    abs_of_pos (Real.exp_pos _)] at h
  have hh := mul_le_mul_of_nonneg_left h hC.le
  calc
    C * x * Real.exp (2 * π * Real.sqrt x) =
        C * (Real.exp (2 * π * Real.sqrt x) * x) := by ring
    _ ≤ C * ((1 / (4 * C)) * Real.exp (7 * Real.sqrt x)) := hh
    _ = Real.exp (7 * Real.sqrt x) / 4 := by field_simp

/-- Both surviving central coefficients are controlled by the same arithmetic
constant, uniformly in the output spin. -/
theorem norm_vacuumCentralKernel_le (C : ℝ)
    (hC : ∀ j J : ℤ,
      ‖centralKernel j J‖ ≤ C * (|(j : ℝ)| * |(J : ℝ)|)) (j : ℤ) :
    ‖vacuumCentralKernel j‖ ≤ 2 * C * |(j : ℝ)| := by
  have hp : ‖centralKernel j 1‖ ≤ C * |(j : ℝ)| := by
    simpa using hC j 1
  have hm : ‖centralKernel j (-1)‖ ≤ C * |(j : ℝ)| := by
    simpa using hC j (-1)
  calc
    _ ≤ ‖centralKernel j 1‖ + ‖centralKernel j (-1)‖ := by
      simpa only [vacuumCentralKernel, norm_neg] using
        norm_sub_le (-centralKernel j 1) (centralKernel j (-1))
    _ ≤ C * |(j : ℝ)| + C * |(j : ℝ)| := add_le_add hp hm
    _ = _ := by ring

/-- The complete remainder explicitly retains its continued central term. -/
theorem norm_vacuumFullRemainder_le (C : ℝ)
    (hC : ∀ j J : ℤ,
      ‖centralKernel j J‖ ≤ C * (|(j : ℝ)| * |(J : ℝ)|))
    (a e : ℝ) (j : ℤ) (ha : 2 ≤ a) (he : |(j : ℝ)| ≤ e) :
    ‖vacuumFullRemainder a e j‖ ≤ 2 * C * |(j : ℝ)| +
      64 * π ^ 2 * (a * e) * Real.exp (2 * π * Real.sqrt (a * e)) := by
  rw [vacuumFullRemainder_eq_central_add_higher]
  exact (norm_add_le _ _).trans (add_le_add
    (norm_vacuumCentralKernel_le C hC j)
    (norm_vacuumHigherRemainder_le a e j ha he))

/-- C5's full vacuum estimate, with one constant for all physical spins and
all parameters `a ≥ 2`. It also holds below output energy one. -/
theorem exists_vacuumFullRemainder_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (a e : ℝ) (j : ℤ),
      2 ≤ a → |(j : ℝ)| ≤ e →
      ‖vacuumFullRemainder a e j‖ ≤
        C * (a * e) * Real.exp (2 * π * Real.sqrt (a * e)) := by
  obtain ⟨C, hC, hbound⟩ := exists_centralKernel_bound
  refine ⟨2 * C + 64 * π ^ 2, by positivity, ?_⟩
  intro a e j ha he
  have he0 : 0 ≤ e := (abs_nonneg _).trans he
  have hae : e ≤ a * e := by nlinarith
  have hexp : 1 ≤ Real.exp (2 * π * Real.sqrt (a * e)) :=
    Real.one_le_exp (by positivity)
  have hj : |(j : ℝ)| ≤ a * e * Real.exp (2 * π * Real.sqrt (a * e)) :=
    he.trans (hae.trans (by nlinarith [mul_nonneg (show 0 ≤ a by linarith) he0]))
  calc
    _ ≤ 2 * C * |(j : ℝ)| +
        64 * π ^ 2 * (a * e) * Real.exp (2 * π * Real.sqrt (a * e)) :=
      norm_vacuumFullRemainder_le C hbound a e j ha he
    _ ≤ 2 * C * (a * e * Real.exp (2 * π * Real.sqrt (a * e))) +
        64 * π ^ 2 * (a * e) * Real.exp (2 * π * Real.sqrt (a * e)) :=
      add_le_add (mul_le_mul_of_nonneg_left hj (show 0 ≤ 2 * C by positivity)) le_rfl
    _ = _ := by ring

/-- At sufficiently large energy product, the full vacuum error occupies only
one quarter of C5's envelope, uniformly in all physical spins. -/
theorem exists_vacuumFullRemainder_exp_bound :
    ∃ T : ℝ, 0 < T ∧ ∀ (a e : ℝ) (j : ℤ),
      2 ≤ a → |(j : ℝ)| ≤ e → T ≤ a * e →
      ‖vacuumFullRemainder a e j‖ ≤ Real.exp (7 * Real.sqrt (a * e)) / 4 := by
  obtain ⟨C, hC, hbound⟩ := exists_vacuumFullRemainder_bound
  obtain ⟨T, hT, hlarge⟩ := eventually_absorb_vacuum_remainder C hC
  exact ⟨T, hT, fun a e j ha he hae =>
    (hbound a e j ha he).trans (hlarge (a * e) hae)⟩

/-- A single sufficiently large vacuum parameter controls every physical output
with energy at least one; no spin-dependent threshold is introduced. -/
theorem exists_vacuumFullRemainder_uniform_exp_bound :
    ∃ A : ℝ, 2 ≤ A ∧ ∀ (a e : ℝ) (j : ℤ),
      A ≤ a → 1 ≤ e → |(j : ℝ)| ≤ e →
      ‖vacuumFullRemainder a e j‖ ≤ Real.exp (7 * Real.sqrt (a * e)) / 4 := by
  obtain ⟨T, hT, hbound⟩ := exists_vacuumFullRemainder_exp_bound
  refine ⟨max 2 T, le_max_left _ _, ?_⟩
  intro a e j ha he hj
  have ha2 : 2 ≤ a := (le_max_left _ _).trans ha
  have hTa : T ≤ a := (le_max_right _ _).trans ha
  exact hbound a e j ha2 hj (hTa.trans (by nlinarith))

/-- The complete higher series has an output-energy factor before taking the
scalar endpoint; its denominator sum contributes at most two. -/
theorem norm_vacuumHigherKernel_le (a e : ℝ) (j : ℤ)
    (ha : 2 ≤ a) (he : |(j : ℝ)| ≤ e) :
    ‖vacuumHigherKernel a e j‖ ≤
      64 * π ^ 2 * (a * e) * Real.exp (4 * π * Real.sqrt (a * e)) := by
  have he0 : 0 ≤ e := (abs_nonneg _).trans he
  have ha0 : 0 ≤ a := by linarith
  have hs : Summable (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) := by
    simpa only [Nat.cast_add, Nat.cast_one] using summable_one_div_nat_sq
  have ht : (∑' n : ℕ, (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) ≤ 2 := by
    simpa only [Nat.cast_add, Nat.cast_one] using tsum_one_div_nat_sq_le_two
  have hterm (n : ℕ) : ‖vacuumHigherTerm a e j n‖ ≤
      (32 * π ^ 2 * (a * e) * Real.exp (4 * π * Real.sqrt (a * e))) *
        (1 / ((n + 1 : ℕ) : ℝ) ^ 2) := by
    have hd : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have hexp : 4 * π * Real.sqrt (a * e) / ((n + 1 : ℕ) : ℝ) ≤
        4 * π * Real.sqrt (a * e) := by
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith [mul_nonneg (show 0 ≤ 4 * π * Real.sqrt (a * e) by positivity)
        (sub_nonneg.mpr hd)]
    calc
      _ ≤ 32 * π ^ 2 * (a * e / ((n + 1 : ℕ) : ℝ) ^ 2) *
          Real.exp (4 * π * Real.sqrt (a * e) / ((n + 1 : ℕ) : ℝ)) :=
        norm_vacuumHigherTerm_le a e j ha he n
      _ ≤ 32 * π ^ 2 * (a * e / ((n + 1 : ℕ) : ℝ) ^ 2) *
          Real.exp (4 * π * Real.sqrt (a * e)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by positivity)
      _ = _ := by ring
  rw [vacuumHigherKernel_eq_tsum]
  calc
    _ ≤ ∑' n : ℕ, ‖vacuumHigherTerm a e j n‖ :=
      norm_tsum_le_tsum_norm (summable_vacuumHigherTerm a e j).norm
    _ ≤ ∑' n : ℕ,
        (32 * π ^ 2 * (a * e) * Real.exp (4 * π * Real.sqrt (a * e))) *
          (1 / ((n + 1 : ℕ) : ℝ) ^ 2) :=
      Summable.tsum_le_tsum hterm (summable_vacuumHigherTerm a e j).norm
        (hs.mul_left _)
    _ = (32 * π ^ 2 * (a * e) * Real.exp (4 * π * Real.sqrt (a * e))) *
        (∑' n : ℕ, 1 / ((n + 1 : ℕ) : ℝ) ^ 2) := tsum_mul_left
    _ ≤ (32 * π ^ 2 * (a * e) * Real.exp (4 * π * Real.sqrt (a * e))) * 2 :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    _ = _ := by ring

/-- The full scalar vacuum has a quantitative linear zero at the endpoint. -/
theorem norm_vacuumFullKernel_scalar_le (a e : ℝ)
    (ha : 2 ≤ a) (he : 0 ≤ e) :
    ‖vacuumFullKernel a e 0‖ ≤
      64 * π ^ 2 * (a * e) * Real.exp (4 * π * Real.sqrt (a * e)) := by
  rw [vacuumFullKernel_scalar_eq_higher]
  exact norm_vacuumHigherKernel_le a e 0 ha (by simpa using he)

/-- An explicit scalar `O(e)` bound throughout each fixed compact energy band. -/
theorem norm_vacuumFullKernel_scalar_on_band_le (a B e : ℝ)
    (ha : 2 ≤ a) (he : 0 ≤ e) (heB : e ≤ B) :
    ‖vacuumFullKernel a e 0‖ ≤
      (64 * π ^ 2 * a * Real.exp (4 * π * Real.sqrt (a * B))) * e := by
  have ha0 : 0 ≤ a := by linarith
  calc
    _ ≤ 64 * π ^ 2 * (a * e) * Real.exp (4 * π * Real.sqrt (a * e)) :=
      norm_vacuumFullKernel_scalar_le a e ha he
    _ ≤ 64 * π ^ 2 * (a * e) * Real.exp (4 * π * Real.sqrt (a * B)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left heB ha0)) (by positivity)
    _ = _ := by ring

end GapFamily.Analytic
