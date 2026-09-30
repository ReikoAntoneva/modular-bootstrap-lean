import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Smooth cutoffs for cusp profile approximation

The lower transition stays away from height one, while the upper transition
moves to infinity. The derivative bound separates the boundary collar from
the weighted cusp tail.
-/

noncomputable section
namespace GapFamily.Analytic

open Set Filter
open scoped Topology ContDiff

/-- The positive scale used by the two transitions. -/
def cuspProfileCutoffScale (n : ℕ) : ℝ := (n : ℝ) + 2

theorem cuspProfileCutoffScale_ge_two (n : ℕ) : 2 ≤ cuspProfileCutoffScale n := by
  unfold cuspProfileCutoffScale
  have := Nat.cast_nonneg (α := ℝ) n
  linarith

theorem cuspProfileCutoffScale_pos (n : ℕ) : 0 < cuspProfileCutoffScale n :=
  lt_of_lt_of_le (by norm_num) (cuspProfileCutoffScale_ge_two n)

/-- A smooth real cutoff supported strictly above height one. -/
def cuspProfileCutoff (n : ℕ) (y : ℝ) : ℝ :=
  Real.smoothTransition (cuspProfileCutoffScale n * (y - 1) - 1) *
    Real.smoothTransition (2 - y / cuspProfileCutoffScale n)

theorem cuspProfileCutoff_contDiff (n : ℕ) : ContDiff ℝ ∞ (cuspProfileCutoff n) := by
  unfold cuspProfileCutoff
  fun_prop

theorem cuspProfileCutoff_nonneg (n : ℕ) (y : ℝ) : 0 ≤ cuspProfileCutoff n y :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem cuspProfileCutoff_le_one (n : ℕ) (y : ℝ) : cuspProfileCutoff n y ≤ 1 := by
  unfold cuspProfileCutoff
  calc
    _ ≤ 1 * Real.smoothTransition (2 - y / cuspProfileCutoffScale n) :=
      mul_le_mul_of_nonneg_right (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
    _ ≤ 1 := by simpa using Real.smoothTransition.le_one (2 - y / cuspProfileCutoffScale n)

theorem cuspProfileCutoff_tsupport_subset_Icc (n : ℕ) :
    tsupport (cuspProfileCutoff n) ⊆
      Icc (1 + 1 / cuspProfileCutoffScale n) (2 * cuspProfileCutoffScale n) := by
  apply closure_minimal _ isClosed_Icc
  intro y hy
  change cuspProfileCutoff n y ≠ 0 at hy
  have hk := cuspProfileCutoffScale_pos n
  constructor
  · by_contra h
    have hlt : y - 1 < 1 / cuspProfileCutoffScale n := by linarith
    have hmul := (lt_div_iff₀ hk).mp hlt
    exact hy (by
      unfold cuspProfileCutoff
      rw [Real.smoothTransition.zero_of_nonpos (by nlinarith :
        cuspProfileCutoffScale n * (y - 1) - 1 ≤ 0), zero_mul])
  · by_contra h
    have hdiv : 2 ≤ y / cuspProfileCutoffScale n := (le_div_iff₀ hk).mpr (by linarith)
    exact hy (by
      unfold cuspProfileCutoff
      rw [Real.smoothTransition.zero_of_nonpos (by linarith :
        2 - y / cuspProfileCutoffScale n ≤ 0), mul_zero])

theorem cuspProfileCutoff_hasCompactSupport (n : ℕ) : HasCompactSupport (cuspProfileCutoff n) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (cuspProfileCutoff_tsupport_subset_Icc n)

theorem cuspProfileCutoff_tsupport_subset (n : ℕ) : tsupport (cuspProfileCutoff n) ⊆ Ioi 1 := by
  intro y hy
  have hlow := (cuspProfileCutoff_tsupport_subset_Icc n hy).1
  have := one_div_pos.mpr (cuspProfileCutoffScale_pos n)
  change 1 < y
  linarith

theorem cuspProfileCutoff_eq_one_of (n : ℕ) {y : ℝ}
    (hl : 2 ≤ cuspProfileCutoffScale n * (y - 1)) (hu : y ≤ cuspProfileCutoffScale n) :
    cuspProfileCutoff n y = 1 := by
  have hdiv : y / cuspProfileCutoffScale n ≤ 1 :=
    (div_le_one (cuspProfileCutoffScale_pos n)).mpr hu
  unfold cuspProfileCutoff
  rw [Real.smoothTransition.one_of_one_le (by linarith :
    1 ≤ cuspProfileCutoffScale n * (y - 1) - 1),
    Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 2 - y / cuspProfileCutoffScale n),
    one_mul]

/-- At every interior height the cutoff eventually equals one on a neighborhood. -/
theorem cuspProfileCutoff_eventually_eq_one {y : ℝ} (hy : 1 < y) :
    ∀ᶠ n in atTop, cuspProfileCutoff n =ᶠ[𝓝 y] (fun _ => 1) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max (2 / (y - 1)) y)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hnR : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hk : max (2 / (y - 1)) y < cuspProfileCutoffScale n := by
    unfold cuspProfileCutoffScale
    linarith
  have hl : 2 < cuspProfileCutoffScale n * (y - 1) :=
    (div_lt_iff₀ (sub_pos.mpr hy)).mp ((le_max_left _ _).trans_lt hk)
  have hu : y < cuspProfileCutoffScale n := (le_max_right _ _).trans_lt hk
  have hloc : ∀ᶠ t in 𝓝 y, 2 < cuspProfileCutoffScale n * (t - 1) :=
    (isOpen_lt continuous_const (continuous_const.mul (continuous_id.sub continuous_const))).mem_nhds hl
  filter_upwards [hloc, Iio_mem_nhds hu] with t ht ht'
  exact cuspProfileCutoff_eq_one_of n ht.le ht'.le

/-- In particular the value and derivative eventually have their constant values. -/
theorem cuspProfileCutoff_eventually_value_deriv {y : ℝ} (hy : 1 < y) :
    ∀ᶠ n in atTop, cuspProfileCutoff n y = 1 ∧ deriv (cuspProfileCutoff n) y = 0 := by
  filter_upwards [cuspProfileCutoff_eventually_eq_one hy] with n hn
  exact ⟨hn.eq_of_nhds, by rw [hn.deriv_eq]; simp⟩

/-- The two literal transition derivatives in the cutoff product rule. -/
theorem cuspProfileCutoff_deriv (n : ℕ) (y : ℝ) :
    deriv (cuspProfileCutoff n) y =
      deriv Real.smoothTransition (cuspProfileCutoffScale n * (y - 1) - 1) *
        cuspProfileCutoffScale n * Real.smoothTransition (2 - y / cuspProfileCutoffScale n) +
      Real.smoothTransition (cuspProfileCutoffScale n * (y - 1) - 1) *
        (deriv Real.smoothTransition (2 - y / cuspProfileCutoffScale n) *
          (-(1 / cuspProfileCutoffScale n))) := by
  have hθ (x : ℝ) : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition x) x :=
    ((Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num) x).hasDerivAt
  have hl : HasDerivAt (fun t : ℝ => cuspProfileCutoffScale n * (t - 1) - 1)
      (cuspProfileCutoffScale n) y := by
    simpa using (((hasDerivAt_id y).sub_const 1).const_mul (cuspProfileCutoffScale n)).sub_const 1
  have hu : HasDerivAt (fun t : ℝ => 2 - t / cuspProfileCutoffScale n)
      (-(1 / cuspProfileCutoffScale n)) y :=
    ((hasDerivAt_id y).div_const (cuspProfileCutoffScale n)).const_sub 2
  exact ((hθ _ |>.comp y hl).mul (hθ _ |>.comp y hu)).deriv

private theorem transition_deriv_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    deriv Real.smoothTransition x = 0 := by
  have hmin : IsLocalMin Real.smoothTransition x := by
    apply Filter.Eventually.of_forall
    intro y
    rw [Real.smoothTransition.zero_of_nonpos hx]
    exact Real.smoothTransition.nonneg y
  exact hmin.deriv_eq_zero

private theorem transition_deriv_zero_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    deriv Real.smoothTransition x = 0 := by
  have hmax : IsLocalMax Real.smoothTransition x := by
    apply Filter.Eventually.of_forall
    intro y
    rw [Real.smoothTransition.one_of_one_le hx]
    exact Real.smoothTransition.le_one y
  exact hmax.deriv_eq_zero

private theorem transition_deriv_bound :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |deriv Real.smoothTransition x| ≤ M := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    Real.smoothTransition.contDiff.continuous_deriv_one
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc.continuousOn
    (s := Icc (0 : ℝ) 1)
  refine ⟨max M 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx0 : x ≤ 0
  · rw [transition_deriv_zero_of_nonpos hx0, abs_zero]
    exact le_max_right _ _
  by_cases hx1 : 1 ≤ x
  · rw [transition_deriv_zero_of_one_le hx1, abs_zero]
    exact le_max_right _ _
  exact (hM x ⟨le_of_not_ge hx0, le_of_not_ge hx1⟩).trans (le_max_left _ _)

/-- One uniform constant controls the derivative separately in the boundary collar
and in the weighted cusp tail. -/
theorem cuspProfileCutoff_deriv_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (y : ℝ), 1 < y →
      ‖deriv (cuspProfileCutoff n) y‖ ≤ if y ≤ 2 then C / (y - 1) else C / y := by
  obtain ⟨M, hM, hb⟩ := transition_deriv_bound
  refine ⟨2 * M, by positivity, fun n y hy => ?_⟩
  have hk := cuspProfileCutoffScale_pos n
  have hk2 := cuspProfileCutoffScale_ge_two n
  have hypos : 0 < y := lt_trans zero_lt_one hy
  have hym : 0 < y - 1 := sub_pos.mpr hy
  by_cases hy2 : y ≤ 2
  · rw [ite_eq_left hy2]
    have hup : 1 ≤ 2 - y / cuspProfileCutoffScale n := by
      have hdiv : y / cuspProfileCutoffScale n ≤ 1 := (div_le_one hk).mpr (hy2.trans hk2)
      linarith
    rw [cuspProfileCutoff_deriv, Real.smoothTransition.one_of_one_le hup,
      transition_deriv_zero_of_one_le hup, mul_one, zero_mul, mul_zero, add_zero,
      Real.norm_eq_abs, abs_mul, abs_of_pos hk]
    by_cases hlow : 1 ≤ cuspProfileCutoffScale n * (y - 1) - 1
    · rw [transition_deriv_zero_of_one_le hlow, abs_zero, zero_mul]
      positivity
    · have hscale : cuspProfileCutoffScale n ≤ 2 / (y - 1) :=
        (le_div_iff₀ hym).mpr (by linarith)
      calc
        _ ≤ M * cuspProfileCutoffScale n := mul_le_mul_of_nonneg_right (hb _) hk.le
        _ ≤ M * (2 / (y - 1)) := mul_le_mul_of_nonneg_left hscale hM
        _ = _ := by ring
  · rw [ite_eq_right hy2]
    have hlow : 1 ≤ cuspProfileCutoffScale n * (y - 1) - 1 := by nlinarith
    rw [cuspProfileCutoff_deriv, Real.smoothTransition.one_of_one_le hlow,
      transition_deriv_zero_of_one_le hlow, zero_mul, zero_mul, zero_add, one_mul,
      Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos (one_div_pos.mpr hk)]
    by_cases hup : 2 - y / cuspProfileCutoffScale n ≤ 0
    · rw [transition_deriv_zero_of_nonpos hup, abs_zero, zero_mul]
      positivity
    · have hdiv : y / cuspProfileCutoffScale n < 2 := by linarith
      have hmul := (div_lt_iff₀ hk).mp hdiv
      have hscale : 1 / cuspProfileCutoffScale n ≤ 2 / y :=
        (div_le_div_iff₀ hk hypos).mpr (by nlinarith)
      calc
        _ ≤ M * (1 / cuspProfileCutoffScale n) :=
          mul_le_mul_of_nonneg_right (hb _) (one_div_nonneg.mpr hk.le)
        _ ≤ M * (2 / y) := mul_le_mul_of_nonneg_left hscale hM
        _ = _ := by ring

end GapFamily.Analytic
