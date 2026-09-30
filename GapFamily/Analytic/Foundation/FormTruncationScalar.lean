import GapFamily.Analytic.Cusp.Profile.CuspProfileApproximationCutoff
import Mathlib.Analysis.Complex.RealDeriv

noncomputable section
namespace GapFamily.Analytic.FormTruncation

open Set Filter
open scoped Topology ContDiff

def scale (n : ℕ) : ℝ := (n : ℝ) + 2

theorem scale_ge_two (n : ℕ) : 2 ≤ scale n := by
  unfold scale
  have := Nat.cast_nonneg (α := ℝ) n
  linarith

theorem scale_pos (n : ℕ) : 0 < scale n :=
  lt_of_lt_of_le (by norm_num) (scale_ge_two n)

def highProfile (n : ℕ) (y : ℝ) : ℂ :=
  (Real.smoothTransition (y / scale n - 1) : ℂ)

def lowProfile (n : ℕ) (y : ℝ) : ℂ := 1 - highProfile n y

theorem highProfile_contDiff (n : ℕ) : ContDiff ℝ ∞ (highProfile n) := by
  unfold highProfile
  exact Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp
    ((contDiff_id.div_const _).sub contDiff_const))

theorem lowProfile_contDiff (n : ℕ) : ContDiff ℝ ∞ (lowProfile n) :=
  contDiff_const.sub (highProfile_contDiff n)

theorem highProfile_eq_zero_of_le (n : ℕ) {y : ℝ} (hy : y ≤ scale n) :
    highProfile n y = 0 := by
  have hd : y / scale n ≤ 1 := (div_le_one (scale_pos n)).mpr hy
  simp only [highProfile, Real.smoothTransition.zero_of_nonpos (by linarith :
    y / scale n - 1 ≤ 0), Complex.ofReal_zero]

theorem highProfile_eq_one_of_ge (n : ℕ) {y : ℝ} (hy : 2 * scale n ≤ y) :
    highProfile n y = 1 := by
  have hd : 2 ≤ y / scale n := (le_div_iff₀ (scale_pos n)).mpr hy
  simp only [highProfile, Real.smoothTransition.one_of_one_le (by linarith :
    1 ≤ y / scale n - 1), Complex.ofReal_one]

theorem highProfile_tsupport_subset_Ici (n : ℕ) :
    tsupport (highProfile n) ⊆ Ici (scale n) := by
  apply closure_minimal _ isClosed_Ici
  intro y hy
  by_contra hn
  exact hy (highProfile_eq_zero_of_le n (le_of_not_ge hn))

theorem highProfile_tsupport_subset (n : ℕ) : tsupport (highProfile n) ⊆ Ioi 1 := by
  intro y hy
  have h := highProfile_tsupport_subset_Ici n hy
  have := scale_ge_two n
  change 1 < y
  change scale n ≤ y at h
  linarith

theorem lowProfile_eq_one_of_le (n : ℕ) {y : ℝ} (hy : y ≤ scale n) :
    lowProfile n y = 1 := by
  rw [lowProfile, highProfile_eq_zero_of_le n hy, sub_zero]

theorem lowProfile_eq_zero_of_ge (n : ℕ) {y : ℝ} (hy : 2 * scale n ≤ y) :
    lowProfile n y = 0 := by
  rw [lowProfile, highProfile_eq_one_of_ge n hy, sub_self]

theorem norm_highProfile_le_one (n : ℕ) (y : ℝ) : ‖highProfile n y‖ ≤ 1 := by
  rw [highProfile, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.smoothTransition.nonneg _)]
  exact Real.smoothTransition.le_one _

theorem norm_lowProfile_le_one (n : ℕ) (y : ℝ) : ‖lowProfile n y‖ ≤ 1 := by
  have h0 := Real.smoothTransition.nonneg (y / scale n - 1)
  have h1 := Real.smoothTransition.le_one (y / scale n - 1)
  change ‖(1 : ℂ) - (Real.smoothTransition (y / scale n - 1) : ℂ)‖ ≤ 1
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by linarith : 0 ≤ 1 - Real.smoothTransition (y / scale n - 1))]
  linarith

theorem transition_deriv_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    deriv Real.smoothTransition x = 0 := by
  have hmin : IsLocalMin Real.smoothTransition x := by
    apply Filter.Eventually.of_forall
    intro y
    rw [Real.smoothTransition.zero_of_nonpos hx]
    exact Real.smoothTransition.nonneg y
  exact hmin.deriv_eq_zero

theorem transition_deriv_zero_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    deriv Real.smoothTransition x = 0 := by
  have hmax : IsLocalMax Real.smoothTransition x := by
    apply Filter.Eventually.of_forall
    intro y
    rw [Real.smoothTransition.one_of_one_le hx]
    exact Real.smoothTransition.le_one y
  exact hmax.deriv_eq_zero

theorem transition_deriv_bound :
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

theorem highProfile_deriv (n : ℕ) (y : ℝ) :
    deriv (highProfile n) y =
      ((deriv Real.smoothTransition (y / scale n - 1) * (1 / scale n) : ℝ) : ℂ) := by
  have hθ (x : ℝ) : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition x) x :=
    ((Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num) x).hasDerivAt
  have ha : HasDerivAt (fun t : ℝ => t / scale n - 1) (1 / scale n) y :=
    ((hasDerivAt_id y).div_const (scale n)).sub_const 1
  exact ((hθ _).comp y ha).ofReal_comp.deriv

theorem highProfile_deriv_zero_of_le (n : ℕ) {y : ℝ} (hy : y ≤ scale n) :
    deriv (highProfile n) y = 0 := by
  have hd : y / scale n ≤ 1 := (div_le_one (scale_pos n)).mpr hy
  rw [highProfile_deriv, transition_deriv_zero_of_nonpos (by linarith :
    y / scale n - 1 ≤ 0), zero_mul, Complex.ofReal_zero]

theorem highProfile_deriv_zero_of_ge (n : ℕ) {y : ℝ} (hy : 2 * scale n ≤ y) :
    deriv (highProfile n) y = 0 := by
  have hd : 2 ≤ y / scale n := (le_div_iff₀ (scale_pos n)).mpr hy
  rw [highProfile_deriv, transition_deriv_zero_of_one_le (by linarith :
    1 ≤ y / scale n - 1), zero_mul, Complex.ofReal_zero]

theorem highProfile_deriv_tsupport_subset (n : ℕ) :
    tsupport (deriv (highProfile n)) ⊆ Icc (scale n) (2 * scale n) := by
  apply closure_minimal _ isClosed_Icc
  intro y hy
  by_contra hn
  simp only [mem_Icc, not_and_or, not_le] at hn
  rcases hn with hl | hr
  · exact hy (highProfile_deriv_zero_of_le n hl.le)
  · exact hy (highProfile_deriv_zero_of_ge n hr.le)

theorem highProfile_weighted_deriv_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (y : ℝ), 0 < y →
      ‖(y : ℂ) * deriv (highProfile n) y‖ ≤ C := by
  obtain ⟨M, hM, hb⟩ := transition_deriv_bound
  refine ⟨2 * M, by positivity, fun n y hy => ?_⟩
  by_cases hlarge : 2 * scale n ≤ y
  · rw [highProfile_deriv_zero_of_ge n hlarge, mul_zero, norm_zero]
    positivity
  have hratio : y / scale n ≤ 2 := (div_le_iff₀ (scale_pos n)).mpr (le_of_not_ge hlarge)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy, highProfile_deriv,
    Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (one_div_pos.mpr (scale_pos n))]
  calc
    y * (|deriv Real.smoothTransition (y / scale n - 1)| * (1 / scale n)) =
        (y / scale n) * |deriv Real.smoothTransition (y / scale n - 1)| := by ring
    _ ≤ 2 * M := mul_le_mul hratio (hb _) (abs_nonneg _) (by norm_num)

theorem lowProfile_eventually_eq_one (y : ℝ) :
    ∀ᶠ n in atTop, lowProfile n =ᶠ[𝓝 y] (fun _ => 1) := by
  obtain ⟨N, hN⟩ := exists_nat_gt y
  filter_upwards [eventually_ge_atTop N] with n hn
  have hnR : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hy : y < scale n := by unfold scale; linarith
  filter_upwards [Iio_mem_nhds hy] with t ht
  exact lowProfile_eq_one_of_le n ht.le

theorem lowProfile_eventually_value_high_deriv (y : ℝ) :
    ∀ᶠ n in atTop, lowProfile n y = 1 ∧ deriv (highProfile n) y = 0 := by
  obtain ⟨N, hN⟩ := exists_nat_gt y
  filter_upwards [eventually_ge_atTop N] with n hn
  have hnR : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hy : y ≤ scale n := by unfold scale; linarith
  exact ⟨lowProfile_eq_one_of_le n hy, highProfile_deriv_zero_of_le n hy⟩

end GapFamily.Analytic.FormTruncation
