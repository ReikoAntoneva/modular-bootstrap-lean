import GapFamily.Analytic.Poincare.PoincareAnalytic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
Actual iterated real derivatives of a complex power on the positive real axis.
The estimates include order zero and every complex exponent.
-/

noncomputable section
namespace GapFamily.Analytic.PoincarePowerHigher

open Set Filter
open scoped Topology ContDiff

theorem contDiffAt_realPower {n : ℕ∞ω} (s : ℂ) {y : ℝ} (hy : 0 < y) :
    ContDiffAt ℝ n (fun t : ℝ => (t : ℂ) ^ s) y := by
  have hd : DifferentiableOn ℂ (fun z : ℂ => z ^ s) Complex.slitPlane :=
    fun z hz => (differentiableAt_id.cpow_const hz).differentiableWithinAt
  have ha : AnalyticAt ℂ (fun z : ℂ => z ^ s) (y : ℂ) :=
    hd.analyticAt (Complex.isOpen_slitPlane.mem_nhds (Or.inl hy))
  exact (ha.contDiffAt.restrict_scalars ℝ).comp y Complex.ofRealCLM.contDiff.contDiffAt

theorem contDiffOn_realPower {n : ℕ∞ω} (s : ℂ) :
    ContDiffOn ℝ n (fun y : ℝ => (y : ℂ) ^ s) (Ioi 0) :=
  fun _ hy => (contDiffAt_realPower s hy).contDiffWithinAt

theorem hasDerivAt_realPower (s : ℂ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => (t : ℂ) ^ s) (s * (y : ℂ) ^ (s - 1)) y :=
  (Complex.hasStrictDerivAt_cpow_const (c := s) (x := (y : ℂ))
    (Or.inl hy)).hasDerivAt.comp_ofReal

/-- The exact descending-Pochhammer derivative formula holds on the positive
real axis, without excluding zero or integer exponents. -/
theorem iteratedDeriv_realPower (n : ℕ) (s : ℂ) {y : ℝ} (hy : 0 < y) :
    iteratedDeriv n (fun t : ℝ => (t : ℂ) ^ s) y =
      (descPochhammer ℂ n).eval s * (y : ℂ) ^ (s - (n : ℂ)) := by
  induction n generalizing y with
  | zero => simp
  | succ n ih =>
      have he : iteratedDeriv n (fun t : ℝ => (t : ℂ) ^ s) =ᶠ[𝓝 y]
          (fun t : ℝ => (descPochhammer ℂ n).eval s * (t : ℂ) ^ (s - (n : ℂ))) := by
        filter_upwards [Ioi_mem_nhds hy] with t ht
        exact ih ht
      rw [iteratedDeriv_succ, he.deriv_eq,
        ((hasDerivAt_realPower (s - (n : ℂ)) hy).const_mul
          ((descPochhammer ℂ n).eval s)).deriv]
      rw [descPochhammer_eval_eq_prod_range, descPochhammer_eval_eq_prod_range,
        Finset.prod_range_succ]
      simp only [Nat.cast_add, Nat.cast_one]
      rw [show s - (n : ℂ) - 1 = s - ((n : ℂ) + 1) by ring]
      ring

/-- The falling-factorial coefficient is uniformly bounded on every parameter ball. -/
theorem norm_descPochhammer_le (n : ℕ) {s : ℂ} {S : ℝ} (hs : ‖s‖ ≤ S) :
    ‖(descPochhammer ℂ n).eval s‖ ≤ (S + (n : ℝ)) ^ n := by
  rw [descPochhammer_eval_eq_prod_range, norm_prod]
  calc
    _ ≤ ∏ _j ∈ Finset.range n, (S + (n : ℝ)) := by
      apply Finset.prod_le_prod₀ (fun j _ => norm_nonneg _)
      intro j hj
      calc
        ‖s - (j : ℂ)‖ ≤ ‖s‖ + ‖(j : ℂ)‖ := norm_sub_le _ _
        _ ≤ S + (n : ℝ) := by
          rw [Complex.norm_natCast]
          exact add_le_add hs (by exact_mod_cast (Finset.mem_range.mp hj).le)
    _ = _ := by simp

/-- The norm formula is for the actual real iterated Frechet derivative. -/
theorem norm_iteratedFDeriv_realPower (n : ℕ) (s : ℂ) {y : ℝ} (hy : 0 < y) :
    ‖iteratedFDeriv ℝ n (fun t : ℝ => (t : ℂ) ^ s) y‖ =
      ‖(descPochhammer ℂ n).eval s‖ * y ^ (s.re - (n : ℝ)) := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_realPower n s hy,
    norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
  simp only [Complex.sub_re, Complex.natCast_re]

/-- A single coefficient bound works for all positive heights; no lower
height bound is required. -/
theorem norm_iteratedFDeriv_realPower_le (n : ℕ) {s : ℂ} {S : ℝ}
    (hs : ‖s‖ ≤ S) {y : ℝ} (hy : 0 < y) :
    ‖iteratedFDeriv ℝ n (fun t : ℝ => (t : ℂ) ^ s) y‖ ≤
      (S + (n : ℝ)) ^ n * y ^ (s.re - (n : ℝ)) := by
  rw [norm_iteratedFDeriv_realPower n s hy]
  exact mul_le_mul_of_nonneg_right (norm_descPochhammer_le n hs)
    (Real.rpow_nonneg hy.le _)

end GapFamily.Analytic.PoincarePowerHigher
