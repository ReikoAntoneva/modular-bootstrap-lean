import GapFamily.Analytic.Foundation.LatticeHeight
import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# The determinant-one lattice theta series

The series uses the same actual lattice energy as the scalar Poincaré lattice
bridge. All summability and continuity statements require positive real time.
-/

noncomputable section

namespace GapFamily.Analytic

open Filter Set
open scoped Real Topology MatrixGroups

/-- The Gaussian attached to an integer row of the actual modular lattice. -/
def latticeThetaTerm (z : UpperHalfPlane) (t : ℝ) (v : Fin 2 → ℤ) : ℝ :=
  Real.exp (-Real.pi * t * latticeEnergy z v)

/-- The nonholomorphic rank-two theta function of the determinant-one lattice. -/
def latticeTheta (z : UpperHalfPlane) (t : ℝ) : ℝ :=
  ∑' v : Fin 2 → ℤ, latticeThetaTerm z t v

/-- Full modular invariance is a reindexing of the actual integer lattice. -/
theorem latticeTheta_smul (g : SL(2, ℤ)) (z : UpperHalfPlane) (t : ℝ) :
    latticeTheta (g • z) t = latticeTheta z t := by
  simp only [latticeTheta, latticeThetaTerm, latticeEnergy_smul_eq]
  exact (latticeRowEquiv g).tsum_eq (fun v => Real.exp (-Real.pi * t * latticeEnergy z v))

@[simp] theorem latticeThetaTerm_zero (z : UpperHalfPlane) (t : ℝ) :
    latticeThetaTerm z t 0 = 1 := by simp [latticeThetaTerm]

theorem latticeThetaTerm_pos (z : UpperHalfPlane) (t : ℝ) (v : Fin 2 → ℤ) :
    0 < latticeThetaTerm z t v := Real.exp_pos _

/-- The one-dimensional Gaussian bound already proved for Jacobi theta. -/
theorem summable_gaussian_int {a : ℝ} (ha : 0 < a) :
    Summable (fun n : ℤ => Real.exp (-Real.pi * a * (n : ℝ) ^ 2)) := by
  simpa only [pow_zero, one_mul, mul_zero, zero_mul, sub_zero, mul_assoc]
    using summable_pow_mul_jacobiTheta₂_term_bound 0 ha 0

private theorem summable_gaussian_finTwo {a : ℝ} (ha : 0 < a) :
    Summable (fun v : Fin 2 → ℤ =>
      Real.exp (-Real.pi * a * ((v 0 : ℝ) ^ 2 + (v 1 : ℝ) ^ 2))) := by
  have hs := summable_gaussian_int ha
  have hprod := hs.mul_of_nonneg hs (fun n => (Real.exp_pos _).le) (fun n => (Real.exp_pos _).le)
  have h := hprod.comp_injective (finTwoArrowEquiv ℤ).injective
  simpa [Real.exp_add, mul_add, Function.comp_def, finTwoArrowEquiv, piFinTwoEquiv] using h

private theorem lattice_coordinate_sq_le (v : Fin 2 → ℤ) :
    (v 0 : ℝ) ^ 2 + (v 1 : ℝ) ^ 2 ≤ 2 * ‖v‖ ^ 2 := by
  have h0 : |(v 0 : ℝ)| ≤ ‖v‖ := by
    simpa only [← Int.norm_cast_real, Real.norm_eq_abs] using norm_le_pi_norm v 0
  have h1 : |(v 1 : ℝ)| ≤ ‖v‖ := by
    simpa only [← Int.norm_cast_real, Real.norm_eq_abs] using norm_le_pi_norm v 1
  have h0' := pow_le_pow_left₀ (abs_nonneg (v 0 : ℝ)) h0 2
  have h1' := pow_le_pow_left₀ (abs_nonneg (v 1 : ℝ)) h1 2
  rw [sq_abs] at h0' h1'
  linarith

/-- The determinant-one quadratic form controls a positive multiple of the coordinate squares. -/
theorem latticeEnergy_coordinate_lower (z : UpperHalfPlane) (v : Fin 2 → ℤ) :
    ((EisensteinSeries.r z) ^ 2 / z.im / 2) *
      ((v 0 : ℝ) ^ 2 + (v 1 : ℝ) ^ 2) ≤ latticeEnergy z v := by
  apply le_trans _ (latticeEnergy_norm_lower z v)
  have hc : 0 ≤ (EisensteinSeries.r z) ^ 2 / z.im / 2 := by positivity
  have h := mul_le_mul_of_nonneg_left (lattice_coordinate_sq_le v) hc
  convert h using 1
  ring

/-- Genuine absolute convergence for every lattice and positive theta time. -/
theorem summable_latticeThetaTerm (z : UpperHalfPlane) {t : ℝ} (ht : 0 < t) :
    Summable (latticeThetaTerm z t) := by
  have hc : 0 < t * ((EisensteinSeries.r z) ^ 2 / z.im / 2) := by
    exact mul_pos ht (div_pos (div_pos (sq_pos_of_pos (EisensteinSeries.r_pos z)) z.im_pos)
      (by norm_num))
  apply (summable_gaussian_finTwo hc).of_nonneg_of_le
    (fun v => (latticeThetaTerm_pos z t v).le)
  intro v
  unfold latticeThetaTerm
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left (latticeEnergy_coordinate_lower z v)
    (mul_nonneg Real.pi_pos.le ht.le)
  nlinarith

/-- The theta definition is certified by its actual convergent series. -/
theorem latticeTheta_hasSum (z : UpperHalfPlane) {t : ℝ} (ht : 0 < t) :
    HasSum (latticeThetaTerm z t) (latticeTheta z t) :=
  (summable_latticeThetaTerm z ht).hasSum

/-- Positive times bounded away from zero have one summable uniform majorant. -/
theorem latticeThetaTerm_le_of_le (z : UpperHalfPlane) {a t : ℝ} (hat : a ≤ t)
    (v : Fin 2 → ℤ) : latticeThetaTerm z t v ≤ latticeThetaTerm z a v := by
  unfold latticeThetaTerm
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_right hat (latticeEnergy_nonneg z v)
  nlinarith [Real.pi_pos]

/-- Uniform convergence on an entire positive-time half-line. -/
theorem latticeTheta_tendstoUniformlyOn_Ici (z : UpperHalfPlane) {a : ℝ} (ha : 0 < a) :
    TendstoUniformlyOn
      (fun F : Finset (Fin 2 → ℤ) => fun t => ∑ v ∈ F, latticeThetaTerm z t v)
      (latticeTheta z) atTop (Ici a) := by
  apply tendstoUniformlyOn_tsum (summable_latticeThetaTerm z ha)
  intro v t ht
  simpa only [Real.norm_of_nonneg (latticeThetaTerm_pos z t v).le] using
    latticeThetaTerm_le_of_le z ht v

/-- Ordinary continuity supplies the local integrability input for the Mellin argument. -/
theorem continuousOn_latticeTheta (z : UpperHalfPlane) :
    ContinuousOn (latticeTheta z) (Ioi 0) := by
  intro t ht
  change 0 < t at ht
  have ha : 0 < t / 2 := by linarith
  have hc : ContinuousOn (latticeTheta z) (Ici (t / 2)) := by
    apply (latticeTheta_tendstoUniformlyOn_Ici z ha).continuousOn
    exact Filter.Frequently.of_forall fun F =>
      (continuous_finsetSum _ fun v _ => (by unfold latticeThetaTerm; fun_prop)).continuousOn
  exact (hc.continuousAt (Ici_mem_nhds (by linarith))).continuousWithinAt

/-- Every nonzero integer row has a positive energy gap, uniformly over that lattice. -/
theorem latticeEnergy_gap (z : UpperHalfPlane) :
    ∃ c : ℝ, 0 < c ∧ ∀ v : Fin 2 → ℤ, v ≠ 0 → c ≤ latticeEnergy z v := by
  refine ⟨(EisensteinSeries.r z) ^ 2 / z.im,
    div_pos (sq_pos_of_pos (EisensteinSeries.r_pos z)) z.im_pos, ?_⟩
  intro v hv
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  have hi' : v i ≠ 0 := hi
  have hiabs : (1 : ℝ) ≤ |(v i : ℝ)| := by exact_mod_cast Int.one_le_abs hi'
  have hnorm : (1 : ℝ) ≤ ‖v‖ := by
    apply hiabs.trans
    simpa only [← Int.norm_cast_real, Real.norm_eq_abs] using norm_le_pi_norm v i
  have hs : (1 : ℝ) ≤ ‖v‖ ^ 2 := by nlinarith
  exact (le_mul_of_one_le_right (by positivity) hs).trans (latticeEnergy_norm_lower z v)

open Real Complex Asymptotics MeasureTheory

/-- A positive spectral gap gives a uniform exponential factor in every Gaussian tail. -/
theorem exp_neg_mul_le_gap_factor {q c t : ℝ} (hc : 0 ≤ c) (hcq : c ≤ q)
    (ht : 2 ≤ t) :
    Real.exp (-Real.pi * q * t) ≤
      Real.exp (-Real.pi * c * t / 2) * Real.exp (-Real.pi * q) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hq : 0 ≤ q := hc.trans hcq
  have h₁ : 0 ≤ (q - c) * (t / 2) := mul_nonneg (sub_nonneg.mpr hcq) (by linarith)
  have h₂ : 0 ≤ q * (t / 2 - 1) := mul_nonneg hq (by linarith)
  have h₃ : c * t / 2 + q ≤ q * t := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h₃ Real.pi_pos.le]

/-- The elementary tail estimate also proves convergence, so a totalized sum cannot
silently supply the estimate. -/
theorem summable_gaussian_of_gap {ι : Type*} {q : ι → ℝ} {c t : ℝ}
    (hc : 0 ≤ c) (hq : ∀ i, c ≤ q i)
    (hs : Summable fun i ↦ Real.exp (-Real.pi * q i)) (ht : 2 ≤ t) :
    Summable fun i ↦ Real.exp (-Real.pi * q i * t) := by
  exact Summable.of_nonneg_of_le (fun _ ↦ (Real.exp_pos _).le)
    (fun i ↦ exp_neg_mul_le_gap_factor hc (hq i) ht) (hs.mul_left _)

/-- Summed explicit exponential bound from any positive gap and a Gaussian sum at one. -/
theorem tsum_gaussian_le_gap_factor {ι : Type*} {q : ι → ℝ} {c t : ℝ}
    (hc : 0 ≤ c) (hq : ∀ i, c ≤ q i)
    (hs : Summable fun i ↦ Real.exp (-Real.pi * q i)) (ht : 2 ≤ t) :
    (∑' i, Real.exp (-Real.pi * q i * t)) ≤
      Real.exp (-Real.pi * c * t / 2) * ∑' i, Real.exp (-Real.pi * q i) := by
  rw [← tsum_mul_left]
  exact Summable.tsum_le_tsum (fun i ↦ exp_neg_mul_le_gap_factor hc (hq i) ht)
    (summable_gaussian_of_gap hc hq hs ht) (hs.mul_left _)

/-- Rapid Gaussian tail decay, with an explicit exponential rate. -/
theorem isBigO_gaussian_tail {ι : Type*} {q : ι → ℝ} {c : ℝ}
    (hc : 0 < c) (hq : ∀ i, c ≤ q i)
    (hs : Summable fun i ↦ Real.exp (-Real.pi * q i)) :
    (fun t ↦ ∑' i, Real.exp (-Real.pi * q i * t)) =O[atTop]
      (fun t ↦ Real.exp (-(Real.pi * c / 2) * t)) := by
  apply IsBigO.of_bound (∑' i, Real.exp (-Real.pi * q i))
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg fun _ ↦ (Real.exp_pos _).le),
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have h := tsum_gaussian_le_gap_factor hc.le hq hs ht
  rw [mul_comm] at h
  convert h using 1
  congr 2
  ring

/-- The exponential estimate gives every inverse-power estimate required by `WeakFEPair`. -/
theorem isBigO_gaussian_tail_rpow {ι : Type*} {q : ι → ℝ} {c : ℝ}
    (hc : 0 < c) (hq : ∀ i, c ≤ q i)
    (hs : Summable fun i ↦ Real.exp (-Real.pi * q i)) (r : ℝ) :
    (fun t ↦ ∑' i, Real.exp (-Real.pi * q i * t)) =O[atTop] (fun t ↦ t ^ r) := by
  exact (isBigO_gaussian_tail hc hq hs).trans
    (isLittleO_exp_neg_mul_rpow_atTop (by positivity : 0 < Real.pi * c / 2) r).isBigO

/-- Removing the single zero mode from a convergent Gaussian theta sum. -/
theorem gaussian_tsum_sub_one {ι : Type*} (e : ι) {q : ι → ℝ} (hq0 : q e = 0)
    {t : ℝ} (hs : Summable fun i ↦ Real.exp (-Real.pi * q i * t)) :
    (∑' i, Real.exp (-Real.pi * q i * t)) - 1 =
      ∑' i : {i // i ≠ e}, Real.exp (-Real.pi * q i * t) := by
  classical
  rw [hs.tsum_eq_add_tsum_ite e, hq0]
  simp only [mul_zero, zero_mul, Real.exp_zero, add_sub_cancel_left]
  calc
    _ = ∑' i, ({i | i ≠ e} : Set ι).indicator
        (fun i ↦ Real.exp (-Real.pi * q i * t)) i := by
      congr 1
      ext i
      simp only [Set.indicator, Set.mem_ofPred_eq]
      split_ifs <;> simp_all
    _ = _ := (tsum_subtype (s := {i | i ≠ e})
      (f := fun i ↦ Real.exp (-Real.pi * q i * t))).symm

/-- A zero-mode theta sum with a positive gap has rapid decay after subtracting one. -/
theorem isBigO_gaussian_tsum_sub_one {ι : Type*} (e : ι) {q : ι → ℝ} {c : ℝ}
    (hq0 : q e = 0) (hc : 0 < c) (hq : ∀ i, i ≠ e → c ≤ q i)
    (hs : ∀ t, 0 < t → Summable fun i ↦ Real.exp (-Real.pi * q i * t)) (r : ℝ) :
    (fun t ↦ (∑' i, Real.exp (-Real.pi * q i * t)) - 1) =O[atTop]
      (fun t ↦ t ^ r) := by
  have hsub : Summable fun i : {i // i ≠ e} ↦ Real.exp (-Real.pi * q i) := by
    simpa only [mul_one, Function.comp_def] using (hs 1 zero_lt_one).subtype (fun i ↦ i ≠ e)
  refine (isBigO_gaussian_tail_rpow (q := fun i : {i // i ≠ e} ↦ q i)
    hc (fun i ↦ hq i i.property) hsub r).congr' ?_ .rfl
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  exact (gaussian_tsum_sub_one e hq0 (hs t ht)).symm


/-- The actual theta function has rapid decay after subtracting its unique zero row. -/
theorem isBigO_latticeTheta_sub_one_rpow (z : UpperHalfPlane) (r : ℝ) :
    (fun t => latticeTheta z t - 1) =O[atTop] (fun t => t ^ r) := by
  obtain ⟨c, hc, hgap⟩ := latticeEnergy_gap z
  have hs (t : ℝ) (ht : 0 < t) :
      Summable (fun v : Fin 2 → ℤ => Real.exp (-Real.pi * latticeEnergy z v * t)) := by
    apply (summable_latticeThetaTerm z ht).congr
    intro v
    unfold latticeThetaTerm
    congr 1
    ring
  have h := isBigO_gaussian_tsum_sub_one (0 : Fin 2 → ℤ) (latticeEnergy_zero z)
    hc hgap hs r
  simpa only [latticeTheta, latticeThetaTerm, mul_right_comm] using h

end GapFamily.Analytic
