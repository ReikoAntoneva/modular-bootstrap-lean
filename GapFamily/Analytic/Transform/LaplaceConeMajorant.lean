import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Uniform domination at a nonzero cone edge

On each fixed nonzero frequency slice the physical cone power has an
integrable endpoint singularity whenever the real part of its parameter is
positive. The majorant is uniform over a closed interval of real parts and
may be multiplied by a continuous energy weight, including finite height
differences. No bound on the imaginary part is required.
-/

noncomputable section

namespace GapFamily.Analytic

open Real Set MeasureTheory

/-- Uniform local majorant for the cone power near the endpoint `E = |J|`. -/
def laplaceConeEdgeMajorant (J a b E : ℝ) : ℝ :=
  (E - |J|) ^ (a - 1) * ((E + |J|) ^ (a - 1) + (E + |J|) ^ (b - 1))

private theorem rpow_le_endpoint_sum {x a b c : ℝ} (hx : 0 < x)
    (ha : a ≤ c) (hb : c ≤ b) : x ^ c ≤ x ^ a + x ^ b := by
  by_cases hx1 : x ≤ 1
  · exact (Real.rpow_le_rpow_of_exponent_ge hx hx1 ha).trans
      (le_add_of_nonneg_right (Real.rpow_nonneg hx.le _))
  · exact (Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hx1) hb).trans
      (le_add_of_nonneg_left (Real.rpow_nonneg hx.le _))

private theorem laplaceConeBase_pos {J E : ℝ} (hE : |J| < E) :
    0 < E ^ 2 - J ^ 2 := by
  have hpos : 0 < E - |J| := sub_pos.mpr hE
  have hsum : 0 < E + |J| := by linarith [abs_nonneg J]
  nlinarith [mul_pos hpos hsum, sq_abs J]

theorem laplaceConeEdgeMajorant_nonneg {J a b E : ℝ} (hE : |J| ≤ E) :
    0 ≤ laplaceConeEdgeMajorant J a b E := by
  unfold laplaceConeEdgeMajorant
  have : 0 ≤ E + |J| := by linarith [abs_nonneg J]
  positivity

/-- The complex cone power is uniformly bounded down to the physical edge.
The interval for `Re s` can cross `1/2` or `1`. -/
theorem norm_conePower_le_laplaceConeEdgeMajorant {J a b E : ℝ} {s : ℂ}
    (ha : a ≤ s.re) (hb : s.re ≤ b) (hE : E ∈ Ioo |J| (|J| + 1)) :
    ‖((E ^ 2 - J ^ 2 : ℝ) : ℂ) ^ (s - 1)‖ ≤
      laplaceConeEdgeMajorant J a b E := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (laplaceConeBase_pos hE.1)]
  simp only [Complex.sub_re, Complex.one_re]
  have hfactor : E ^ 2 - J ^ 2 = (E - |J|) * (E + |J|) := by
    nlinarith [sq_abs J]
  have hsub : 0 < E - |J| := sub_pos.mpr hE.1
  have hsum : 0 < E + |J| := by linarith [abs_nonneg J, hE.1]
  rw [hfactor, Real.mul_rpow hsub.le hsum.le]
  unfold laplaceConeEdgeMajorant
  apply mul_le_mul
  · exact Real.rpow_le_rpow_of_exponent_ge hsub (by linarith [hE.2])
      (by linarith)
  · exact rpow_le_endpoint_sum hsum (by linarith) (by linarith)
  · positivity
  · positivity

private theorem integrableOn_edge_rpow {a : ℝ} (ha : 0 < a) (m : ℝ) :
    IntegrableOn (fun E : ℝ => (E - m) ^ (a - 1)) (Ioo m (m + 1)) := by
  have hi : IntervalIntegrable (fun u : ℝ => u ^ (a - 1)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have ht := hi.comp_sub_right m
  have ht' : IntervalIntegrable (fun E : ℝ => (E - m) ^ (a - 1)) volume m (m + 1) := by
    simpa only [zero_add, add_comm 1 m] using ht
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith)).mp ht'

/-- Ordinary endpoint integrability is uniform over every parameter interval
whose lower real part is positive, on each nonzero frequency slice. -/
theorem integrableOn_laplaceConeEdgeMajorant {J a : ℝ} (hJ : J ≠ 0)
    (ha : 0 < a) (b : ℝ) :
    IntegrableOn (laplaceConeEdgeMajorant J a b) (Ioo |J| (|J| + 1)) := by
  have hJpos : 0 < |J| := abs_pos.mpr hJ
  have hc (c : ℝ) : ContinuousOn (fun E : ℝ => (E + |J|) ^ c)
      (Icc |J| (|J| + 1)) := by
    apply (continuous_id.add continuous_const).continuousOn.rpow_const
    intro E hE
    exact Or.inl (ne_of_gt (by linarith [hE.1] : 0 < E + |J|))
  exact (integrableOn_edge_rpow ha |J|).mul_continuousOn_of_subset
    ((hc (a - 1)).add (hc (b - 1))) measurableSet_Ioo isCompact_Icc
      Ioo_subset_Icc_self

/-- A continuous energy weight, such as a finite Laplace difference times
`1 + E`, preserves ordinary integrability of the uniform edge majorant. -/
theorem integrableOn_laplaceConeEdgeMajorant_mul_norm {J a : ℝ} (hJ : J ≠ 0)
    (ha : 0 < a) (b : ℝ) {w : ℝ → ℂ}
    (hw : ContinuousOn w (Icc |J| (|J| + 1))) :
    IntegrableOn (fun E => laplaceConeEdgeMajorant J a b E * ‖w E‖)
      (Ioo |J| (|J| + 1)) :=
  (integrableOn_laplaceConeEdgeMajorant hJ ha b).mul_continuousOn_of_subset
    hw.norm measurableSet_Ioo isCompact_Icc Ioo_subset_Icc_self

/-- Any continuous weight can be carried through the fixed-frequency edge
with a common ordinary majorant for the full strip of parameters. -/
theorem norm_conePower_mul_le_laplaceConeEdgeMajorant {J a b E : ℝ} {s : ℂ}
    (ha : a ≤ s.re) (hb : s.re ≤ b) (hE : E ∈ Ioo |J| (|J| + 1)) (w : ℂ) :
    ‖((E ^ 2 - J ^ 2 : ℝ) : ℂ) ^ (s - 1) * w‖ ≤
      laplaceConeEdgeMajorant J a b E * ‖w‖ := by
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_conePower_le_laplaceConeEdgeMajorant ha hb hE)
    (norm_nonneg _)

/-- The weighted complex cone power itself is absolutely integrable at the
nonzero edge for the full half-plane `Re s > 0`. -/
theorem integrableOn_conePower_mul_at_edge {J : ℝ} (hJ : J ≠ 0) {s : ℂ}
    (hs : 0 < s.re) {w : ℝ → ℂ} (hw : ContinuousOn w (Icc |J| (|J| + 1))) :
    IntegrableOn (fun E : ℝ => ((E ^ 2 - J ^ 2 : ℝ) : ℂ) ^ (s - 1) * w E)
      (Ioo |J| (|J| + 1)) := by
  apply (integrableOn_laplaceConeEdgeMajorant_mul_norm hJ hs s.re hw).mono'
  · have hp : ContinuousOn (fun E : ℝ => ((E ^ 2 - J ^ 2 : ℝ) : ℂ) ^ (s - 1))
        (Ioo |J| (|J| + 1)) :=
      (by fun_prop : Continuous (fun E : ℝ => ((E ^ 2 - J ^ 2 : ℝ) : ℂ))).continuousOn.cpow_const
        (fun E hE => Or.inl (laplaceConeBase_pos hE.1))
    exact (hp.mul (hw.mono Ioo_subset_Icc_self)).aestronglyMeasurable measurableSet_Ioo
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with E hE
    exact norm_conePower_mul_le_laplaceConeEdgeMajorant le_rfl le_rfl hE (w E)

/-- The physical height-difference weight has an ordinary endpoint majorant
uniform in the complex parameter. The heights need no restriction for this
local endpoint statement. -/
theorem laplaceCone_difference_edge_majorant {J a : ℝ} (hJ : J ≠ 0) (ha : 0 < a)
    (b t d : ℝ) :
    ∃ g : ℝ → ℝ, IntegrableOn g (Ioo |J| (|J| + 1)) ∧
      ∀ (s : ℂ), a ≤ s.re → s.re ≤ b → ∀ E ∈ Ioo |J| (|J| + 1),
        ‖((E ^ 2 - J ^ 2 : ℝ) : ℂ) ^ (s - 1) *
          ((Real.exp (-t * E) - Real.exp (-(t + d) * E)) * (1 + E) : ℝ)‖ ≤ g E := by
  let w : ℝ → ℂ := fun E =>
    (((Real.exp (-t * E) - Real.exp (-(t + d) * E)) * (1 + E) : ℝ) : ℂ)
  refine ⟨fun E => laplaceConeEdgeMajorant J a b E * ‖w E‖,
    integrableOn_laplaceConeEdgeMajorant_mul_norm hJ ha b (by fun_prop), ?_⟩
  intro s hsa hsb E hE
  exact norm_conePower_mul_le_laplaceConeEdgeMajorant hsa hsb hE (w E)

/-- At distance at least one from the edge, one polynomial exponent controls
the whole closed parameter strip. -/
theorem norm_conePower_le_tail_rpow {J b E : ℝ} {s : ℂ}
    (hb : s.re ≤ b) (hE : |J| + 1 ≤ E) :
    ‖((E ^ 2 - J ^ 2 : ℝ) : ℂ) ^ (s - 1)‖ ≤ E ^ (2 * max 0 (b - 1)) := by
  have hE0 : 0 < E := by linarith [abs_nonneg J]
  have hEJ : |J| < E := by linarith
  have hbase : 1 ≤ E ^ 2 - J ^ 2 := by
    have hfactor : E ^ 2 - J ^ 2 = (E - |J|) * (E + |J|) := by
      nlinarith [sq_abs J]
    rw [hfactor]
    have hm : 1 ≤ E - |J| := by linarith
    have hp : 1 ≤ E + |J| := by linarith [abs_nonneg J]
    nlinarith
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (laplaceConeBase_pos hEJ)]
  simp only [Complex.sub_re, Complex.one_re]
  calc
    (E ^ 2 - J ^ 2) ^ (s.re - 1) ≤
        (E ^ 2 - J ^ 2) ^ max 0 (b - 1) :=
      Real.rpow_le_rpow_of_exponent_le hbase ((sub_le_sub_right hb 1).trans (le_max_right _ _))
    _ ≤ (E ^ 2) ^ max 0 (b - 1) :=
      Real.rpow_le_rpow (by linarith) (by nlinarith [sq_nonneg J]) (le_max_left _ _)
    _ = E ^ (2 * max 0 (b - 1)) := by
      rw [← Real.rpow_two, ← Real.rpow_mul hE0.le]

private theorem integrableOn_laplaceConeTail {t : ℝ} (ht : 0 < t) (b : ℝ) :
    IntegrableOn (fun E : ℝ => E ^ (2 * max 0 (b - 1)) * Real.exp (-t * E) * (1 + E))
      (Ioi 0) := by
  have hp : 0 ≤ 2 * max 0 (b - 1) := by positivity
  have hi (p : ℝ) (hp : -1 < p) :
      IntegrableOn (fun E : ℝ => E ^ p * Real.exp (-t * E)) (Ioi 0) := by
    simpa only [Real.rpow_one, neg_mul] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (s := p) (p := 1) (b := t)
        hp zero_lt_one ht)
  apply ((hi (2 * max 0 (b - 1)) (by linarith)).add
    (hi (2 * max 0 (b - 1) + 1) (by linarith))).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with E hE
  simp only [Pi.add_apply, Real.rpow_add hE, Real.rpow_one]
  ring

private theorem norm_laplaceDifference_weight_le {E d : ℝ} (hE : 0 ≤ E) (hd : 0 ≤ d)
    (t : ℝ) :
    ‖(((Real.exp (-t * E) - Real.exp (-(t + d) * E)) * (1 + E) : ℝ) : ℂ)‖ ≤
      Real.exp (-t * E) * (1 + E) := by
  have he : Real.exp (-(t + d) * E) ≤ Real.exp (-t * E) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hd hE]
  rw [Complex.norm_of_nonneg (mul_nonneg (sub_nonneg.mpr he) (by linarith))]
  exact mul_le_mul_of_nonneg_right (sub_le_self _ (Real.exp_pos _).le) (by linarith)

/-- After a finite positive height difference, a fixed nonzero frequency
slice has an ordinary majorant on the entire physical energy half-line,
uniform in every strip `0 < a ≤ Re s ≤ b`. -/
theorem laplaceCone_difference_majorant {J a t d : ℝ} (hJ : J ≠ 0) (ha : 0 < a)
    (ht : 0 < t) (hd : 0 ≤ d) (b : ℝ) :
    ∃ g : ℝ → ℝ, IntegrableOn g (Ioi |J|) ∧
      ∀ (s : ℂ), a ≤ s.re → s.re ≤ b → ∀ E ∈ Ioi |J|,
        ‖((E ^ 2 - J ^ 2 : ℝ) : ℂ) ^ (s - 1) *
          ((Real.exp (-t * E) - Real.exp (-(t + d) * E)) * (1 + E) : ℝ)‖ ≤ g E := by
  obtain ⟨ge, hge, hbound⟩ := laplaceCone_difference_edge_majorant hJ ha b t d
  let gt : ℝ → ℝ := fun E =>
    E ^ (2 * max 0 (b - 1)) * Real.exp (-t * E) * (1 + E)
  refine ⟨fun E => (Ioo |J| (|J| + 1)).indicator ge E + gt E,
    (hge.integrable_indicator measurableSet_Ioo).integrableOn.add
      ((integrableOn_laplaceConeTail ht b).mono_set (fun E hE =>
        (abs_nonneg J).trans_lt hE)), ?_⟩
  intro s hsa hsb E hE
  dsimp only
  have hE0 : 0 < E := (abs_nonneg J).trans_lt hE
  by_cases hedge : E < |J| + 1
  · have hm : E ∈ Ioo |J| (|J| + 1) := ⟨hE, hedge⟩
    rw [Set.indicator_of_mem hm]
    exact (hbound s hsa hsb E hm).trans (le_add_of_nonneg_right (by dsimp [gt]; positivity))
  · have hm : E ∉ Ioo |J| (|J| + 1) := fun h => hedge h.2
    rw [Set.indicator_of_notMem hm, zero_add]
    rw [norm_mul]
    dsimp [gt]
    calc
      _ ≤ E ^ (2 * max 0 (b - 1)) * (Real.exp (-t * E) * (1 + E)) := by
        exact mul_le_mul (norm_conePower_le_tail_rpow hsb (le_of_not_gt hedge))
          (norm_laplaceDifference_weight_le hE0.le hd t) (norm_nonneg _) (by positivity)
      _ = _ := by ring

/-- The height-differenced cone slice, including its linear energy weight,
is ordinarily absolutely integrable throughout `Re s > 0`. -/
theorem integrableOn_laplaceCone_difference {J t d : ℝ} (hJ : J ≠ 0)
    (ht : 0 < t) (hd : 0 ≤ d) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun E : ℝ => ((E ^ 2 - J ^ 2 : ℝ) : ℂ) ^ (s - 1) *
      ((Real.exp (-t * E) - Real.exp (-(t + d) * E)) * (1 + E) : ℝ))
      (Ioi |J|) := by
  obtain ⟨g, hg, hbound⟩ := laplaceCone_difference_majorant hJ hs ht hd s.re
  apply hg.mono'
  · have hp : ContinuousOn (fun E : ℝ => ((E ^ 2 - J ^ 2 : ℝ) : ℂ) ^ (s - 1))
        (Ioi |J|) :=
      (by fun_prop : Continuous (fun E : ℝ => ((E ^ 2 - J ^ 2 : ℝ) : ℂ))).continuousOn.cpow_const
        (fun E hE => Or.inl (laplaceConeBase_pos hE))
    exact (hp.mul (by fun_prop)).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with E hE
    exact hbound s le_rfl le_rfl E hE

end GapFamily.Analytic
