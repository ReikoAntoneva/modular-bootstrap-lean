import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# An ordinary majorant for scalar Laplace differences

A difference of two positive thermal heights gains one power at zero. Thus
its same-parameter scalar cone weight is ordinarily integrable on every
closed strip strictly inside `Re s > 0`, even after multiplication by a
seed bounded by `C * (1 + E)`.
-/

noncomputable section

namespace GapFamily.Analytic

open Set MeasureTheory

/-- The input height difference before a choice of discrete test heights. -/
def thermalHeightDifference (t d E : ℝ) : ℝ :=
  Real.exp (-t * E) - Real.exp (-(t + d) * E)

/-- The scalar cone weight with its endpoint-regularizing height difference. -/
def scalarLaplaceDifferenceWeight (s : ℂ) (t d E : ℝ) : ℂ :=
  (E : ℂ) ^ (2 * (s - 1)) * (thermalHeightDifference t d E : ℂ)

/-- A single real majorant for the full closed strip, including linear seed growth. -/
def scalarLaplaceDifferenceMajorant (a b t d E : ℝ) : ℝ :=
  d * (E ^ (2 * a - 1) + E ^ (2 * b - 1)) * (1 + E) * Real.exp (-t * E)

/-- Identification with the squared-base convention of the spatial cone formula. -/
theorem scalarLaplaceDifferenceWeight_eq_sq (s : ℂ) (t d : ℝ) {E : ℝ} (hE : 0 < E) :
    scalarLaplaceDifferenceWeight s t d E =
      ((E ^ 2 : ℝ) : ℂ) ^ (s - 1) * (thermalHeightDifference t d E : ℂ) := by
  unfold scalarLaplaceDifferenceWeight
  rw [Complex.cpow_ofNat_mul' (n := 2)]
  · norm_cast
  · simp only [Complex.arg_ofReal_of_nonneg hE.le, mul_zero]
    exact neg_lt_zero.mpr Real.pi_pos
  · simp only [Complex.arg_ofReal_of_nonneg hE.le, mul_zero]
    exact Real.pi_pos.le

/-- At the threshold the scalar weight is precisely the height difference
against the physical reference density `1 / E`. -/
theorem scalarLaplaceDifferenceWeight_one_half (t d E : ℝ) :
    scalarLaplaceDifferenceWeight (1 / 2) t d E =
      ((E⁻¹ * thermalHeightDifference t d E : ℝ) : ℂ) := by
  norm_num [scalarLaplaceDifferenceWeight, Complex.cpow_neg_one]

theorem thermalHeightDifference_eq (t d E : ℝ) :
    thermalHeightDifference t d E = Real.exp (-t * E) * (1 - Real.exp (-d * E)) := by
  unfold thermalHeightDifference
  rw [mul_sub, mul_one, ← Real.exp_add]
  congr 2
  ring

theorem thermalHeightDifference_nonneg (t : ℝ) {d E : ℝ} (hd : 0 ≤ d) (hE : 0 ≤ E) :
    0 ≤ thermalHeightDifference t d E := by
  rw [thermalHeightDifference_eq]
  exact mul_nonneg (Real.exp_pos _).le
    (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hd) hE)))

/-- The finite difference gains one full energy power at the scalar origin. -/
theorem thermalHeightDifference_le (t d E : ℝ) :
    thermalHeightDifference t d E ≤ d * E * Real.exp (-t * E) := by
  rw [thermalHeightDifference_eq]
  have h := Real.add_one_le_exp (-d * E)
  have hdiff : 1 - Real.exp (-d * E) ≤ d * E := by linarith
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hdiff (Real.exp_pos (-t * E)).le

/-- Endpoint powers dominate all intermediate exponents on the positive axis. -/
theorem rpow_le_endpoint_sum {E a b r : ℝ} (hE : 0 < E) (ha : a ≤ r) (hb : r ≤ b) :
    E ^ r ≤ E ^ a + E ^ b := by
  by_cases hE1 : E ≤ 1
  · exact (Real.rpow_le_rpow_of_exponent_ge hE hE1 ha).trans
      (le_add_of_nonneg_right (Real.rpow_nonneg hE.le _))
  · exact (Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hE1) hb).trans
      (le_add_of_nonneg_left (Real.rpow_nonneg hE.le _))

theorem norm_scalarLaplaceDifferenceWeight (s : ℂ) (t : ℝ) {d E : ℝ}
    (hd : 0 ≤ d) (hE : 0 < E) :
    ‖scalarLaplaceDifferenceWeight s t d E‖ =
      E ^ (2 * (s.re - 1)) * thermalHeightDifference t d E := by
  rw [scalarLaplaceDifferenceWeight, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hE, Complex.norm_real,
    Real.norm_of_nonneg (thermalHeightDifference_nonneg t hd hE.le)]
  congr 2
  simp

/-- Uniform scalar endpoint domination on a closed real-part strip. -/
theorem norm_scalarLaplaceDifferenceWeight_mul_linear_le
    {s : ℂ} {a b t d E : ℝ} (has : a ≤ s.re) (hsb : s.re ≤ b)
    (hd : 0 ≤ d) (hE : 0 < E) :
    ‖scalarLaplaceDifferenceWeight s t d E‖ * (1 + E) ≤
      scalarLaplaceDifferenceMajorant a b t d E := by
  rw [norm_scalarLaplaceDifferenceWeight s t hd hE]
  have hp : E ^ (2 * (s.re - 1)) * E = E ^ (2 * s.re - 1) := by
    rw [← Real.rpow_add_one hE.ne']
    congr 1
    ring
  have hbnd : E ^ (2 * s.re - 1) ≤ E ^ (2 * a - 1) + E ^ (2 * b - 1) :=
    rpow_le_endpoint_sum hE (by linarith) (by linarith)
  calc
    E ^ (2 * (s.re - 1)) * thermalHeightDifference t d E * (1 + E) ≤
        E ^ (2 * (s.re - 1)) * (d * E * Real.exp (-t * E)) * (1 + E) := by
      gcongr
      exact thermalHeightDifference_le t d E
    _ = d * E ^ (2 * s.re - 1) * (1 + E) * Real.exp (-t * E) := by
      rw [← hp]
      ring
    _ ≤ scalarLaplaceDifferenceMajorant a b t d E := by
      unfold scalarLaplaceDifferenceMajorant
      gcongr

/-- The strip majorant also controls a seed with a uniform linear growth bound. -/
theorem norm_scalarLaplaceDifferenceWeight_mul_le
    {s F : ℂ} {a b t d E C : ℝ} (has : a ≤ s.re) (hsb : s.re ≤ b)
    (hd : 0 ≤ d) (hE : 0 < E) (hC : 0 ≤ C) (hF : ‖F‖ ≤ C * (1 + E)) :
    ‖scalarLaplaceDifferenceWeight s t d E * F‖ ≤
      C * scalarLaplaceDifferenceMajorant a b t d E := by
  rw [norm_mul]
  calc
    ‖scalarLaplaceDifferenceWeight s t d E‖ * ‖F‖ ≤
        ‖scalarLaplaceDifferenceWeight s t d E‖ * (C * (1 + E)) :=
      mul_le_mul_of_nonneg_left hF (norm_nonneg _)
    _ = C * (‖scalarLaplaceDifferenceWeight s t d E‖ * (1 + E)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (norm_scalarLaplaceDifferenceWeight_mul_linear_le has hsb hd hE) hC

/-- Ordinary Gamma integrability, with an additional linear energy factor. -/
theorem integrableOn_rpow_mul_one_add_mul_exp {r t : ℝ} (hr : -1 < r) (ht : 0 < t) :
    IntegrableOn (fun E : ℝ => E ^ r * (1 + E) * Real.exp (-t * E)) (Ioi 0) := by
  have hi (q : ℝ) (hq : -1 < q) :
      IntegrableOn (fun E : ℝ => E ^ q * Real.exp (-t * E)) (Ioi 0) := by
    simpa only [Real.rpow_one] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (s := q) (p := 1) hq zero_lt_one ht)
  apply ((hi r hr).add (hi (r + 1) (by linarith))).congr_fun _ measurableSet_Ioi
  intro E hE
  simp only [Pi.add_apply]
  rw [Real.rpow_add_one (ne_of_gt hE)]
  ring

/-- The majorant is an ordinary integrable function whenever `0 < a ≤ b`
and the lower thermal height is positive. -/
theorem integrableOn_scalarLaplaceDifferenceMajorant
    {a b t : ℝ} (ha : 0 < a) (hab : a ≤ b) (ht : 0 < t) (d : ℝ) :
    IntegrableOn (scalarLaplaceDifferenceMajorant a b t d) (Ioi 0) := by
  have hi := ((integrableOn_rpow_mul_one_add_mul_exp (r := 2 * a - 1)
    (by linarith) ht).add
    (integrableOn_rpow_mul_one_add_mul_exp (r := 2 * b - 1) (by linarith) ht)).const_mul d
  apply hi.congr
  filter_upwards [] with E
  simp only [scalarLaplaceDifferenceMajorant, Pi.add_apply]
  ring

theorem continuousOn_scalarLaplaceDifferenceWeight (s : ℂ) (t d : ℝ) :
    ContinuousOn (scalarLaplaceDifferenceWeight s t d) (Ioi 0) := by
  apply ContinuousOn.mul
  · exact Complex.continuous_ofReal.continuousOn.cpow_const (fun E hE => Or.inl hE)
  · unfold thermalHeightDifference
    fun_prop

/-- The regularized scalar weight is entire in the shared complex parameter
at every positive energy. -/
theorem differentiable_scalarLaplaceDifferenceWeight (t d : ℝ) {E : ℝ} (hE : 0 < E) :
    Differentiable ℂ (fun s : ℂ => scalarLaplaceDifferenceWeight s t d E) := by
  unfold scalarLaplaceDifferenceWeight
  apply Differentiable.mul_const
  apply Differentiable.const_cpow
  · fun_prop
  · exact Or.inl (Complex.ofReal_ne_zero.mpr hE.ne')

/-- Absolute integrability of the regularized scalar weight including a
linearly growing energy factor, throughout `Re s > 0`. -/
theorem integrableOn_scalarLaplaceDifferenceWeight_mul_linear
    {s : ℂ} (hs : 0 < s.re) {t d : ℝ} (ht : 0 < t) (hd : 0 ≤ d) :
    IntegrableOn (fun E : ℝ => scalarLaplaceDifferenceWeight s t d E * (1 + E : ℝ))
      (Ioi 0) := by
  apply (integrableOn_scalarLaplaceDifferenceMajorant hs le_rfl ht d).mono'
  · exact ((continuousOn_scalarLaplaceDifferenceWeight s t d).mul
      (by fun_prop)).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with E hE
    change 0 < E at hE
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith : 0 ≤ 1 + E)]
    exact norm_scalarLaplaceDifferenceWeight_mul_linear_le le_rfl le_rfl hd hE

/-- A normally continued seed with a proved linear energy bound can be
integrated against the same-parameter scalar height difference. -/
theorem integrableOn_scalarLaplaceDifferenceWeight_mul_of_bound
    {s : ℂ} (hs : 0 < s.re) {t d C : ℝ} (ht : 0 < t) (hd : 0 ≤ d)
    {F : ℝ → ℂ} (hF : AEStronglyMeasurable F (volume.restrict (Ioi 0)))
    (hbound : ∀ E, 0 < E → ‖F E‖ ≤ C * (1 + E)) :
    IntegrableOn (fun E => scalarLaplaceDifferenceWeight s t d E * F E) (Ioi 0) := by
  have hi := (integrableOn_scalarLaplaceDifferenceWeight_mul_linear hs ht hd).norm.const_mul C
  apply hi.mono'
  · exact ((continuousOn_scalarLaplaceDifferenceWeight s t d).aestronglyMeasurable
      measurableSet_Ioi).mul hF
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with E hE
    change 0 < E at hE
    simp only [norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (by linarith : 0 ≤ 1 + E)]
    calc
      ‖scalarLaplaceDifferenceWeight s t d E‖ * ‖F E‖ ≤
          ‖scalarLaplaceDifferenceWeight s t d E‖ * (C * (1 + E)) :=
        mul_le_mul_of_nonneg_left (hbound E hE) (norm_nonneg _)
      _ = C * (‖scalarLaplaceDifferenceWeight s t d E‖ * (1 + E)) := by ring

end GapFamily.Analytic
