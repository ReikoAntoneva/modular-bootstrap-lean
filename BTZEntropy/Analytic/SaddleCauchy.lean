import BTZEntropy.Analytic.SaddlePhase
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# Gaussian Cauchy bound for the rescaled saddle integrand

A disk in the perturbation parameter maps into a half disk around the positive
saddle. The reciprocal phase has a uniform positive real part there, giving
Gaussian decay before Cauchy's derivative estimate is applied.
-/

noncomputable section

open scoped Topology

namespace BTZEntropy

/-- Radius that remains usable at arbitrarily large Gaussian coordinate. -/
def saddleCauchyRadius (β t : ℝ) : ℝ := β / (4 * (1 + |t|))

/-- The exact integrand after scaling contour height by the small parameter. -/
def rescaledSaddleIntegrand (A : ℂ → ℂ) (β t : ℝ) (z : ℂ) : ℂ :=
  A ((β : ℂ) + Complex.I * z * (t : ℂ)) *
    Complex.exp (-(phaseConstant : ℂ) * (t : ℂ) ^ 2 /
      ((β : ℂ) ^ 2 * ((β : ℂ) + Complex.I * z * (t : ℂ))))

theorem saddleCauchyRadius_pos {β : ℝ} (hβ : 0 < β) (t : ℝ) :
    0 < saddleCauchyRadius β t := by
  unfold saddleCauchyRadius
  positivity

theorem saddleCauchyRadius_mul_abs_le {β : ℝ} (hβ : 0 < β) (t : ℝ) :
    saddleCauchyRadius β t * |t| ≤ β / 4 := by
  unfold saddleCauchyRadius
  have hd : 0 < 4 * (1 + |t|) := by positivity
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).2
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
  apply (div_le_iff₀ hd).2
  nlinarith [abs_nonneg t]

/-- The complex parameter disk maps into the half disk at the real saddle. -/
theorem saddleCauchy_argument_mem {β ε t : ℝ} (hβ : 0 < β)
    (hε : |ε * t| ≤ β / 4) {z : ℂ}
    (hz : z ∈ Metric.closedBall (ε : ℂ) (saddleCauchyRadius β t)) :
    (β : ℂ) + Complex.I * z * (t : ℂ) ∈
      Metric.closedBall (β : ℂ) (β / 2) := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hz ⊢
  simp only [add_sub_cancel_left]
  calc
    ‖Complex.I * z * (t : ℂ)‖ =
        ‖Complex.I * (z - (ε : ℂ)) * (t : ℂ) +
          Complex.I * (ε : ℂ) * (t : ℂ)‖ := by congr 1; ring
    _ ≤ ‖Complex.I * (z - (ε : ℂ)) * (t : ℂ)‖ +
        ‖Complex.I * (ε : ℂ) * (t : ℂ)‖ := norm_add_le _ _
    _ = ‖z - (ε : ℂ)‖ * |t| + |ε * t| := by simp
    _ ≤ saddleCauchyRadius β t * |t| + β / 4 :=
      add_le_add (mul_le_mul_of_nonneg_right hz (abs_nonneg t)) hε
    _ ≤ β / 2 := by linarith [saddleCauchyRadius_mul_abs_le hβ t]

/-- The half disk has a positive real part. -/
theorem saddle_halfDisk_re_le {β : ℝ} (_hβ : 0 < β) {w : ℂ}
    (hw : w ∈ Metric.closedBall (β : ℂ) (β / 2)) : β / 2 ≤ w.re := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hw
  have hr := Complex.abs_re_le_norm (w - (β : ℂ))
  simp only [Complex.sub_re, Complex.ofReal_re] at hr
  have := (abs_le.mp (hr.trans hw)).1
  linarith

theorem saddle_halfDisk_norm_le {β : ℝ} (hβ : 0 < β) {w : ℂ}
    (hw : w ∈ Metric.closedBall (β : ℂ) (β / 2)) : ‖w‖ ≤ 3 * β / 2 := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hw
  have ht := norm_add_le (w - (β : ℂ)) (β : ℂ)
  simp only [sub_add_cancel, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hβ] at ht
  linarith

theorem saddle_halfDisk_ne_zero {β : ℝ} (hβ : 0 < β) {w : ℂ}
    (hw : w ∈ Metric.closedBall (β : ℂ) (β / 2)) : w ≠ 0 := by
  have hr := saddle_halfDisk_re_le hβ hw
  intro he
  simp [he] at hr
  linarith

/-- The explicit lower bound produces a Gaussian envelope independent of the
complex point on the parameter disk. -/
theorem saddle_halfDisk_inv_re {β : ℝ} (hβ : 0 < β) {w : ℂ}
    (hw : w ∈ Metric.closedBall (β : ℂ) (β / 2)) :
    2 / (9 * β) ≤ w⁻¹.re := by
  have hr := saddle_halfDisk_re_le hβ hw
  have hn := saddle_halfDisk_norm_le hβ hw
  have hw0 := saddle_halfDisk_ne_zero hβ hw
  rw [Complex.inv_re, Complex.normSq_eq_norm_sq]
  have hn0 : 0 < ‖w‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hw0)
  apply (div_le_div_iff₀ (by positivity : 0 < 9 * β) hn0).2
  nlinarith [sq_nonneg (3 * β / 2 - ‖w‖),
    mul_le_mul_of_nonneg_left hr (show 0 ≤ 9 * β by positivity),
    mul_self_le_mul_self (norm_nonneg w) hn]

/-- The Gaussian exponential bound is derived from the actual reciprocal phase. -/
theorem norm_rescaledSaddleIntegrand_le {A : ℂ → ℂ} {β ε t M : ℝ}
    (hβ : 0 < β) (hε : |ε * t| ≤ β / 4)
    (hA : ∀ w ∈ Metric.closedBall (β : ℂ) (β / 2), ‖A w‖ ≤ M)
    {z : ℂ} (hz : z ∈ Metric.closedBall (ε : ℂ) (saddleCauchyRadius β t)) :
    ‖rescaledSaddleIntegrand A β t z‖ ≤
      M * Real.exp (-(2 * phaseConstant / (9 * β ^ 3)) * t ^ 2) := by
  let w : ℂ := (β : ℂ) + Complex.I * z * (t : ℂ)
  have hw := saddleCauchy_argument_mem hβ hε hz
  have hi := saddle_halfDisk_inv_re hβ hw
  have hphase :
      (-(phaseConstant : ℂ) * (t : ℂ) ^ 2 / ((β : ℂ) ^ 2 * w)).re =
        -(phaseConstant * t ^ 2 / β ^ 2) * w⁻¹.re := by
    rw [div_mul_eq_div_div, div_eq_mul_inv]
    have hc : -(phaseConstant : ℂ) * (t : ℂ) ^ 2 / (β : ℂ) ^ 2 =
        (-(phaseConstant * t ^ 2 / β ^ 2) : ℝ) := by push_cast; ring
    rw [hc]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hp := phaseConstant_pos
  have he : ‖Complex.exp (-(phaseConstant : ℂ) * (t : ℂ) ^ 2 /
      ((β : ℂ) ^ 2 * w))‖ ≤
        Real.exp (-(2 * phaseConstant / (9 * β ^ 3)) * t ^ 2) := by
    rw [Complex.norm_exp, hphase]
    apply Real.exp_le_exp.mpr
    calc
      -(phaseConstant * t ^ 2 / β ^ 2) * w⁻¹.re ≤
          -(phaseConstant * t ^ 2 / β ^ 2) * (2 / (9 * β)) := by
        exact mul_le_mul_of_nonpos_left hi (neg_nonpos.mpr (by positivity))
      _ = _ := by field_simp
  unfold rescaledSaddleIntegrand
  rw [norm_mul]
  exact mul_le_mul (hA w hw) he (norm_nonneg _) ((norm_nonneg _).trans (hA w hw))

/-- Holomorphicity comes from that of the amplitude on the image disk. -/
theorem differentiableOn_rescaledSaddleIntegrand {A : ℂ → ℂ} {β ε t : ℝ}
    (hβ : 0 < β) (hε : |ε * t| ≤ β / 4)
    (hA : AnalyticOnNhd ℂ A (Metric.closedBall (β : ℂ) (β / 2))) :
    DifferentiableOn ℂ (rescaledSaddleIntegrand A β t)
      (Metric.closedBall (ε : ℂ) (saddleCauchyRadius β t)) := by
  intro z hz
  have hw := saddleCauchy_argument_mem hβ hε hz
  have hw0 := saddle_halfDisk_ne_zero hβ hw
  have hd : DifferentiableAt ℂ (fun z : ℂ => (β : ℂ) + Complex.I * z * (t : ℂ)) z :=
    (differentiableAt_const _).add (((differentiableAt_const _).mul differentiableAt_id).mul_const _)
  have ha := (hA _ hw).differentiableAt.comp z hd
  have hden : (β : ℂ) ^ 2 * ((β : ℂ) + Complex.I * z * (t : ℂ)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (ne_of_gt hβ))) hw0
  have he := ((differentiableAt_const (-(phaseConstant : ℂ) * (t : ℂ) ^ 2)).div ((differentiableAt_const _).mul hd) hden).cexp
  exact (ha.mul he).differentiableWithinAt

/-- The actual saddle integrand satisfies Cauchy's estimate with Gaussian decay. -/
theorem norm_iteratedDeriv_rescaledSaddleIntegrand_le {A : ℂ → ℂ} {β ε t M : ℝ}
    (hβ : 0 < β) (hε : |ε * t| ≤ β / 4)
    (hA : AnalyticOnNhd ℂ A (Metric.closedBall (β : ℂ) (β / 2)))
    (hM : ∀ w ∈ Metric.closedBall (β : ℂ) (β / 2), ‖A w‖ ≤ M) (n : ℕ) :
    ‖iteratedDeriv n (rescaledSaddleIntegrand A β t) (ε : ℂ)‖ ≤
      n.factorial * (M * Real.exp (-(2 * phaseConstant / (9 * β ^ 3)) * t ^ 2)) /
        saddleCauchyRadius β t ^ n := by
  apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n
    (saddleCauchyRadius_pos hβ t)
  · apply DifferentiableOn.diffContOnCl
    exact (differentiableOn_rescaledSaddleIntegrand hβ hε hA).mono
      Metric.closure_ball_subset_closedBall
  · intro z hz
    exact norm_rescaledSaddleIntegrand_le hβ hε hM (Metric.sphere_subset_closedBall hz)

/-- On a compact positive saddle interval, the derivative constants separate
into a fixed coefficient, a polynomial in the Gaussian coordinate, and one
Gaussian valid throughout the interval. -/
theorem norm_iteratedDeriv_rescaledSaddleIntegrand_le_uniform
    {A : ℂ → ℂ} {b B β ε t M : ℝ} (hb : 0 < b) (hβ : β ∈ Set.Icc b B)
    (hε : |ε * t| ≤ b / 4)
    (hA : AnalyticOnNhd ℂ A (Metric.closedBall (β : ℂ) (β / 2)))
    (hM : ∀ w ∈ Metric.closedBall (β : ℂ) (β / 2), ‖A w‖ ≤ M) (n : ℕ) :
    ‖iteratedDeriv n (rescaledSaddleIntegrand A β t) (ε : ℂ)‖ ≤
      (n.factorial * M * (4 / b) ^ n) * (1 + |t|) ^ n *
        Real.exp (-(2 * phaseConstant / (9 * B ^ 3)) * t ^ 2) := by
  have hβp : 0 < β := hb.trans_le hβ.1
  have hBp : 0 < B := hβp.trans_le hβ.2
  have hεβ : |ε * t| ≤ β / 4 := hε.trans (by linarith [hβ.1])
  have hM0 : 0 ≤ M := (norm_nonneg (A (β : ℂ))).trans
    (hM _ (Metric.mem_closedBall_self (by positivity)))
  have hc : 2 * phaseConstant / (9 * B ^ 3) ≤
      2 * phaseConstant / (9 * β ^ 3) := by
    apply div_le_div_of_nonneg_left (by positivity [phaseConstant_pos]) (by positivity)
    gcongr
    exact hβ.2
  have he : Real.exp (-(2 * phaseConstant / (9 * β ^ 3)) * t ^ 2) ≤
      Real.exp (-(2 * phaseConstant / (9 * B ^ 3)) * t ^ 2) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (neg_le_neg hc) (sq_nonneg t)
  have hr : saddleCauchyRadius b t ≤ saddleCauchyRadius β t := by
    unfold saddleCauchyRadius
    exact div_le_div_of_nonneg_right hβ.1 (by positivity)
  calc
    _ ≤ n.factorial * (M * Real.exp (-(2 * phaseConstant / (9 * β ^ 3)) * t ^ 2)) /
        saddleCauchyRadius β t ^ n :=
      norm_iteratedDeriv_rescaledSaddleIntegrand_le hβp hεβ hA hM n
    _ ≤ n.factorial * (M * Real.exp (-(2 * phaseConstant / (9 * B ^ 3)) * t ^ 2)) /
        saddleCauchyRadius b t ^ n := by
      apply div_le_div₀ (by positivity) _ (by positivity [saddleCauchyRadius_pos hb t])
      · exact pow_le_pow_left₀ (le_of_lt (saddleCauchyRadius_pos hb t)) hr n
      · exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he hM0) (by positivity)
    _ = _ := by
      unfold saddleCauchyRadius
      rw [div_pow, div_div_eq_mul_div, mul_pow, div_pow]
      ring

/-- Restricting a holomorphic function to the real axis preserves every scalar
iterated derivative. This is a local assertion, so no global extension is used. -/
theorem iteratedDeriv_comp_ofReal_of_analyticAt {f : ℂ → ℂ} {x : ℝ}
    (hf : AnalyticAt ℂ f (x : ℂ)) (n : ℕ) :
    iteratedDeriv n (fun y : ℝ => f (y : ℂ)) x = iteratedDeriv n f (x : ℂ) := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
      rw [iteratedDeriv_succ', iteratedDeriv_succ']
      have he : deriv (fun y : ℝ => f (y : ℂ)) =ᶠ[𝓝 x]
          fun y : ℝ => deriv f (y : ℂ) := by
        filter_upwards [Complex.continuous_ofReal.continuousAt.eventually
          hf.eventually_analyticAt] with y hy
        exact hy.differentiableAt.hasDerivAt.comp_ofReal.deriv
      exact (he.iteratedDeriv_eq n).trans (ih hf.deriv)

/-- The actual parameter integrand is holomorphic at every admissible real center. -/
theorem analyticAt_rescaledSaddleIntegrand {A : ℂ → ℂ} {β ε t : ℝ}
    (hβ : 0 < β) (hε : |ε * t| ≤ β / 4)
    (hA : AnalyticOnNhd ℂ A (Metric.closedBall (β : ℂ) (β / 2))) :
    AnalyticAt ℂ (rescaledSaddleIntegrand A β t) (ε : ℂ) :=
  (differentiableOn_rescaledSaddleIntegrand hβ hε hA).analyticAt
    (Metric.closedBall_mem_nhds _ (saddleCauchyRadius_pos hβ t))

/-- Arbitrary finite real smoothness required by the real Taylor integral theorem. -/
theorem contDiffAt_rescaledSaddleIntegrand_real {A : ℂ → ℂ} {β ε t : ℝ}
    (hβ : 0 < β) (hε : |ε * t| ≤ β / 4)
    (hA : AnalyticOnNhd ℂ A (Metric.closedBall (β : ℂ) (β / 2)))
    (n : WithTop ℕ∞) :
    ContDiffAt ℝ n (fun e : ℝ => rescaledSaddleIntegrand A β t (e : ℂ)) ε := by
  have ha := analyticAt_rescaledSaddleIntegrand hβ hε hA
  exact (ha.restrictScalars (𝕜 := ℝ)).contDiffAt.comp ε
    Complex.ofRealCLM.contDiff.contDiffAt

/-- Uniform Gaussian Cauchy estimate for the real parameter derivatives used by
Taylor's theorem under the contour integral. -/
theorem norm_iteratedDeriv_rescaledSaddleIntegrand_real_le_uniform
    {A : ℂ → ℂ} {b B β ε t M : ℝ} (hb : 0 < b) (hβ : β ∈ Set.Icc b B)
    (hε : |ε * t| ≤ b / 4)
    (hA : AnalyticOnNhd ℂ A (Metric.closedBall (β : ℂ) (β / 2)))
    (hM : ∀ w ∈ Metric.closedBall (β : ℂ) (β / 2), ‖A w‖ ≤ M) (n : ℕ) :
    ‖iteratedDeriv n (fun e : ℝ => rescaledSaddleIntegrand A β t (e : ℂ)) ε‖ ≤
      (n.factorial * M * (4 / b) ^ n) * (1 + |t|) ^ n *
        Real.exp (-(2 * phaseConstant / (9 * B ^ 3)) * t ^ 2) := by
  rw [iteratedDeriv_comp_ofReal_of_analyticAt
    (analyticAt_rescaledSaddleIntegrand (hb.trans_le hβ.1)
      (hε.trans (by linarith [hβ.1])) hA)]
  exact norm_iteratedDeriv_rescaledSaddleIntegrand_le_uniform hb hβ hε hA hM n

end BTZEntropy
