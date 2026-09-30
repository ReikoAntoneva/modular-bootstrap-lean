import BTZEntropy.Comparison.SpinComplexBound
import Mathlib.Analysis.Complex.SummableUniformlyOn
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Normally convergent complex spin image sum

A uniform `|n|^(-3/2)` bound on every closed right half-plane gives normal
convergence of the actual image series. Its holomorphic sum restricts on the
positive real axis to the previously proved integer-image sum.
-/

noncomputable section

open Filter Set
open scoped Topology

namespace BTZEntropy

/-- The actual complex image with its central term removed. -/
def complexSpinTail (a : ℝ) (z : ℂ) (n : ℤ) : ℂ :=
  if n = 0 then 0 else complexSpinImage a z n

def complexSpinImageSum (a : ℝ) (z : ℂ) : ℂ := ∑' n : ℤ, complexSpinImage a z n

def complexSpinTailSum (a : ℝ) (z : ℂ) : ℂ := ∑' n : ℤ, complexSpinTail a z n

/-- The majorant constant depends only on the lower real-part bound. -/
def complexSpinStripConstant (a ε : ℝ) : ℝ :=
  spinNullBound ε ^ 2 * ε ^ (-(3 / 2 : ℝ)) * Real.exp (2 * Real.pi * a / ε)

private theorem summable_stripMajorant (a ε : ℝ) :
    Summable (fun n : ℤ => complexSpinStripConstant a ε * |(n : ℝ)| ^ (-(3 / 2 : ℝ))) :=
  (Real.summable_abs_int_rpow (by norm_num : (1 : ℝ) < 3 / 2)).mul_left _

theorem norm_complexSpinTail_le_strip {a ε : ℝ} (ha : 0 ≤ a) (hε : 0 < ε)
    {z : ℂ} (hz : ε ≤ z.re) (n : ℤ) :
    ‖complexSpinTail a z n‖ ≤
      complexSpinStripConstant a ε * |(n : ℝ)| ^ (-(3 / 2 : ℝ)) := by
  by_cases hn : n = 0
  · simp [complexSpinTail, hn, complexSpinStripConstant]
  · simpa only [complexSpinTail, ite_eq_right hn, complexSpinStripConstant] using
      norm_complexSpinImage_le_strip ha hε hz hn

theorem summable_norm_complexSpinTail {a : ℝ} (ha : 0 ≤ a) {z : ℂ} (hz : 0 < z.re) :
    Summable (fun n : ℤ => ‖complexSpinTail a z n‖) :=
  (summable_stripMajorant a z.re).of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_complexSpinTail_le_strip ha hz le_rfl)

theorem summable_complexSpinImage {a : ℝ} (ha : 0 ≤ a) {z : ℂ} (hz : 0 < z.re) :
    Summable (fun n : ℤ => complexSpinImage a z n) := by
  apply (summable_norm_complexSpinTail ha hz).of_norm.congr_cofinite
  filter_upwards [eventually_cofinite_ne (0 : ℤ)] with n hn
  simp only [complexSpinTail, ite_eq_right hn]

theorem hasSumUniformlyOn_complexSpinTail_strip {a ε : ℝ} (ha : 0 ≤ a) (hε : 0 < ε) :
    HasSumUniformlyOn (fun n : ℤ => fun z : ℂ => complexSpinTail a z n)
      (complexSpinTailSum a) {z : ℂ | ε ≤ z.re} := by
  apply hasSumUniformlyOn_iff_tendstoUniformlyOn.mpr
  exact tendstoUniformlyOn_tsum (summable_stripMajorant a ε)
    (fun n _ hz => norm_complexSpinTail_le_strip ha hε hz n)

theorem hasSumUniformlyOn_complexSpinImage_strip {a ε : ℝ} (ha : 0 ≤ a) (hε : 0 < ε) :
    HasSumUniformlyOn (fun n : ℤ => fun z : ℂ => complexSpinImage a z n)
      (complexSpinImageSum a) {z : ℂ | ε ≤ z.re} := by
  apply hasSumUniformlyOn_iff_tendstoUniformlyOn.mpr
  apply tendstoUniformlyOn_tsum_of_cofinite_eventually (summable_stripMajorant a ε)
  filter_upwards [eventually_cofinite_ne (0 : ℤ)] with n hn
  intro z hz
  exact norm_complexSpinImage_le_strip ha hε hz hn

private theorem strip_mem_nhdsWithin {z : ℂ} (hz : 0 < z.re) :
    {w : ℂ | z.re / 2 ≤ w.re} ∈ 𝓝[{w : ℂ | 0 < w.re}] z := by
  apply mem_nhdsWithin_of_mem_nhds
  have hn : {w : ℂ | z.re / 2 < w.re} ∈ 𝓝 z :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by dsimp; linarith)
  exact mem_of_superset hn (fun w h => show z.re / 2 ≤ w.re from le_of_lt h)

theorem hasSumLocallyUniformlyOn_complexSpinImage {a : ℝ} (ha : 0 ≤ a) :
    HasSumLocallyUniformlyOn (fun n : ℤ => fun z : ℂ => complexSpinImage a z n)
      (complexSpinImageSum a) {z : ℂ | 0 < z.re} := by
  apply hasSumLocallyUniformlyOn_of_of_forall_exists_nhds
  intro z hz
  exact ⟨{w : ℂ | z.re / 2 ≤ w.re}, strip_mem_nhdsWithin hz,
    hasSumUniformlyOn_complexSpinImage_strip ha (by dsimp at hz; linarith)⟩

theorem hasSumLocallyUniformlyOn_complexSpinTail {a : ℝ} (ha : 0 ≤ a) :
    HasSumLocallyUniformlyOn (fun n : ℤ => fun z : ℂ => complexSpinTail a z n)
      (complexSpinTailSum a) {z : ℂ | 0 < z.re} := by
  apply hasSumLocallyUniformlyOn_of_of_forall_exists_nhds
  intro z hz
  exact ⟨{w : ℂ | z.re / 2 ≤ w.re}, strip_mem_nhdsWithin hz,
    hasSumUniformlyOn_complexSpinTail_strip ha (by dsimp at hz; linarith)⟩

theorem analyticOnNhd_complexSpinImageSum {a : ℝ} (ha : 0 ≤ a) :
    AnalyticOnNhd ℂ (complexSpinImageSum a) {z : ℂ | 0 < z.re} := by
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  exact ((hasSumLocallyUniformlyOn_complexSpinImage ha).summableLocallyUniformlyOn.differentiableOn
    hopen (fun n _ hz => (analyticAt_complexSpinImage a hz n).differentiableAt)).analyticOnNhd hopen

theorem analyticOnNhd_complexSpinTailSum {a : ℝ} (ha : 0 ≤ a) :
    AnalyticOnNhd ℂ (complexSpinTailSum a) {z : ℂ | 0 < z.re} := by
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  apply ((hasSumLocallyUniformlyOn_complexSpinTail ha).summableLocallyUniformlyOn.differentiableOn
    hopen ?_).analyticOnNhd hopen
  intro n z hz
  by_cases hn : n = 0
  · simp only [complexSpinTail, ite_eq_left hn]
    exact differentiableAt_const _
  · simpa only [complexSpinTail, ite_eq_right hn] using
      (analyticAt_complexSpinImage a hz n).differentiableAt

theorem complexSpinImageSum_eq_central_add_tail {a : ℝ} (ha : 0 ≤ a)
    {z : ℂ} (hz : 0 < z.re) :
    complexSpinImageSum a z = complexSpinImage a z 0 + complexSpinTailSum a z := by
  exact (summable_complexSpinImage ha hz).tsum_eq_add_tsum_ite (0 : ℤ)

theorem complexSpinTail_ofReal {y : ℝ} (hy : 0 < y) (a : ℝ) (n : ℤ) :
    complexSpinTail a (y : ℂ) n = spinImageTail a y n / (Real.sqrt y : ℂ) := by
  by_cases hn : n = 0
  · simp [complexSpinTail, spinImageTail, hn]
  · simp only [complexSpinTail, spinImageTail, ite_eq_right hn, complexSpinImage_ofReal hy]

/-- The restriction is the same actual integer-image series, with its normalization. -/
theorem complexSpinImageSum_ofReal {y : ℝ} (hy : 0 < y) (a : ℝ) :
    complexSpinImageSum a (y : ℂ) =
      (∑' n : ℤ, spinImageKernel a y (n : ℝ)) / (Real.sqrt y : ℂ) := by
  simp only [complexSpinImageSum, complexSpinImage_ofReal hy, tsum_div_const]

theorem complexSpinTailSum_ofReal {y : ℝ} (hy : 0 < y) (a : ℝ) :
    complexSpinTailSum a (y : ℂ) =
      (∑' n : ℤ, spinImageTail a y n) / (Real.sqrt y : ℂ) := by
  simp only [complexSpinTailSum, complexSpinTail_ofReal hy, tsum_div_const]

end BTZEntropy
