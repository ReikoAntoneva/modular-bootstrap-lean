import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv

noncomputable section
namespace GapFamily.Analytic.SpatialPoint

open Set Filter
open scoped Topology ContDiff ComplexConjugate

def pointParameter (z w : ℂ) : ℝ :=
  1 + Complex.normSq (z - w) / (4 * z.im * w.im)

def pointKernel (s : ℂ) (z w : ℂ) : ℂ :=
  (1 / 4 : ℂ) * (pointParameter z w : ℂ) ^ (-s)

theorem pointParameter_ge_one {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    1 ≤ pointParameter z w := by
  unfold pointParameter
  have h : 0 ≤ Complex.normSq (z - w) / (4 * z.im * w.im) :=
    div_nonneg (Complex.normSq_nonneg _) (by positivity)
  linarith

theorem pointParameter_pos {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    0 < pointParameter z w := lt_of_lt_of_le zero_lt_one (pointParameter_ge_one hz hw)

theorem pointParameter_eq_normSq_sub_conj {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    pointParameter z w = Complex.normSq (z - conj w) / (4 * z.im * w.im) := by
  unfold pointParameter
  field_simp [ne_of_gt hz, ne_of_gt hw]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im]
  ring

theorem pointParameter_symm (z w : ℂ) : pointParameter z w = pointParameter w z := by
  unfold pointParameter
  have h : Complex.normSq (z - w) = Complex.normSq (w - z) := by
    rw [← neg_sub w z, Complex.normSq_neg]
  rw [h]
  congr 2
  ring

theorem pointKernel_symm (s z w : ℂ) : pointKernel s z w = pointKernel s w z := by
  rw [pointKernel, pointKernel, pointParameter_symm]

theorem pointKernel_eq_exp (s : ℂ) {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    pointKernel s z w = (1 / 4 : ℂ) *
      Complex.exp ((Real.log (pointParameter z w) : ℂ) * (-s)) := by
  rw [pointKernel, Complex.cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr (pointParameter_pos hz hw).ne'),
    ← Complex.ofReal_log (pointParameter_pos hz hw).le]

theorem pointParameter_contDiffAt_of_ne_zero {z w : ℂ} (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    ContDiffAt ℝ ∞ (fun p : ℂ × ℂ => pointParameter p.1 p.2) (z, w) := by
  have hd : ContDiff ℝ ∞ (fun p : ℂ × ℂ => p.1 - p.2) := contDiff_fst.sub contDiff_snd
  have hr := Complex.reCLM.contDiff.comp hd
  have hi := Complex.imCLM.contDiff.comp hd
  have hn : ContDiff ℝ ∞ (fun p : ℂ × ℂ => Complex.normSq (p.1 - p.2)) := by
    simpa only [Function.comp_def, Complex.normSq_apply, Complex.reCLM_apply, Complex.imCLM_apply] using
      (hr.mul hr).add (hi.mul hi)
  have hz' : ContDiff ℝ ∞ (fun p : ℂ × ℂ => p.1.im) :=
    Complex.imCLM.contDiff.comp contDiff_fst
  have hw' : ContDiff ℝ ∞ (fun p : ℂ × ℂ => p.2.im) :=
    Complex.imCLM.contDiff.comp contDiff_snd
  exact contDiffAt_const.add (hn.contDiffAt.div
    ((contDiff_const.mul hz').mul hw').contDiffAt
    (mul_ne_zero (mul_ne_zero (by norm_num) hz) hw))

theorem pointParameter_contDiffAt {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    ContDiffAt ℝ ∞ (fun p : ℂ × ℂ => pointParameter p.1 p.2) (z, w) :=
  pointParameter_contDiffAt_of_ne_zero hz.ne' hw.ne'

theorem pointParameter_contDiffAt_left_of_ne_zero {z w : ℂ}
    (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    ContDiffAt ℝ ∞ (fun z : ℂ => pointParameter z w) z :=
  ContDiffAt.comp₂ (g := fun p : ℂ × ℂ => pointParameter p.1 p.2)
    (pointParameter_contDiffAt_of_ne_zero hz hw) contDiffAt_id contDiffAt_const

theorem pointParameter_contDiffAt_left {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    ContDiffAt ℝ ∞ (fun z : ℂ => pointParameter z w) z :=
  pointParameter_contDiffAt_left_of_ne_zero hz.ne' hw.ne'

theorem pointKernel_contDiffAt (s : ℂ) {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    ContDiffAt ℝ ∞ (fun p : ℂ × ℂ => pointKernel s p.1 p.2) (z, w) := by
  have hp := pointParameter_contDiffAt hz hw
  have hl := (Real.contDiffAt_log.mpr (pointParameter_pos hz hw).ne').comp (z, w) hp
  have he : ContDiffAt ℝ ∞ (fun p : ℂ × ℂ =>
      (1 / 4 : ℂ) * Complex.exp ((Real.log (pointParameter p.1 p.2) : ℂ) * (-s))) (z, w) :=
    contDiffAt_const.mul ((Complex.contDiff_exp (𝕜 := ℝ)).contDiffAt.comp (z, w)
      ((Complex.ofRealCLM.contDiff.contDiffAt.comp (z, w) hl).mul contDiffAt_const))
  apply he.congr_of_eventuallyEq
  have hzne : ∀ᶠ p : ℂ × ℂ in 𝓝 (z, w), 0 < p.1.im :=
    (isOpen_lt continuous_const (Complex.continuous_im.comp continuous_fst)).mem_nhds hz
  have hwne : ∀ᶠ p : ℂ × ℂ in 𝓝 (z, w), 0 < p.2.im :=
    (isOpen_lt continuous_const (Complex.continuous_im.comp continuous_snd)).mem_nhds hw
  filter_upwards [hzne, hwne] with p hpz hpw
  exact pointKernel_eq_exp s hpz hpw

theorem pointKernel_contDiffAt_left (s : ℂ) {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    ContDiffAt ℝ ∞ (fun z : ℂ => pointKernel s z w) z :=
  ContDiffAt.comp₂ (g := fun p : ℂ × ℂ => pointKernel s p.1 p.2)
    (pointKernel_contDiffAt s hz hw) contDiffAt_id contDiffAt_const

theorem pointKernel_conj (s : ℂ) {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    conj (pointKernel s z w) = pointKernel (conj s) z w := by
  rw [pointKernel_eq_exp s hz hw, pointKernel_eq_exp (conj s) hz hw]
  simp only [map_mul, map_div₀, map_one, map_ofNat, ← Complex.exp_conj, map_neg,
    Complex.conj_ofReal]

theorem pointKernel_hermitian (s : ℝ) {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    conj (pointKernel (s : ℂ) z w) = pointKernel (s : ℂ) w z := by
  rw [pointKernel_conj _ hz hw, Complex.conj_ofReal, pointKernel_symm]

end GapFamily.Analytic.SpatialPoint
