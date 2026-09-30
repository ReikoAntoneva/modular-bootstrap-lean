import GapFamily.Analytic.Elliptic.FixedPoissonPointBound
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import GapFamily.Analytic.Modular.Elliptic.ModularInteriorCompactUpperSmooth

/-!
# A fixed translated bump for unit-height cusp neighborhoods

The inner radius is three eighths and the outer radius is seven sixteenths.
The strict gap below one half places the entire topological support inside
the desired open lower edge of a unit-height band.
-/

noncomputable section

namespace GapFamily.Analytic.CuspUniformBump

open Set Metric UpperHalfPlane
open scoped ContDiff

def bumpData (p : ℂ) : ContDiffBump p where
  rIn := 3 / 8
  rOut := 7 / 16
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The actual complex-valued fixed-shape bump centered at the physical point. -/
def bump (p : ℂ) (z : ℂ) : ℂ := (bumpData p z : ℝ)

theorem contDiff_bump (p : ℂ) : ContDiff ℝ ∞ (bump p) :=
  Complex.ofRealCLM.contDiff.comp (bumpData p).contDiff

theorem hasCompactSupport_bump (p : ℂ) : HasCompactSupport (bump p) :=
  (bumpData p).hasCompactSupport.comp_left Complex.ofReal_zero

theorem norm_bump_le_one (p z : ℂ) : ‖bump p z‖ ≤ 1 := by
  simpa only [bump, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (bumpData p).nonneg] using (bumpData p).le_one (x := z)

theorem tsupport_bump_subset_closedBall (p : ℂ) :
    tsupport (bump p) ⊆ closedBall p (7 / 16 : ℝ) := by
  calc
    tsupport (bump p) ⊆ tsupport (fun z => bumpData p z) :=
      tsupport_comp_subset Complex.ofReal_zero (bumpData p)
    _ = closedBall p (7 / 16 : ℝ) := (bumpData p).tsupport_eq

theorem bump_eq_translate (p z : ℂ) : bump p z = bump 0 (z - p) := by
  simp only [bump, ContDiffBump.toFun, bumpData, Function.comp_apply, sub_zero]

theorem referenceSquare_norm_lt {z : ℂ}
    (hz : z ∈ FixedPoissonPointBound.referenceSquare) : ‖z‖ < (3 / 8 : ℝ) := by
  have hr : z.re ^ 2 < (1 / 4 : ℝ) ^ 2 := by
    have h := (sq_lt_sq₀ (abs_nonneg z.re) (by norm_num : (0 : ℝ) ≤ 1 / 4)).mpr hz.1
    simpa only [sq_abs] using h
  have hi : z.im ^ 2 < (1 / 4 : ℝ) ^ 2 := by
    have h := (sq_lt_sq₀ (abs_nonneg z.im) (by norm_num : (0 : ℝ) ≤ 1 / 4)).mpr hz.2
    simpa only [sq_abs] using h
  have hn := Complex.sq_norm z
  rw [Complex.normSq_apply] at hn
  nlinarith [norm_nonneg z]

/-- The plateau contains the whole translated quarter-square. -/
theorem bump_eq_one_on_referenceSquare (p : ℂ) :
    EqOn (bump p) 1 {z : ℂ | z - p ∈ FixedPoissonPointBound.referenceSquare} := by
  intro z hz
  have hm : z ∈ closedBall p (bumpData p).rIn := by
    rw [mem_closedBall_iff_norm]
    exact (referenceSquare_norm_lt hz).le
  simpa only [bump, Pi.one_apply, Complex.ofReal_one] using
    congrArg Complex.ofReal ((bumpData p).one_of_mem_closedBall hm)

/-- Every support point lies in the fixed horizontal range and the literal
unit-height band with strict lower edge. -/
theorem tsupport_bump_coordinate_bounds {p : ℂ} (hp : |p.re| ≤ (1 / 2 : ℝ))
    {z : ℂ} (hz : z ∈ tsupport (bump p)) :
    |z.re| ≤ 1 ∧ p.im - 1 / 2 < z.im ∧ z.im ≤ (p.im - 1 / 2) + 1 := by
  have hn : ‖z - p‖ ≤ (7 / 16 : ℝ) :=
    mem_closedBall_iff_norm.mp (tsupport_bump_subset_closedBall p hz)
  have hr : |z.re - p.re| ≤ (7 / 16 : ℝ) := by
    simpa only [Complex.sub_re] using (Complex.abs_re_le_norm (z - p)).trans hn
  have hi : |z.im - p.im| ≤ (7 / 16 : ℝ) := by
    simpa only [Complex.sub_im] using (Complex.abs_im_le_norm (z - p)).trans hn
  constructor
  · have htri := abs_add_le (z.re - p.re) p.re
    rw [sub_add_cancel] at htri
    linarith
  · exact ⟨by linarith [(abs_le.mp hi).1], by linarith [(abs_le.mp hi).2]⟩

theorem one_le_lowerHeight {p : ℂ} (hp : 2 ≤ p.im) : 1 ≤ p.im - 1 / 2 := by
  linarith

theorem tsupport_bump_subset_upperHalfPlane {p : ℂ} (hp : 2 ≤ p.im) :
    tsupport (bump p) ⊆ upperHalfPlaneSet := by
  intro z hz
  have hn : ‖z - p‖ ≤ (7 / 16 : ℝ) :=
    mem_closedBall_iff_norm.mp (tsupport_bump_subset_closedBall p hz)
  have hi : |z.im - p.im| ≤ (7 / 16 : ℝ) := by
    simpa only [Complex.sub_im] using (Complex.abs_im_le_norm (z - p)).trans hn
  change 0 < z.im
  linarith [(abs_le.mp hi).1]

theorem isOpen_translatedReferenceSquare (p : ℂ) :
    IsOpen {z : ℂ | z - p ∈ FixedPoissonPointBound.referenceSquare} :=
  FixedPoissonPointBound.isOpen_referenceSquare.preimage (continuous_id.sub continuous_const)

theorem translatedReferenceSquare_subset_high {p : ℂ} (hp : 2 ≤ p.im) :
    {z : ℂ | z - p ∈ FixedPoissonPointBound.referenceSquare} ⊆
      {z : ℂ | 1 < z.im} := by
  intro z hz
  have hi : |z.im - p.im| < (1 / 4 : ℝ) := by
    simpa only [Complex.sub_im] using hz.2
  change 1 < z.im
  linarith [(abs_lt.mp hi).1]

end GapFamily.Analytic.CuspUniformBump
