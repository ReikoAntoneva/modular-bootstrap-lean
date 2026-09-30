import GapFamily.Analytic.Modular.Geometry.ModularTruncatedCutoff
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

noncomputable section
namespace GapFamily.Analytic
open Set UpperHalfPlane
open scoped ContDiff ComplexOrder

def cuspTranslationWeight (x : ℝ) : ℝ :=
  Real.smoothTransition (x + 1/2) - Real.smoothTransition (x - 1/2)

theorem contDiff_cuspTranslationWeight : ContDiff ℝ ∞ cuspTranslationWeight :=
  (Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)).sub
    (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const))

theorem cuspTranslationWeight_zero_left {x : ℝ} (hx : x ≤ -1/2) :
    cuspTranslationWeight x = 0 := by
  rw [cuspTranslationWeight, Real.smoothTransition.zero_of_nonpos (by linarith),
    Real.smoothTransition.zero_of_nonpos (by linarith), sub_self]

theorem cuspTranslationWeight_zero_right {x : ℝ} (hx : 3/2 ≤ x) :
    cuspTranslationWeight x = 0 := by
  rw [cuspTranslationWeight, Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.one_of_one_le (by linarith), sub_self]

theorem cuspTranslationWeight_tsupport_subset :
    tsupport cuspTranslationWeight ⊆ Icc (-1/2 : ℝ) (3/2) := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  constructor
  · by_contra h
    exact hx (cuspTranslationWeight_zero_left (le_of_lt (lt_of_not_ge h)))
  · by_contra h
    exact hx (cuspTranslationWeight_zero_right (le_of_lt (lt_of_not_ge h)))

theorem cuspTranslationWeight_hasCompactSupport : HasCompactSupport cuspTranslationWeight :=
  isCompact_Icc.of_isClosed_subset isClosed_closure cuspTranslationWeight_tsupport_subset

theorem cuspTranslationWeight_partition {x : ℝ} (hx : x ∈ Icc (-1/2 : ℝ) (1/2)) :
    cuspTranslationWeight x + cuspTranslationWeight (x + 1) = 1 := by
  simp only [cuspTranslationWeight]
  rw [Real.smoothTransition.zero_of_nonpos (x := x - 1/2) (by linarith [hx.2]),
    Real.smoothTransition.one_of_one_le (x := x + 1 + 1/2) (by linarith [hx.1]),
    show x + 1 - 1 / 2 = x + 1 / 2 by ring]
  ring

theorem cuspTranslationWeight_translate_zero {x : ℝ}
    (hx : x ∈ Icc (-1/2 : ℝ) (1/2)) {n : ℤ} (hn0 : n ≠ 0) (hn1 : n ≠ 1) :
    cuspTranslationWeight (x + n) = 0 := by
  have hn : n ≤ -1 ∨ 2 ≤ n := by omega
  rcases hn with hn | hn
  · have hn' : (n : ℝ) ≤ -1 := by exact_mod_cast hn
    exact cuspTranslationWeight_zero_left (by linarith [hx.2])
  · have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    exact cuspTranslationWeight_zero_right (by linarith [hx.1])

def cuspProfileSeed (b : ℝ → ℂ) (z : ℂ) : ℂ :=
  (cuspTranslationWeight z.re : ℂ) * b z.im

theorem contDiff_cuspProfileSeed {b : ℝ → ℂ} (hb : ContDiff ℝ ∞ b) :
    ContDiff ℝ ∞ (cuspProfileSeed b) :=
  (Complex.ofRealCLM.contDiff.comp
    (contDiff_cuspTranslationWeight.comp Complex.reCLM.contDiff)).mul
      (hb.comp Complex.imCLM.contDiff)

theorem cuspProfileSeed_tsupport_subset {b : ℝ → ℂ} (hc : HasCompactSupport b) :
    tsupport (cuspProfileSeed b) ⊆ (Icc (-1/2 : ℝ) (3/2)) ×ℂ tsupport b := by
  apply closure_minimal _ (isCompact_Icc.reProdIm hc).isClosed
  intro z hz
  have hmul : (cuspTranslationWeight z.re : ℂ) * b z.im ≠ 0 := hz
  have hparts := mul_ne_zero_iff.mp hmul
  refine ⟨cuspTranslationWeight_tsupport_subset (subset_tsupport _ ?_),
    subset_tsupport _ hparts.2⟩
  exact fun h => hparts.1 (by simp only [h, Complex.ofReal_zero])

theorem cuspProfileSeed_hasCompactSupport {b : ℝ → ℂ} (hc : HasCompactSupport b) :
    HasCompactSupport (cuspProfileSeed b) :=
  (isCompact_Icc.reProdIm hc).of_isClosed_subset isClosed_closure
    (cuspProfileSeed_tsupport_subset hc)

theorem cuspProfileSeed_upper_support {b : ℝ → ℂ} (hc : HasCompactSupport b)
    (hs : tsupport b ⊆ Ioi (1 : ℝ)) :
    tsupport (cuspProfileSeed b) ⊆ upperHalfPlaneSet := by
  intro z hz
  have h := hs (cuspProfileSeed_tsupport_subset hc hz).2
  change 1 < z.im at h
  change 0 < z.im
  linarith

theorem cuspProfileSeed_partition (b : ℝ → ℂ) {z : ℂ}
    (hz : z.re ∈ Icc (-1/2 : ℝ) (1/2)) :
    cuspProfileSeed b z + cuspProfileSeed b (z + 1) = b z.im := by
  simp only [cuspProfileSeed, Complex.add_re, Complex.one_re, Complex.add_im,
    Complex.one_im, add_zero]
  rw [← add_mul, ← Complex.ofReal_add, cuspTranslationWeight_partition hz]
  simp only [Complex.ofReal_one, one_mul]

end GapFamily.Analytic
