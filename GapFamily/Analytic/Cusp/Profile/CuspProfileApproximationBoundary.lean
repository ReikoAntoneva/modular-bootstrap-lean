import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic.Linarith

/-!
# Boundary control for cusp profile approximation

A smooth profile vanishing at height one has linear growth from that boundary
on a fixed collar. Multiplying a profile smooth only at positive heights by a
smooth cutoff supported above height one gives a globally smooth function.
-/

namespace GapFamily.Analytic

open Set
open scoped ContDiff

/-- A profile vanishing at height one is bounded by a constant times its
distance from that height throughout the collar `[1,2]`. -/
theorem exists_cuspProfile_boundary_bound {b : ℝ → ℂ}
    (hb : ContDiffOn ℝ ∞ b (Ioi 0)) (hb1 : b 1 = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ Icc (1 : ℝ) 2, ‖b y‖ ≤ C * (y - 1) := by
  have hsub : Icc (1 : ℝ) 2 ⊆ Ioi 0 := fun y hy => lt_of_lt_of_le zero_lt_one hy.1
  have hd : ContinuousOn (deriv b) (Icc (1 : ℝ) 2) :=
    (hb.continuousOn_deriv_of_isOpen isOpen_Ioi (by simp)).mono hsub
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hd
  have hC0 : 0 ≤ C := (norm_nonneg (deriv b 1)).trans (hC 1 (by norm_num))
  refine ⟨C, hC0, ?_⟩
  have hderiv : ∀ y ∈ Icc (1 : ℝ) 2, HasDerivWithinAt b (deriv b y) (Icc 1 2) y := by
    intro y hy
    exact ((hb.contDiffAt (isOpen_Ioi.mem_nhds (hsub hy))).differentiableAt
      (by simp)).hasDerivAt.hasDerivWithinAt
  intro y hy
  simpa only [hb1, sub_zero] using
    norm_image_sub_le_of_norm_deriv_le_segment' hderiv
      (fun t ht => hC t (Ico_subset_Icc_self ht)) y hy

/-- A smooth cutoff supported above height one makes a profile that is
smooth at positive heights globally smooth. -/
theorem contDiff_cuspProfile_cutoff_mul {b : ℝ → ℂ} {χ : ℝ → ℝ}
    (hb : ContDiffOn ℝ ∞ b (Ioi 0)) (hχ : ContDiff ℝ ∞ χ)
    (hs : tsupport χ ⊆ Ioi (1 : ℝ)) :
    ContDiff ℝ ∞ (fun y => χ y • b y) := by
  apply contDiff_iff_contDiffAt.mpr
  intro y
  by_cases hy : y ∈ tsupport χ
  · have hy0 : y ∈ Ioi (0 : ℝ) := lt_trans (zero_lt_one : (0 : ℝ) < 1) (hs hy)
    exact hχ.contDiffAt.smul (hb.contDiffAt (isOpen_Ioi.mem_nhds hy0))
  · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hy] with t ht
    simp only [Pi.zero_apply] at ht
    simp only [ht, zero_smul]

/-- Multiplication by an arbitrary profile preserves the cutoff's compact
support. No regularity of the profile is needed for this support statement. -/
theorem hasCompactSupport_cuspProfile_cutoff_mul {b : ℝ → ℂ} {χ : ℝ → ℝ}
    (hχ : HasCompactSupport χ) : HasCompactSupport (fun y => χ y • b y) :=
  hχ.smul_right

/-- The full topological support of a cut off profile stays above height one. -/
theorem tsupport_cuspProfile_cutoff_mul {b : ℝ → ℂ} {χ : ℝ → ℝ}
    (hχ : tsupport χ ⊆ Ioi (1 : ℝ)) :
    tsupport (fun y => χ y • b y) ⊆ Ioi (1 : ℝ) :=
  (tsupport_smul_subset_left χ b).trans hχ

end GapFamily.Analytic
