import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Geometry of the canonical continuation region

The right half-plane with the point 1/2 removed is the union of four
overlapping convex regions. Adding any positive-radius disk at zero
therefore gives an open preconnected continuation region.
-/

noncomputable section

namespace GapFamily.Analytic.PoincareCanonical

open Set Complex

def continuationRegion (r : ℝ) : Set ℂ :=
  Metric.ball 0 r ∪ {κ : ℂ | 0 < κ.re ∧ κ ≠ (1 / 2 : ℂ)}

theorem isOpen_continuationRegion (r : ℝ) : IsOpen (continuationRegion r) :=
  Metric.isOpen_ball.union
    ((isOpen_lt continuous_const Complex.continuous_re).inter
      isOpen_ne)

theorem isPreconnected_puncturedRightHalfPlane :
    IsPreconnected {κ : ℂ | 0 < κ.re ∧ κ ≠ (1 / 2 : ℂ)} := by
  let A : Set ℂ := {κ | 0 < κ.re ∧ 0 < κ.im}
  let B : Set ℂ := {κ | 0 < κ.re ∧ κ.re < (1 / 2 : ℝ)}
  let C : Set ℂ := {κ | 0 < κ.re ∧ κ.im < 0}
  let D : Set ℂ := {κ | (1 / 2 : ℝ) < κ.re}
  have hA : IsPreconnected A :=
    ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_gt 0)).isPreconnected
  have hB : IsPreconnected B :=
    ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_re_lt (1 / 2))).isPreconnected
  have hC : IsPreconnected C :=
    ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_lt 0)).isPreconnected
  have hD : IsPreconnected D := (convex_halfSpace_re_gt (1 / 2)).isPreconnected
  have hAB : IsPreconnected (A ∪ B) := by
    apply IsPreconnected.union' _ hA hB
    exact ⟨(1 / 4 : ℂ) + Complex.I, by norm_num [A, B]⟩
  have hABC : IsPreconnected ((A ∪ B) ∪ C) := by
    apply IsPreconnected.union' _ hAB hC
    exact ⟨(1 / 4 : ℂ) - Complex.I, by norm_num [A, B, C]⟩
  have hABCD : IsPreconnected (((A ∪ B) ∪ C) ∪ D) := by
    apply IsPreconnected.union' _ hABC hD
    exact ⟨(1 : ℂ) + Complex.I, by norm_num [A, B, C, D]⟩
  have he : {κ : ℂ | 0 < κ.re ∧ κ ≠ (1 / 2 : ℂ)} = ((A ∪ B) ∪ C) ∪ D := by
    ext κ
    simp only [A, B, C, D, Set.mem_union, Set.mem_ofPred_eq]
    constructor
    · intro h
      by_cases hpos : 0 < κ.im
      · exact Or.inl (Or.inl (Or.inl ⟨h.1, hpos⟩))
      by_cases hneg : κ.im < 0
      · exact Or.inl (Or.inr ⟨h.1, hneg⟩)
      have him : κ.im = 0 := le_antisymm (le_of_not_gt hpos) (le_of_not_gt hneg)
      have hre : κ.re ≠ (1 / 2 : ℝ) := by
        intro heq
        apply h.2
        apply Complex.ext
        · simpa using heq
        · simpa using him
      rcases lt_or_gt_of_ne hre with hlt | hgt
      · exact Or.inl (Or.inl (Or.inr ⟨h.1, hlt⟩))
      · exact Or.inr hgt
    · intro h
      rcases h with ((h | h) | h) | h
      · refine ⟨h.1, ?_⟩
        intro heq
        rw [heq] at h
        norm_num at h
      · refine ⟨h.1, ?_⟩
        intro heq
        rw [heq] at h
        norm_num at h
      · refine ⟨h.1, ?_⟩
        intro heq
        rw [heq] at h
        norm_num at h
      · refine ⟨by linarith, ?_⟩
        intro heq
        rw [heq] at h
        norm_num at h
  rw [he]
  exact hABCD

theorem isPreconnected_continuationRegion {r : ℝ} (hr : 0 < r) :
    IsPreconnected (continuationRegion r) := by
  let t : ℝ := min (r / 2) (1 / 4)
  have ht : 0 < t := lt_min (half_pos hr) (by norm_num)
  have htr : t < r := (min_le_left _ _).trans_lt (half_lt_self hr)
  have hthalf : t < (1 / 2 : ℝ) := (min_le_right _ _).trans_lt (by norm_num)
  apply IsPreconnected.union' _ Metric.isPreconnected_ball
    isPreconnected_puncturedRightHalfPlane
  refine ⟨(t : ℂ), ?_, ?_⟩
  · simpa only [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ht] using htr
  · refine ⟨ht, ?_⟩
    intro heq
    have hh := congrArg Complex.re heq
    norm_num at hh
    linarith

theorem continuationRegion_mono {r R : ℝ} (h : r ≤ R) :
    continuationRegion r ⊆ continuationRegion R :=
  union_subset_union (Metric.ball_subset_ball h) Subset.rfl

end GapFamily.Analytic.PoincareCanonical
