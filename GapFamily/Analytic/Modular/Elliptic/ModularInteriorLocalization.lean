import GapFamily.Analytic.Modular.Elliptic.ModularRectangleEvaluation
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Smooth localization around an interior compact set

Real smooth Urysohn functions supply a genuine compact cutoff equal to one
near any compact subset of the open modular interior. Compactness also gives
one finite logarithmic height bound for the full topological support.
-/

noncomputable section

namespace GapFamily.Analytic.ModularGradient

open Set
open scoped ContDiff

/-- A real smooth cutoff equals one on the closure of an open neighborhood
of a compact set, and has compact topological support inside the given open set. -/
theorem exists_realCutoff_eq_one_on_neighborhood {K U : Set ℂ}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ (χ : ℂ → ℝ) (V : Set ℂ),
      ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ U ∧
      range χ ⊆ Icc 0 1 ∧ IsOpen V ∧ K ⊆ V ∧ closure V ⊆ U ∧
      EqOn χ 1 (closure V) := by
  obtain ⟨V, hV, hKV, hVU, hVc⟩ :=
    exists_open_between_and_isCompact_closure hK hU hKU
  obtain ⟨W, hW, hVW, hWU, hWc⟩ :=
    exists_open_between_and_isCompact_closure hVc hU hVU
  obtain ⟨χ, hχ, hχrange, hχsupport, hχone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := ⊤) hW isClosed_closure hVW
  have hχts : tsupport χ = closure W := by rw [tsupport, hχsupport]
  have hχc : HasCompactSupport χ := by
    change IsCompact (tsupport χ)
    rw [hχts]
    exact hWc
  refine ⟨χ, V, hχ, hχc, hχts ▸ hWU, hχrange, hV, hKV, hVU, ?_⟩
  intro z hz
  exact (hχone z).mp hz

/-- Compact topological support has a strict finite logarithmic height cap;
no nonempty-support or positivity assumption is needed. -/
theorem exists_nonneg_height_cap_of_hasCompactSupport
    {χ : ℂ → ℝ} (hχ : HasCompactSupport χ) :
    ∃ L : ℝ, 0 ≤ L ∧ tsupport χ ⊆ {z : ℂ | z.im < Real.exp L} := by
  obtain ⟨M, hM⟩ := (show IsCompact (tsupport χ) from hχ).bddAbove_image
    Complex.continuous_im.continuousOn
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro z hz
  exact ((hM (mem_image_of_mem Complex.im hz)).trans (le_max_left M 0)).trans_lt
    ((lt_add_one (max M 0)).trans_le (Real.add_one_le_exp (max M 0)))

/-- Every actual compact interior set admits a real globally smooth cutoff
equal to one near the set, with compact support and one nonnegative height cap. -/
theorem exists_modularInteriorCutoff {K : Set ℂ}
    (hK : IsCompact K) (hKU : K ⊆ modularInterior) :
    ∃ (χ : ℂ → ℝ) (V : Set ℂ) (L : ℝ),
      0 ≤ L ∧ ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ modularInterior ∧ range χ ⊆ Icc 0 1 ∧
      IsOpen V ∧ K ⊆ V ∧ closure V ⊆ modularInterior ∧
      EqOn χ 1 (closure V) ∧ tsupport χ ⊆ {z : ℂ | z.im ≤ Real.exp L} := by
  obtain ⟨χ, V, hχ, hχc, hχs, hχrange, hV, hKV, hVU, hχone⟩ :=
    exists_realCutoff_eq_one_on_neighborhood hK isOpen_modularInterior hKU
  obtain ⟨L, hL, hcap⟩ := exists_nonneg_height_cap_of_hasCompactSupport hχc
  refine ⟨χ, V, L, hL, hχ, hχc, hχs, hχrange, hV, hKV, hVU, hχone, ?_⟩
  intro z hz
  exact (show z.im < Real.exp L from hcap hz).le

/-- The literal rectangle used for local graph-norm evaluation has an actual
admissible cutoff whenever it is contained in the modular interior. -/
theorem exists_localEvaluationRectangleCutoff (a b c d : ℝ)
    (hK : localEvaluationRectangle a b c d ⊆ modularInterior) :
    ∃ (χ : ℂ → ℝ) (V : Set ℂ) (L : ℝ),
      0 ≤ L ∧ ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ modularInterior ∧ range χ ⊆ Icc 0 1 ∧
      IsOpen V ∧ localEvaluationRectangle a b c d ⊆ V ∧
      closure V ⊆ modularInterior ∧ EqOn χ 1 (closure V) ∧
      tsupport χ ⊆ {z : ℂ | z.im ≤ Real.exp L} :=
  exists_modularInteriorCutoff (isCompact_localEvaluationRectangle a b c d) hK

end GapFamily.Analytic.ModularGradient
