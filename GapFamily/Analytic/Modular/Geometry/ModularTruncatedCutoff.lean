import GapFamily.Analytic.Modular.Elliptic.ModularInteriorCompactUpperSmooth
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Actual smooth cutoff around a compact truncated domain

A compact subset of an open region in the complex plane admits a globally
smooth, compactly supported complex cutoff equal to one on that subset. The
construction first chooses an intermediate open set with compact closure and
then applies the smooth Urysohn theorem. In particular, no cutoff-existence
assumption is needed for a compact subset of the upper half-plane.
-/

noncomputable section

namespace GapFamily.Analytic.ModularGradient

open Set UpperHalfPlane
open scoped ContDiff

/-- A genuine complex-valued smooth cutoff of a compact subset of an open
region, with its full topological support contained in that region. -/
theorem exists_complexCutoff_eq_one {T U : Set ℂ} (hT : IsCompact T)
    (hU : IsOpen U) (hTU : T ⊆ U) :
    ∃ χ : ℂ → ℂ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ U ∧ EqOn χ 1 T := by
  obtain ⟨V, hV, hTV, hVU, hVc⟩ :=
    exists_open_between_and_isCompact_closure hT hU hTU
  obtain ⟨f, hf, _, hfs, hfone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := ⊤) hV hT.isClosed hTV
  have hts : tsupport f = closure V := by rw [tsupport, hfs]
  have hfc : HasCompactSupport f := by
    change IsCompact (tsupport f)
    rw [hts]
    exact hVc
  refine ⟨fun z => (f z : ℂ), Complex.ofRealCLM.contDiff.comp hf,
    hfc.comp_left Complex.ofReal_zero, ?_, ?_⟩
  · exact (tsupport_comp_subset Complex.ofReal_zero f).trans (hts ▸ hVU)
  · intro z hz
    simpa only [Pi.one_apply, Complex.ofReal_one] using
      congrArg (fun r : ℝ => (r : ℂ)) ((hfone z).mp hz)

/-- Every actual compact subset of the upper half-plane has an admissible
cutoff for the completed modular cutoff operator, equal to one on the set. -/
theorem exists_upperCutoff_eq_one {T : Set ℂ} (hT : IsCompact T)
    (hTU : T ⊆ upperHalfPlaneSet) :
    ∃ χ : ℂ → ℂ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ upperHalfPlaneSet ∧ EqOn χ 1 T :=
  exists_complexCutoff_eq_one hT isOpen_upperHalfPlaneSet hTU

end GapFamily.Analytic.ModularGradient
