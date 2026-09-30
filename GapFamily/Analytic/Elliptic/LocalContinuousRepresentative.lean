import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.MeasureTheory.Measure.OpenPos

noncomputable section

namespace GapFamily.Analytic

open Set MeasureTheory Filter
open scoped Topology

/-- Locally continuous representatives of one function glue on an open set.
The representatives agree pointwise on overlaps because volume is positive on open sets. -/
theorem exists_continuousOn_ae_eq_of_locally
    (U : Set ℂ) (hU : IsOpen U) (f : ℂ → ℂ)
    (hlocal : ∀ z ∈ U, ∃ V : Set ℂ, IsOpen V ∧ z ∈ V ∧ V ⊆ U ∧
      ∃ G : ℂ → ℂ, ContinuousOn G V ∧ G =ᵐ[volume.restrict V] f) :
    ∃ G : ℂ → ℂ, ContinuousOn G U ∧ G =ᵐ[volume.restrict U] f := by
  classical
  choose V hVo hxV hVU g hgc hgf using fun z : U => hlocal z z.property
  have hagree (x y : U) : EqOn (g x) (g y) (V x ∩ V y) := by
    have hx : g x =ᵐ[volume.restrict (V x ∩ V y)] f :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_left (hgf x)
    have hy : g y =ᵐ[volume.restrict (V x ∩ V y)] f :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_right (hgf y)
    exact Measure.eqOn_open_of_ae_eq (μ := volume) (hx.trans hy.symm)
      ((hVo x).inter (hVo y))
      ((hgc x).mono inter_subset_left) ((hgc y).mono inter_subset_right)
  let G : ℂ → ℂ := fun z => if hz : z ∈ U then g ⟨z, hz⟩ z else 0
  have heq (x : U) : EqOn G (g x) (V x) := by
    intro z hz
    have hzU := hVU x hz
    dsimp [G]
    rw [dite_eq_left hzU]
    exact hagree ⟨z, hzU⟩ x ⟨hxV ⟨z, hzU⟩, hz⟩
  have hGc : ContinuousOn G U := by
    apply hU.continuousOn_iff.mpr
    intro z hz
    have hcont : ContinuousOn G (V ⟨z, hz⟩) := (hgc ⟨z, hz⟩).congr (heq ⟨z, hz⟩)
    exact hcont.continuousAt ((hVo ⟨z, hz⟩).mem_nhds (hxV ⟨z, hz⟩))
  have hGf (x : U) : G =ᵐ[volume.restrict (V x)] f := by
    filter_upwards [ae_restrict_mem (hVo x).measurableSet, hgf x] with z hz hzf
    exact (heq x hz).trans hzf
  obtain ⟨s, hs, hcover⟩ := (HereditarilyLindelofSpace.isLindelof U).elim_countable_subcover
    V hVo (fun z hz => mem_iUnion.mpr ⟨⟨z, hz⟩, hxV ⟨z, hz⟩⟩)
  refine ⟨G, hGc, ?_⟩
  exact ae_restrict_of_ae_restrict_of_subset hcover
    ((ae_eq_restrict_biUnion_iff V hs G f).mpr fun x _ => hGf x)

end GapFamily.Analytic
