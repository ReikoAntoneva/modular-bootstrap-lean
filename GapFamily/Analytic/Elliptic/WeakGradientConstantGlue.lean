import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Gluing local almost-everywhere constants

On a connected set covered by open neighborhoods, an almost-everywhere constant
on each neighborhood is one almost-everywhere constant on the whole set. The
measure need only be positive on nonempty open sets, and second countability
supplies a countable subcover. No differential regularity is assumed here.
-/

noncomputable section

namespace GapFamily.Analytic

open Set Filter MeasureTheory
open scoped Topology

private theorem const_eq_of_ae_eq_on_open_overlap
    {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X]
    {μ : Measure X} [μ.IsOpenPosMeasure] {f : X → Y}
    {V W : Set X} (hV : IsOpen V) (hW : IsOpen W)
    (hne : (V ∩ W).Nonempty) {c d : Y}
    (hc : f =ᵐ[μ.restrict V] fun _ => c)
    (hd : f =ᵐ[μ.restrict W] fun _ => d) : c = d := by
  let : (ae (μ.restrict (V ∩ W))).NeBot :=
    ae_restrict_neBot.mpr ((hV.inter hW).measure_ne_zero μ hne)
  have hc' : f =ᵐ[μ.restrict (V ∩ W)] fun _ => c :=
    ae_restrict_of_ae_restrict_of_subset inter_subset_left hc
  have hd' : f =ᵐ[μ.restrict (V ∩ W)] fun _ => d :=
    ae_restrict_of_ae_restrict_of_subset inter_subset_right hd
  exact eventually_const.mp (hc'.symm.trans hd')

/-- Local almost-everywhere constancy on open neighborhoods determines a single
almost-everywhere constant throughout a connected set. -/
theorem exists_ae_eq_const_of_locally_ae_eq_const
    {X Y : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] {μ : Measure X} [μ.IsOpenPosMeasure]
    {U : Set X} (hU : IsConnected U) {f : X → Y}
    (hloc : ∀ x ∈ U, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      ∃ c : Y, f =ᵐ[μ.restrict V] fun _ => c) :
    ∃ c : Y, f =ᵐ[μ.restrict U] fun _ => c := by
  classical
  choose V hVo hxV hVU c hc using fun x : U => hloc x x.property
  have hlc : IsLocallyConstant c := by
    refine (IsLocallyConstant.iff_exists_open c).mpr fun x => ?_
    refine ⟨Subtype.val ⁻¹' V x, (hVo x).preimage continuous_subtype_val, hxV x, ?_⟩
    intro y hy
    exact const_eq_of_ae_eq_on_open_overlap (hVo y) (hVo x)
      ⟨y, hxV y, hy⟩ (hc y) (hc x)
  let : PreconnectedSpace U :=
    isPreconnected_iff_preconnectedSpace.mp hU.isPreconnected
  obtain ⟨x₀, hx₀⟩ := hU.nonempty
  let u₀ : U := ⟨x₀, hx₀⟩
  have hc₀ (x : U) : c x = c u₀ := hlc.apply_eq_of_preconnectedSpace x u₀
  obtain ⟨T, hT, hcover⟩ :=
    (HereditarilyLindelofSpace.isLindelof U).elim_countable_subcover V hVo
      (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩)
  refine ⟨c u₀, ae_restrict_of_ae_restrict_of_subset hcover ?_⟩
  apply (ae_eq_restrict_biUnion_iff V hT f (fun _ => c u₀)).mpr
  intro x hx
  simpa only [hc₀ x] using hc x

/-- A ball-based version for complex-valued functions on planar domains. -/
theorem exists_ae_eq_const_of_locally_ae_eq_const_ball
    {U : Set ℂ} (hU : IsConnected U) {f : ℂ → ℂ}
    (hloc : ∀ x ∈ U, ∃ r > 0, Metric.ball x r ⊆ U ∧
      ∃ c : ℂ, f =ᵐ[volume.restrict (Metric.ball x r)] fun _ => c) :
    ∃ c : ℂ, f =ᵐ[volume.restrict U] fun _ => c := by
  apply exists_ae_eq_const_of_locally_ae_eq_const hU
  intro x hx
  obtain ⟨r, hr, hrU, c, hc⟩ := hloc x hx
  exact ⟨Metric.ball x r, Metric.isOpen_ball, Metric.mem_ball_self hr, hrU, c, hc⟩

end GapFamily.Analytic
