import GapFamily.Analytic.Modular.ModularVolume
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import Mathlib.Topology.Connected.Clopen

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open Filter MeasureTheory Set
open scoped Topology

/-- A locally constant predicate with one witness holds throughout a preconnected space. -/
theorem forall_of_eventually_iff_of_exists {X : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] (P : X → Prop)
    (hloc : ∀ x, ∀ᶠ y in 𝓝 x, P y ↔ P x) (hex : ∃ x, P x) : ∀ x, P x := by
  have hopen : IsOpen {x | P x} := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    exact (hloc x).mono (fun _ h => h.mpr hx)
  have hcompl : IsOpen {x | ¬ P x} := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    exact (hloc x).mono (fun _ h => fun hy => hx (h.mp hy))
  have hclopen : IsClopen {x | P x} := ⟨isOpen_compl_iff.mp hcompl, hopen⟩
  have heq : {x | P x} = univ := hclopen.eq_univ hex
  intro x
  change x ∈ {x | P x}
  rw [heq]
  exact mem_univ x

/-- The actual modular measure has positive mass, so an almost-everywhere predicate has a witness. -/
theorem exists_of_ae_modularMeasure {P : UpperHalfPlane → Prop}
    (h : ∀ᵐ z ∂modularMeasure, P z) : ∃ z, P z := by
  have hμ : modularMeasure ≠ 0 := by
    intro heq
    have hpos := modularMeasure_univ_pos
    simp [heq] at hpos
  have : NeBot (ae modularMeasure) := ae_neBot.mpr hμ
  exact h.exists

/-- Local constancy promotes an actual modular almost-everywhere statement to every point. -/
theorem forall_of_eventually_iff_of_ae_modularMeasure (P : UpperHalfPlane → Prop)
    (hloc : ∀ z, ∀ᶠ w in 𝓝 z, P w ↔ P z)
    (hae : ∀ᵐ z ∂modularMeasure, P z) : ∀ z, P z :=
  forall_of_eventually_iff_of_exists P hloc (exists_of_ae_modularMeasure hae)

end GapFamily.Analytic.SpatialPoint
