import GapFamily.Contract
import Mathlib.Basic.Finite.Sigma

/-!
# Equivalence with the paper's counting and thermal conventions

The spectrum uses distinct weight pairs with natural multiplicities. The
paper counts primary occurrences, including repetitions. Finiteness of
these two descriptions is equivalent when supported multiplicities are
positive. The positive thermal parameter may equally be `t` or `2 * π * y`.
-/

noncomputable section

namespace GapFamily

/-- Primary occurrences below a dimension bound, counting multiplicity. -/
def Spectrum.PrimaryBelow (s : Spectrum) (D : ℝ) :=
  (p : {p : ℝ × ℝ // p ∈ s.support ∧ dimension p ≤ D}) × Fin (s.multiplicity p)

theorem finite_primaryBelow_of_locally_finite {s : Spectrum} {D : ℝ}
    (h : {p ∈ s.support | dimension p ≤ D}.Finite) : Finite (s.PrimaryBelow D) := by
  let : Finite {p : ℝ × ℝ // p ∈ s.support ∧ dimension p ≤ D} := h.to_subtype
  unfold Spectrum.PrimaryBelow
  infer_instance

theorem locally_finite_of_finite_primaryBelow {s : Spectrum} {D : ℝ}
    (hm : ∀ p ∈ s.support, 0 < s.multiplicity p)
    (h : Finite (s.PrimaryBelow D)) : {p ∈ s.support | dimension p ≤ D}.Finite := by
  let : Finite ((p : {p : ℝ × ℝ // p ∈ s.support ∧ dimension p ≤ D}) ×
    Fin (s.multiplicity p)) := h
  have hs : Function.Surjective
      (Sigma.fst : s.PrimaryBelow D → {p : ℝ × ℝ // p ∈ s.support ∧ dimension p ≤ D}) := by
    intro p
    exact ⟨⟨p, ⟨0, hm p p.property.1⟩⟩, rfl⟩
  have : Finite {p ∈ s.support | dimension p ≤ D} := Finite.of_surjective _ hs
  exact Set.toFinite _

theorem finite_primaryBelow_iff {s : Spectrum} {D : ℝ}
    (hm : ∀ p ∈ s.support, 0 < s.multiplicity p) :
    Finite (s.PrimaryBelow D) ↔ {p ∈ s.support | dimension p ≤ D}.Finite :=
  ⟨locally_finite_of_finite_primaryBelow hm, finite_primaryBelow_of_locally_finite⟩

/-- The exact thermal convergence convention in Definition 2.1. -/
theorem thermal_summable_iff (s : Spectrum) :
    (∀ y : ℝ, 0 < y → Summable (fun p : s.support =>
      (s.multiplicity p : ℝ) * Real.exp (-2 * Real.pi * y * dimension p))) ↔
    (∀ t : ℝ, 0 < t → Summable (fun p : s.support =>
      (s.multiplicity p : ℝ) * Real.exp (-t * dimension p))) := by
  constructor
  · intro h t ht
    have hy : 0 < t / (2 * Real.pi) := div_pos ht (by positivity)
    convert h (t / (2 * Real.pi)) hy using 1
    funext p
    congr 2
    field_simp
  · intro h y hy
    convert h (2 * Real.pi * y) (by positivity) using 1
    funext p
    congr 2
    ring

theorem TorusAdmissible.finite_primaryBelow {c : ℝ} {s : Spectrum}
    (h : TorusAdmissible c s) (D : ℝ) : Finite (s.PrimaryBelow D) :=
  finite_primaryBelow_of_locally_finite (h.locally_finite D)

theorem TorusAdmissible.thermal_summable_exp {c : ℝ} {s : Spectrum}
    (h : TorusAdmissible c s) (t : ℝ) (ht : 0 < t) :
    Summable (fun p : s.support =>
      (s.multiplicity p : ℝ) * Real.exp (-t * dimension p)) :=
  (thermal_summable_iff s).mp h.thermal_summable t ht

end GapFamily
