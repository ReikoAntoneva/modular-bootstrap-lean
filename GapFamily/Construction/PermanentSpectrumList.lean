import GapFamily.Construction.PermanentSpectrumData
import GapFamily.Construction.PermanentSpectrumSum
import Mathlib.Algebra.BigOperators.Fin

/-! Literal finite list sums agree with the unit-node indexing of the
permanent spectrum, retaining every repeated list entry. -/

noncomputable section
namespace GapFamily.Construction

/-- Indexing a finite list by `Fin length` preserves the sum with repetition. -/
theorem sum_fin_get_eq_list_sum {α A : Type*} [AddCommMonoid A]
    (l : List α) (f : α → A) :
    (∑ i : Fin l.length, f (l.get i)) = (l.map f).sum := by
  simpa only [List.get_eq_getElem] using Fin.sum_univ_fun_getElem l f

namespace PermanentSpectrumData

variable {b : ℝ} (hb : 0 ≤ b)
    (initial : List (ℝ × ℤ)) (layer : ℕ → List (ℝ × ℤ))
    (hinitial : ∀ p ∈ initial, b ≤ p.1 ∧ |(p.2 : ℝ)| ≤ p.1)
    (hlayer : ∀ (m : ℕ) p, p ∈ layer m → b ≤ p.1 ∧ |(p.2 : ℝ)| ≤ p.1 ∧
      (m : ℝ) ≤ p.1 ∧ p.1 < (m : ℝ) + 2)

/-- The permanent-layer thermal mass is exactly the original list thermal sum. -/
theorem ofLists_layerThermal (t : ℝ) (m : ℕ) :
    (ofLists hb initial layer hinitial hlayer).layerThermal t m =
      ((layer m).map (fun p => Real.exp (-t * p.1))).sum :=
  sum_fin_get_eq_list_sum (layer m) (fun p => Real.exp (-t * p.1))

/-- A summable list thermal bound transfers directly to the full literal
unit-node family, including the marker and the finite initial list. -/
theorem ofLists_thermal_summable (t : ℝ)
    (hsum : Summable (fun m => ((layer m).map (fun p => Real.exp (-t * p.1))).sum)) :
    Summable (fun i : (ofLists hb initial layer hinitial hlayer).Node =>
      Real.exp (-t * (ofLists hb initial layer hinitial hlayer).energy i)) := by
  apply (ofLists hb initial layer hinitial hlayer).thermal_summable t
  change Summable (fun m => (ofLists hb initial layer hinitial hlayer).layerThermal t m)
  simpa only [ofLists_layerThermal] using hsum

/-- The literal finite prefix for any node term equals the marker term,
the initial list sum, and the first complete layer list sums. This applies
in particular to the actual threshold point-seed term. -/
theorem ofLists_permanentNodePrefix {A : Type*} [AddCommMonoid A]
    (F : ℝ × ℤ → A) (n : ℕ) :
    permanentNodePrefix
      (fun i : (ofLists hb initial layer hinitial hlayer).Node =>
        F ((ofLists hb initial layer hinitial hlayer).energy i,
          (ofLists hb initial layer hinitial hlayer).spin i)) n =
      F (b, 0) + (initial.map F).sum +
        ∑ m ∈ Finset.range n, ((layer m).map F).sum := by
  change F (b, 0) + (∑ i : Fin initial.length, F (initial.get i)) +
    (∑ m ∈ Finset.range n, ∑ i : Fin (layer m).length, F ((layer m).get i)) = _
  simp only [sum_fin_get_eq_list_sum]

end PermanentSpectrumData
end GapFamily.Construction
