import BTZEntropy.Construction.FixedFamilyData

/-!
# Common bounds for actual fixed-cutoff cells

The bounds are independent of the marker and the selector. Their predicate
constrains the stored initial cells and every valid call of the stored tail
selector. Exact moment and mass identities refer to those same cells.
-/

noncomputable section

open Set MeasureTheory Real
open scoped BigOperators

namespace BTZEntropy.Construction

open GapFamily GapFamily.Construction GapFamily.Analytic

/-- Quantitative bounds fixed before selecting the marker or cell nodes.
Counts and variations have real upper bounds; degrees have natural lower
bounds. The tail bounds may depend on the actual cell's left endpoint. -/
structure FixedFamilyBounds where
  initialCount : ℝ → ℤ → ℝ
  initialVariation : ℝ → ℤ → ℝ
  tailCount : ℝ → ℕ → ℤ → ℝ → ℝ
  tailVariation : ℝ → ℕ → ℤ → ℝ → ℝ
  initialDegree : ℝ → ℕ
  tailDegree : ℝ → ℕ → ℕ

namespace FixedFamilyDatum

variable {B : ℝ} {g : FixedFamilyGeometry B} {a : ℝ} {δ : ℝ}
  (d : FixedFamilyDatum g a δ)

/-- A common bound applies to the actual cells, including the tail selector
at every valid state, layer and spin. No asymptotic entropy property is part
of this local construction condition. -/
structure HasBounds (bounds : FixedFamilyBounds) : Prop where
  initial_count : ∀ J : realInitialRows g.radius,
    ((d.initialCell J).count : ℝ) ≤ bounds.initialCount a J
  initial_variation : ∀ J : realInitialRows g.radius,
    (d.initialCell J).residual.variation.real univ ≤ bounds.initialVariation a J
  initial_degree : bounds.initialDegree a ≤ d.initialDegree
  tail_count : ∀ (state : FiniteRepairState) (m : ℕ) (J : ℤ)
    (h : RealTailStepValid (shift (gapFamilyCharge a)) g.start state m J),
    ((d.tail.cell state m J h).count : ℝ) ≤ bounds.tailCount a m J (state.front J)
  tail_variation : ∀ (state : FiniteRepairState) (m : ℕ) (J : ℤ)
    (h : RealTailStepValid (shift (gapFamilyCharge a)) g.start state m J),
    (d.tail.cell state m J h).residual.variation.real univ ≤
      bounds.tailVariation a m J (state.front J)
  tail_degree : ∀ m : ℕ, bounds.tailDegree a m ≤ d.tailDegree m

/-- The initial unit-node count is exactly the signed continuum mass. -/
theorem initialCell_mass_eq (J : realInitialRows g.radius) :
    (∫ E in Ioo (max g.clearing |(J : ℝ)|) (d.initialCell J).right,
      d.density J E ∂referenceMeasure J) = ((d.initialCell J).count : ℝ) :=
  (d.initialCell J).mass_eq

/-- Polynomial moments in the actual square-root coordinate match the
ordinary signed continuum integral exactly. -/
theorem initialCell_coordinate_moment (J : realInitialRows g.radius)
    (p : Polynomial ℝ) (hp : p.natDegree ≤ d.initialDegree) :
    (∑ i, p.eval (rootCoord |(J : ℝ)| ((d.initialCell J).node i))) =
      ∫ E in Ioo (max g.clearing |(J : ℝ)|) (d.initialCell J).right,
        d.density J E * p.eval (rootCoord |(J : ℝ)| E) ∂referenceMeasure J := by
  have heq := (cellResidualMeasure_integral_coordinatePolynomial J
    (max g.clearing |(J : ℝ)|) (d.initialCell J).right
    (d.initialCell J).node (d.initialCell J).density_integrable p).2.2
  rw [((d.initialCell J).moment p hp).2] at heq
  exact (sub_eq_zero.mp heq.symm)

theorem initialCell_count_le_abs_mass (J : realInitialRows g.radius) :
    ((d.initialCell J).count : ℝ) ≤
      ∫ E in Ioo (max g.clearing |(J : ℝ)|) (d.initialCell J).right,
        |d.density J E| ∂referenceMeasure J :=
  (d.initialCell J).count_le_abs_mass

theorem initialCell_variation_le_twice_abs_mass (J : realInitialRows g.radius) :
    (d.initialCell J).residual.variation.real univ ≤
      2 * ∫ E in Ioo (max g.clearing |(J : ℝ)|) (d.initialCell J).right,
        |d.density J E| ∂referenceMeasure J :=
  (d.initialCell J).variation_le_twice_abs_mass

/-- The finite initial list retains one occurrence for each selected node. -/
theorem initial_nodes_length :
    d.initialState.nodes.length = ∑ J, (d.initialCell J).count := by
  classical
  simp only [FixedFamilyDatum.initialState, realInitialRepairState_nodes,
    realInitialRepairNodes, List.length_flatMap, List.length_ofFn,
    Finset.sum_map_toList, Finset.attach_eq_univ]

/-- The tail cell's count is the mass of the actual current signed density. -/
theorem tailCell_mass_eq (state : FiniteRepairState) (m : ℕ) (J : ℤ)
    (h : RealTailStepValid (shift (gapFamilyCharge a)) g.start state m J) :
    (∫ E in Ioo (state.front J) (d.tail.cell state m J h).right,
      state.numerator J E ∂referenceMeasure J) =
        ((d.tail.cell state m J h).count : ℝ) :=
  (d.tail.cell state m J h).mass_eq

theorem tailCell_coordinate_moment (state : FiniteRepairState) (m : ℕ) (J : ℤ)
    (h : RealTailStepValid (shift (gapFamilyCharge a)) g.start state m J)
    (p : Polynomial ℝ) (hp : p.natDegree ≤ d.tailDegree m) :
    (∑ i, p.eval (rootCoord |(J : ℝ)| ((d.tail.cell state m J h).node i))) =
      ∫ E in Ioo (state.front J) (d.tail.cell state m J h).right,
        state.numerator J E * p.eval (rootCoord |(J : ℝ)| E) ∂referenceMeasure J := by
  have heq := (cellResidualMeasure_integral_coordinatePolynomial J
    (state.front J) (d.tail.cell state m J h).right
    (d.tail.cell state m J h).node (d.tail.cell state m J h).density_integrable p).2.2
  rw [((d.tail.cell state m J h).moment p hp).2] at heq
  exact (sub_eq_zero.mp heq.symm)

/-- Every valid local call automatically has the existing exponential
unit-node budget, without an additional assumption on node selection. -/
theorem tailCell_count_le (state : FiniteRepairState) (m : ℕ) (J : ℤ)
    (h : RealTailStepValid (shift (gapFamilyCharge a)) g.start state m J) :
    ((d.tail.cell state m J h).count : ℝ) ≤
      6 * exp (4 * π * (shift (gapFamilyCharge a) + state.front J)) := by
  apply (d.tail.cell state m J h).count_le d.charge_large ?_ h.physical h.envelope
  exact (show (1 : ℝ) ≤ m by exact_mod_cast g.start_pos.trans h.layer).trans h.front_lower

theorem tailCell_variation_le (state : FiniteRepairState) (m : ℕ) (J : ℤ)
    (h : RealTailStepValid (shift (gapFamilyCharge a)) g.start state m J) :
    (d.tail.cell state m J h).residual.variation.real univ ≤
      12 * exp (4 * π * (shift (gapFamilyCharge a) + state.front J)) := by
  apply (d.tail.cell state m J h).variation_le d.charge_large ?_ h.physical h.envelope
  exact (show (1 : ℝ) ≤ m by exact_mod_cast g.start_pos.trans h.layer).trans h.front_lower

/-- The list emitted by a valid step contains precisely these selected
unit-node occurrences, including repetitions. -/
theorem tail_nodeList_eq (state : FiniteRepairState) (m : ℕ) (J : ℤ)
    (h : RealTailStepValid (shift (gapFamilyCharge a)) g.start state m J) :
    d.tail.nodeList m J state =
      List.ofFn (fun i => ((d.tail.cell state m J h).node i, J)) := by
  simp only [RealTailLocalData.nodeList, dite_eq_left h]

theorem tail_nodeList_length (state : FiniteRepairState) (m : ℕ) (J : ℤ)
    (h : RealTailStepValid (shift (gapFamilyCharge a)) g.start state m J) :
    (d.tail.nodeList m J state).length = (d.tail.cell state m J h).count := by
  rw [d.tail_nodeList_eq state m J h, List.length_ofFn]

/-- The stored recurrence appends the same list to its previous state. -/
theorem tail_step_nodes (state : FiniteRepairState) (m : ℕ) (J : ℤ)
    (h : RealTailStepValid (shift (gapFamilyCharge a)) g.start state m J) :
    (d.tail.step m J state).nodes = state.nodes ++
      List.ofFn (fun i => ((d.tail.cell state m J h).node i, J)) := by
  rw [d.tail.step_nodes, d.tail_nodeList_eq state m J h]

namespace HasBounds

variable {d} {bounds : FixedFamilyBounds} (hbound : d.HasBounds bounds)

include hbound

/-- The common initial count budget controls the literal initial list. -/
theorem initial_nodes_length_le :
    (d.initialState.nodes.length : ℝ) ≤ ∑ J : realInitialRows g.radius,
      bounds.initialCount a J := by
  rw [d.initial_nodes_length, Nat.cast_sum]
  exact Finset.sum_le_sum (fun J _ => hbound.initial_count J)

/-- Every initial selector in the class supplies the same minimum degree
of exact coordinate moments. -/
theorem initialCell_coordinate_moment (J : realInitialRows g.radius)
    (p : Polynomial ℝ) (hp : p.natDegree ≤ bounds.initialDegree a) :
    (∑ i, p.eval (rootCoord |(J : ℝ)| ((d.initialCell J).node i))) =
      ∫ E in Ioo (max g.clearing |(J : ℝ)|) (d.initialCell J).right,
        d.density J E * p.eval (rootCoord |(J : ℝ)| E) ∂referenceMeasure J :=
  d.initialCell_coordinate_moment J p (hp.trans hbound.initial_degree)

theorem tailCell_coordinate_moment (state : FiniteRepairState) (m : ℕ) (J : ℤ)
    (h : RealTailStepValid (shift (gapFamilyCharge a)) g.start state m J)
    (p : Polynomial ℝ) (hp : p.natDegree ≤ bounds.tailDegree a m) :
    (∑ i, p.eval (rootCoord |(J : ℝ)| ((d.tail.cell state m J h).node i))) =
      ∫ E in Ioo (state.front J) (d.tail.cell state m J h).right,
        state.numerator J E * p.eval (rootCoord |(J : ℝ)| E) ∂referenceMeasure J :=
  d.tailCell_coordinate_moment state m J h p (hp.trans (hbound.tail_degree m))

theorem tail_nodeList_length_le (state : FiniteRepairState) (m : ℕ) (J : ℤ)
    (h : RealTailStepValid (shift (gapFamilyCharge a)) g.start state m J) :
    ((d.tail.nodeList m J state).length : ℝ) ≤ bounds.tailCount a m J (state.front J) := by
  rw [d.tail_nodeList_length state m J h]
  exact hbound.tail_count state m J h

end HasBounds

end FixedFamilyDatum

end BTZEntropy.Construction
