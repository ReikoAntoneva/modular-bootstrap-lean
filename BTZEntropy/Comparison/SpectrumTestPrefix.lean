import GapFamily.Construction.RealPermanentSpectrumData

/-! Compact energy tests of the actual permanent spectrum stabilize exactly.
Every repeated node remains an individual occurrence in the finite prefix. -/

noncomputable section
open Set Filter
open GapFamily GapFamily.Construction

namespace BTZEntropy.Comparison

/-- An upper energy support bound makes the actual unit-node test finitely
supported; no thermal or modular assertion is used. -/
theorem permanentNodeTest_hasFiniteSupport {b : ℝ} (D : PermanentSpectrumData b)
    (f : ℝ × ℤ → ℝ) (B : ℝ) (hf : ∀ p, B ≤ p.1 → f p = 0) :
    Function.HasFiniteSupport (fun i : D.Node => f (D.energy i, D.spin i)) := by
  apply (D.energy_sublevel_finite B).subset
  intro i hi
  change f (D.energy i, D.spin i) ≠ 0 at hi
  change D.energy i ≤ B
  by_contra h
  exact hi (hf _ (le_of_lt (lt_of_not_ge h)))

theorem permanentNodeTest_summable {b : ℝ} (D : PermanentSpectrumData b)
    (f : ℝ × ℤ → ℝ) (B : ℝ) (hf : ∀ p, B ≤ p.1 → f p = 0) :
    Summable (fun i : D.Node => f (D.energy i, D.spin i)) :=
  summable_of_hasFiniteSupport (permanentNodeTest_hasFiniteSupport D f B hf)

/-- A window below layer `N` has already stabilized after that layer prefix.
This is an equality for the same permanent unit-node family. -/
theorem permanentNodeTest_eq_prefix {b : ℝ} (D : PermanentSpectrumData b)
    (f : ℝ × ℤ → ℝ) (B : ℝ) (hf : ∀ p, B ≤ p.1 → f p = 0)
    (N : ℕ) (hBN : B ≤ (N : ℝ)) :
    (∑' i : D.Node, f (D.energy i, D.spin i)) =
      ((D.permanentAtomList N).map f).sum := by
  rw [D.sum_map_permanentAtomList,
    tsum_permanentNode_eq _ (permanentNodeTest_summable D f B hf)]
  unfold permanentNodePrefix
  congr 1
  apply tsum_eq_sum
  intro m hm
  apply Finset.sum_eq_zero
  intro i _
  apply hf
  exact hBN.trans ((by exact_mod_cast (Nat.le_of_not_gt
    (by simpa only [Finset.mem_range] using hm)) : (N : ℝ) ≤ m).trans (D.layer_escape m i))

/-- All later permanent prefixes give the identical compact test. -/
theorem permanentNodeTest_eventually_eq_prefix {b : ℝ} (D : PermanentSpectrumData b)
    (f : ℝ × ℤ → ℝ) (B : ℝ) (hf : ∀ p, B ≤ p.1 → f p = 0) :
    ∀ᶠ N : ℕ in atTop,
      (∑' i : D.Node, f (D.energy i, D.spin i)) =
        ((D.permanentAtomList N).map f).sum := by
  filter_upwards [eventually_ge_atTop ⌈B⌉₊] with N hN
  exact permanentNodeTest_eq_prefix D f B hf N
    ((Nat.le_ceil B).trans (by exact_mod_cast hN))

variable {a U : ℝ} {T : ℕ} {degree : ℕ → ℕ}
  (d : RealTailLocalData a U T degree) (initial : FiniteRepairState)

/-- The finite state separates into its original packet and the same emitted
layer lists used by the actual permanent spectrum. -/
theorem stateNodeTest_eq_initial_add_layer (f : ℝ × ℤ → ℝ) (k : ℕ) :
    (((d.state initial k).nodes).map f).sum = (initial.nodes.map f).sum +
      ∑ m ∈ Finset.range k,
        ((scheduledLayerBlock T FiniteRepairState.front d.step d.nodeList initial m).map f).sum := by
  induction k with
  | zero => simp [RealTailLocalData.state]
  | succ k ih =>
      rw [d.state_nodes initial, scheduledNodePrefix_succ,
        List.map_append, List.sum_append, ← d.state_nodes initial, ih,
        Finset.sum_range_succ, add_assoc]

/-- In a compact window, the permanent spectrum is exactly its marker plus
the literal finite repair state; the marker is not included a second time. -/
theorem realPermanentNodeTest_eq_state
    (b : ℝ) (hb : 0 ≤ b) (hbT : b ≤ (T : ℝ))
    (hinitial : ∀ p ∈ initial.nodes, b ≤ p.1 ∧ |(p.2 : ℝ)| ≤ p.1)
    (f : ℝ × ℤ → ℝ) (B : ℝ) (hf : ∀ p, B ≤ p.1 → f p = 0)
    (k : ℕ) (hBk : B ≤ ((T + k : ℕ) : ℝ)) :
    (∑' i : (d.permanentSpectrumData b hb hbT initial hinitial).Node,
      f ((d.permanentSpectrumData b hb hbT initial hinitial).energy i,
        (d.permanentSpectrumData b hb hbT initial hinitial).spin i)) =
      f (b, 0) + (((d.state initial k).nodes).map f).sum := by
  rw [permanentNodeTest_eq_prefix _ f B hf (T + k) hBk,
    d.permanentSpectrumData_permanentAtomList, List.map_cons, List.sum_cons]

/-- The same stabilized test explicitly retains the marker, initial packet,
and every actual finite tail layer. -/
theorem realPermanentNodeTest_eq_initial_add_layer
    (b : ℝ) (hb : 0 ≤ b) (hbT : b ≤ (T : ℝ))
    (hinitial : ∀ p ∈ initial.nodes, b ≤ p.1 ∧ |(p.2 : ℝ)| ≤ p.1)
    (f : ℝ × ℤ → ℝ) (B : ℝ) (hf : ∀ p, B ≤ p.1 → f p = 0)
    (k : ℕ) (hBk : B ≤ ((T + k : ℕ) : ℝ)) :
    (∑' i : (d.permanentSpectrumData b hb hbT initial hinitial).Node,
      f ((d.permanentSpectrumData b hb hbT initial hinitial).energy i,
        (d.permanentSpectrumData b hb hbT initial hinitial).spin i)) =
      f (b, 0) + (initial.nodes.map f).sum +
        ∑ m ∈ Finset.range k,
          ((scheduledLayerBlock T FiniteRepairState.front d.step d.nodeList initial m).map f).sum := by
  rw [realPermanentNodeTest_eq_state d initial b hb hbT hinitial f B hf k hBk,
    stateNodeTest_eq_initial_add_layer, add_assoc]

end BTZEntropy.Comparison
