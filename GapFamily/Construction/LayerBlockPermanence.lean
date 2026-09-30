import Mathlib.Data.List.Infix
import Mathlib.Data.List.Range
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Permanence of finite atom blocks below a cutoff

Atoms are literal ordered lists of energy-spin pairs. Filtering to energies
at most a fixed cutoff commutes with appending later high-energy blocks.
The resulting list equality preserves both order and every multiplicity;
in particular it preserves any mapped additive contribution.
-/

noncomputable section
namespace GapFamily.Construction

/-- The exact ordered atom list at energies at most `D`, with repetitions retained. -/
def atomSublevel (D : ℝ) (atoms : List (ℝ × ℤ)) : List (ℝ × ℤ) :=
  atoms.filter (fun p => decide (p.1 ≤ D))

@[simp] theorem mem_atomSublevel {D : ℝ} {atoms : List (ℝ × ℤ)} {p : ℝ × ℤ} :
    p ∈ atomSublevel D atoms ↔ p ∈ atoms ∧ p.1 ≤ D := by
  simp [atomSublevel]

@[simp] theorem atomSublevel_nil (D : ℝ) : atomSublevel D [] = [] := rfl

@[simp] theorem atomSublevel_append (D : ℝ) (old new : List (ℝ × ℤ)) :
    atomSublevel D (old ++ new) = atomSublevel D old ++ atomSublevel D new :=
  List.filter_append old new

/-- A block strictly above the cutoff has no contribution to the sublevel list. -/
theorem atomSublevel_eq_nil_of_above {D : ℝ} {atoms : List (ℝ × ℤ)}
    (h : ∀ p ∈ atoms, D < p.1) : atomSublevel D atoms = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro p hp
  simpa using not_le.mpr (h p hp)

/-- A list already below the cutoff is preserved literally by the filter. -/
theorem atomSublevel_eq_self_of_le {D : ℝ} {atoms : List (ℝ × ℤ)}
    (h : ∀ p ∈ atoms, p.1 ≤ D) : atomSublevel D atoms = atoms := by
  apply List.filter_eq_self.mpr
  intro p hp
  simpa using h p hp

/-- Appending a high-energy block preserves the full ordered sublevel list. -/
theorem atomSublevel_append_eq_of_above (D : ℝ) (old : List (ℝ × ℤ))
    {new : List (ℝ × ℤ)} (hnew : ∀ p ∈ new, D < p.1) :
    atomSublevel D (old ++ new) = atomSublevel D old := by
  rw [atomSublevel_append, atomSublevel_eq_nil_of_above hnew, List.append_nil]

/-- The layer lower bound is enough for permanence below every earlier cutoff. -/
theorem atomSublevel_append_eq_of_lower_bound {D m : ℝ}
    (old : List (ℝ × ℤ)) {new : List (ℝ × ℤ)} (hDm : D < m)
    (hnew : ∀ p ∈ new, m ≤ p.1) :
    atomSublevel D (old ++ new) = atomSublevel D old :=
  atomSublevel_append_eq_of_above D old (fun p hp => hDm.trans_le (hnew p hp))

/-- Existing atoms remain an exact ordered prefix after any appended block. -/
theorem atomList_isPrefix_append (old new : List (ℝ × ℤ)) : old <+: old ++ new :=
  List.prefix_append old new

/-- In particular, every old occurrence survives as part of the new list. -/
theorem atomList_sublist_append (old new : List (ℝ × ℤ)) : old.Sublist (old ++ new) :=
  (atomList_isPrefix_append old new).sublist

/-- Exact multiplicity of each sublevel atom is unchanged. -/
theorem count_atomSublevel_append_of_above (D : ℝ) (old : List (ℝ × ℤ))
    {new : List (ℝ × ℤ)} (hnew : ∀ p ∈ new, D < p.1) (p : ℝ × ℤ) :
    (atomSublevel D (old ++ new)).count p = (atomSublevel D old).count p := by
  rw [atomSublevel_append_eq_of_above D old hnew]

/-- Any additive observable of the exact sublevel list remains unchanged. -/
theorem sum_map_atomSublevel_append_of_above {A : Type*} [AddCommMonoid A]
    (D : ℝ) (old : List (ℝ × ℤ)) {new : List (ℝ × ℤ)}
    (hnew : ∀ p ∈ new, D < p.1) (f : ℝ × ℤ → A) :
    ((atomSublevel D (old ++ new)).map f).sum = ((atomSublevel D old).map f).sum := by
  rw [atomSublevel_append_eq_of_above D old hnew]

/-- Append a finite sequence of literal blocks, preserving block and node order. -/
def appendAtomBlocks (old : List (ℝ × ℤ)) (blocks : List (List (ℝ × ℤ))) : List (ℝ × ℤ) :=
  old ++ blocks.flatten

@[simp] theorem appendAtomBlocks_nil (old : List (ℝ × ℤ)) : appendAtomBlocks old [] = old := by
  simp [appendAtomBlocks]

@[simp] theorem appendAtomBlocks_cons (old block : List (ℝ × ℤ))
    (blocks : List (List (ℝ × ℤ))) :
    appendAtomBlocks old (block :: blocks) = appendAtomBlocks (old ++ block) blocks := by
  simp [appendAtomBlocks, List.append_assoc]

/-- The finite-block definition is the literal succession of append operations. -/
theorem appendAtomBlocks_eq_foldl (old : List (ℝ × ℤ)) (blocks : List (List (ℝ × ℤ))) :
    appendAtomBlocks old blocks = blocks.foldl List.append old := by
  induction blocks generalizing old with
  | nil => simp
  | cons block blocks ih => simpa using ih (old ++ block)

theorem atomList_isPrefix_appendAtomBlocks (old : List (ℝ × ℤ))
    (blocks : List (List (ℝ × ℤ))) : old <+: appendAtomBlocks old blocks :=
  List.prefix_append old blocks.flatten

theorem atomList_sublist_appendAtomBlocks (old : List (ℝ × ℤ))
    (blocks : List (List (ℝ × ℤ))) : old.Sublist (appendAtomBlocks old blocks) :=
  (atomList_isPrefix_appendAtomBlocks old blocks).sublist

/-- Every finite succession of later blocks leaves the exact earlier sublevel unchanged. -/
theorem atomSublevel_appendAtomBlocks_of_above (D : ℝ) (old : List (ℝ × ℤ))
    {blocks : List (List (ℝ × ℤ))}
    (hblocks : ∀ block ∈ blocks, ∀ p ∈ block, D < p.1) :
    atomSublevel D (appendAtomBlocks old blocks) = atomSublevel D old := by
  apply atomSublevel_append_eq_of_above
  intro p hp
  rcases List.mem_flatten.mp hp with ⟨block, hb, hp⟩
  exact hblocks block hb p hp

/-- The full statement for a finite natural layer schedule: the lower energy
bound of each layer makes every cutoff preceding those layers permanent. -/
theorem atomSublevel_append_layers (D : ℝ) (old : List (ℝ × ℤ))
    (layers : List ℕ) (block : ℕ → List (ℝ × ℤ))
    (hlayers : ∀ n ∈ layers, D < (n : ℝ))
    (hlower : ∀ n ∈ layers, ∀ p ∈ block n, (n : ℝ) ≤ p.1) :
    atomSublevel D (appendAtomBlocks old (layers.map block)) = atomSublevel D old := by
  apply atomSublevel_appendAtomBlocks_of_above
  intro b hb p hp
  rcases List.mem_map.mp hb with ⟨n, hn, rfl⟩
  exact (hlayers n hn).trans_le (hlower n hn p hp)

/-- Arbitrary additive contributions below the cutoff are permanent under
any finite sequence of later blocks. -/
theorem sum_map_atomSublevel_appendAtomBlocks_of_above {A : Type*} [AddCommMonoid A]
    (D : ℝ) (old : List (ℝ × ℤ)) {blocks : List (List (ℝ × ℤ))}
    (hblocks : ∀ block ∈ blocks, ∀ p ∈ block, D < p.1) (f : ℝ × ℤ → A) :
    ((atomSublevel D (appendAtomBlocks old blocks)).map f).sum =
      ((atomSublevel D old).map f).sum := by
  rw [atomSublevel_appendAtomBlocks_of_above D old hblocks]

/-- In particular this applies to any finite prescribed schedule of later natural layers. -/
theorem sum_map_atomSublevel_append_layers {A : Type*} [AddCommMonoid A]
    (D : ℝ) (old : List (ℝ × ℤ)) (layers : List ℕ) (block : ℕ → List (ℝ × ℤ))
    (hlayers : ∀ n ∈ layers, D < (n : ℝ))
    (hlower : ∀ n ∈ layers, ∀ p ∈ block n, (n : ℝ) ≤ p.1) (f : ℝ × ℤ → A) :
    ((atomSublevel D (appendAtomBlocks old (layers.map block))).map f).sum =
      ((atomSublevel D old).map f).sum := by
  rw [atomSublevel_append_layers D old layers block hlayers hlower]

/-- The permanence statement also applies directly to a finite recursive
schedule implemented by `foldl`, rather than only its flattened representation. -/
theorem atomSublevel_foldl_layers (D : ℝ) (old : List (ℝ × ℤ))
    (layers : List ℕ) (block : ℕ → List (ℝ × ℤ))
    (hlayers : ∀ n ∈ layers, D < (n : ℝ))
    (hlower : ∀ n ∈ layers, ∀ p ∈ block n, (n : ℝ) ≤ p.1) :
    atomSublevel D (layers.foldl (fun atoms n => atoms ++ block n) old) = atomSublevel D old := by
  simpa only [appendAtomBlocks_eq_foldl, List.foldl_map, List.append_eq] using
    atomSublevel_append_layers D old layers block hlayers hlower

/-- Any finite run of consecutive later layers preserves the exact sublevel list.
Only the lower energy bound of the atoms in those actual layers is needed. -/
theorem atomSublevel_append_layerRange (D : ℝ) (old : List (ℝ × ℤ))
    (block : ℕ → List (ℝ × ℤ)) (start n : ℕ) (hD : D < (start : ℝ))
    (hlower : ∀ r ∈ List.range n, ∀ p ∈ block (start + r),
      ((start + r : ℕ) : ℝ) ≤ p.1) :
    atomSublevel D (appendAtomBlocks old ((List.range n).map (fun r => block (start + r)))) =
      atomSublevel D old := by
  apply atomSublevel_appendAtomBlocks_of_above
  intro b hb p hp
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hb
  have hstart : (start : ℝ) ≤ ((start + r : ℕ) : ℝ) :=
    Nat.cast_le.mpr (Nat.le_add_right start r)
  exact (hD.trans_le hstart).trans_le (hlower r hr p hp)

/-- Consecutive finite iteration preserves the sublevel before its first layer. -/
theorem atomSublevel_foldl_layerRange (D : ℝ) (old : List (ℝ × ℤ))
    (block : ℕ → List (ℝ × ℤ)) (start n : ℕ) (hD : D < (start : ℝ))
    (hlower : ∀ r ∈ List.range n, ∀ p ∈ block (start + r),
      ((start + r : ℕ) : ℝ) ≤ p.1) :
    atomSublevel D ((List.range n).foldl (fun atoms r => atoms ++ block (start + r)) old) =
      atomSublevel D old := by
  simpa only [appendAtomBlocks_eq_foldl, List.foldl_map, List.append_eq] using
    atomSublevel_append_layerRange D old block start n hD hlower

/-- Every additive contribution of the old sublevel is permanent through
a finite run of actual later layers. -/
theorem sum_map_atomSublevel_foldl_layerRange {A : Type*} [AddCommMonoid A]
    (D : ℝ) (old : List (ℝ × ℤ)) (block : ℕ → List (ℝ × ℤ)) (start n : ℕ)
    (hD : D < (start : ℝ))
    (hlower : ∀ r ∈ List.range n, ∀ p ∈ block (start + r),
      ((start + r : ℕ) : ℝ) ≤ p.1) (f : ℝ × ℤ → A) :
    ((atomSublevel D
      ((List.range n).foldl (fun atoms r => atoms ++ block (start + r)) old)).map f).sum =
      ((atomSublevel D old).map f).sum := by
  rw [atomSublevel_foldl_layerRange D old block start n hD hlower]

/-- The initial atom list followed by exactly the first `n` emitted blocks. -/
def atomBlockPrefix (initial : List (ℝ × ℤ)) (block : ℕ → List (ℝ × ℤ))
    (n : ℕ) : List (ℝ × ℤ) :=
  appendAtomBlocks initial ((List.range n).map block)

@[simp] theorem mem_atomBlockPrefix {initial : List (ℝ × ℤ)}
    {block : ℕ → List (ℝ × ℤ)} {n : ℕ} {p : ℝ × ℤ} :
    p ∈ atomBlockPrefix initial block n ↔ p ∈ initial ∨ ∃ r < n, p ∈ block r := by
  simp [atomBlockPrefix, appendAtomBlocks]

@[simp] theorem atomBlockPrefix_zero (initial : List (ℝ × ℤ))
    (block : ℕ → List (ℝ × ℤ)) : atomBlockPrefix initial block 0 = initial := by
  simp [atomBlockPrefix]

@[simp] theorem atomBlockPrefix_succ (initial : List (ℝ × ℤ))
    (block : ℕ → List (ℝ × ℤ)) (n : ℕ) :
    atomBlockPrefix initial block (n + 1) = atomBlockPrefix initial block n ++ block n := by
  simp [atomBlockPrefix, List.range_succ, appendAtomBlocks, List.flatten_append,
    List.append_assoc]

/-- A later finite prefix is exactly an earlier prefix followed by the intervening blocks. -/
theorem atomBlockPrefix_add (initial : List (ℝ × ℤ))
    (block : ℕ → List (ℝ × ℤ)) (n k : ℕ) :
    atomBlockPrefix initial block (n + k) =
      appendAtomBlocks (atomBlockPrefix initial block n)
        ((List.range k).map (fun r => block (n + r))) := by
  simp [atomBlockPrefix, List.range_add, appendAtomBlocks, List.map_append,
    List.map_map, List.flatten_append, List.append_assoc, Function.comp_def]

theorem initial_isPrefix_atomBlockPrefix (initial : List (ℝ × ℤ))
    (block : ℕ → List (ℝ × ℤ)) (n : ℕ) : initial <+: atomBlockPrefix initial block n :=
  atomList_isPrefix_appendAtomBlocks initial _

theorem initial_sublist_atomBlockPrefix (initial : List (ℝ × ℤ))
    (block : ℕ → List (ℝ × ℤ)) (n : ℕ) : initial.Sublist (atomBlockPrefix initial block n) :=
  (initial_isPrefix_atomBlockPrefix initial block n).sublist

/-- Every earlier stage survives as an exact ordered prefix at every later stage. -/
theorem atomBlockPrefix_isPrefix (initial : List (ℝ × ℤ))
    (block : ℕ → List (ℝ × ℤ)) {n k : ℕ} (hnk : n ≤ k) :
    atomBlockPrefix initial block n <+: atomBlockPrefix initial block k := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hnk
  rw [atomBlockPrefix_add]
  exact atomList_isPrefix_appendAtomBlocks _ _

theorem atomBlockPrefix_sublist (initial : List (ℝ × ℤ))
    (block : ℕ → List (ℝ × ℤ)) {n k : ℕ} (hnk : n ≤ k) :
    (atomBlockPrefix initial block n).Sublist (atomBlockPrefix initial block k) :=
  (atomBlockPrefix_isPrefix initial block hnk).sublist

/-- Once all remaining blocks lie above a cutoff, any finite extension
preserves its literal ordered sublevel list. -/
theorem atomSublevel_atomBlockPrefix_add_of_above (D : ℝ) (initial : List (ℝ × ℤ))
    (block : ℕ → List (ℝ × ℤ)) (n k : ℕ)
    (habove : ∀ r, n ≤ r → ∀ p ∈ block r, D < p.1) :
    atomSublevel D (atomBlockPrefix initial block (n + k)) =
      atomSublevel D (atomBlockPrefix initial block n) := by
  rw [atomBlockPrefix_add]
  apply atomSublevel_appendAtomBlocks_of_above
  intro b hb p hp
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hb
  exact habove (n + r) (Nat.le_add_right _ _) p hp

theorem atomSublevel_atomBlockPrefix_eq_of_above (D : ℝ) (initial : List (ℝ × ℤ))
    (block : ℕ → List (ℝ × ℤ)) {n k : ℕ} (hnk : n ≤ k)
    (habove : ∀ r, n ≤ r → ∀ p ∈ block r, D < p.1) :
    atomSublevel D (atomBlockPrefix initial block k) =
      atomSublevel D (atomBlockPrefix initial block n) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hnk
  exact atomSublevel_atomBlockPrefix_add_of_above D initial block n r habove

/-- Exact sublevel permanence also preserves every mapped additive contribution. -/
theorem sum_map_atomSublevel_atomBlockPrefix_eq_of_above {A : Type*} [AddCommMonoid A]
    (D : ℝ) (initial : List (ℝ × ℤ)) (block : ℕ → List (ℝ × ℤ)) {n k : ℕ}
    (hnk : n ≤ k) (habove : ∀ r, n ≤ r → ∀ p ∈ block r, D < p.1)
    (f : ℝ × ℤ → A) :
    ((atomSublevel D (atomBlockPrefix initial block k)).map f).sum =
      ((atomSublevel D (atomBlockPrefix initial block n)).map f).sum := by
  rw [atomSublevel_atomBlockPrefix_eq_of_above D initial block hnk habove]

/-- The physical lower bound of layer `T + r` makes every earlier cutoff permanent. -/
theorem atomSublevel_atomBlockPrefix_eq_of_layer_lower (D : ℝ)
    (initial : List (ℝ × ℤ)) (block : ℕ → List (ℝ × ℤ)) (T : ℕ) {n k : ℕ}
    (hnk : n ≤ k) (hD : D < ((T + n : ℕ) : ℝ))
    (hlower : ∀ r, ∀ p ∈ block r, ((T + r : ℕ) : ℝ) ≤ p.1) :
    atomSublevel D (atomBlockPrefix initial block k) =
      atomSublevel D (atomBlockPrefix initial block n) := by
  apply atomSublevel_atomBlockPrefix_eq_of_above D initial block hnk
  intro r hnr p hp
  have hnr' : ((T + n : ℕ) : ℝ) ≤ ((T + r : ℕ) : ℝ) :=
    Nat.cast_le.mpr (Nat.add_le_add_left hnr T)
  exact (hD.trans_le hnr').trans_le (hlower r p hp)

/-- Every fixed sublevel becomes a fixed finite ordered list after finitely
many layers. The initial list and all repeated coordinates are retained. -/
theorem atomSublevel_atomBlockPrefix_eventually_constant (D : ℝ)
    (initial : List (ℝ × ℤ)) (block : ℕ → List (ℝ × ℤ)) (T : ℕ)
    (hlower : ∀ r, ∀ p ∈ block r, ((T + r : ℕ) : ℝ) ≤ p.1) :
    ∃ n : ℕ, ∀ k, n ≤ k →
      atomSublevel D (atomBlockPrefix initial block k) =
        atomSublevel D (atomBlockPrefix initial block n) := by
  obtain ⟨n, hn⟩ := exists_nat_gt D
  have hD : D < ((T + n : ℕ) : ℝ) :=
    hn.trans_le (Nat.cast_le.mpr (Nat.le_add_left n T))
  exact ⟨n, fun k hnk =>
    atomSublevel_atomBlockPrefix_eq_of_layer_lower D initial block T hnk hD hlower⟩

/-- Every additive sublevel observable eventually stabilizes along the same atom prefixes. -/
theorem sum_map_atomSublevel_atomBlockPrefix_eventually_constant
    {A : Type*} [AddCommMonoid A] (D : ℝ) (initial : List (ℝ × ℤ))
    (block : ℕ → List (ℝ × ℤ)) (T : ℕ)
    (hlower : ∀ r, ∀ p ∈ block r, ((T + r : ℕ) : ℝ) ≤ p.1) (f : ℝ × ℤ → A) :
    ∃ n : ℕ, ∀ k, n ≤ k →
      ((atomSublevel D (atomBlockPrefix initial block k)).map f).sum =
        ((atomSublevel D (atomBlockPrefix initial block n)).map f).sum := by
  obtain ⟨n, hn⟩ := atomSublevel_atomBlockPrefix_eventually_constant D initial block T hlower
  exact ⟨n, fun k hnk => by rw [hn k hnk]⟩

end GapFamily.Construction
