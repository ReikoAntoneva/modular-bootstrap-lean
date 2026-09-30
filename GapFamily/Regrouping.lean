import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Data.Set.Card

/-!
# Regrouping unit nodes into distinct spectral coordinates

Local finiteness is imposed on nodes, before repeated coordinates are collapsed.
It therefore supplies a finite, nonempty fibre over every coordinate in the range.
The resulting natural multiplicities preserve every summable coordinate-dependent
series, and in particular preserve absolutely convergent thermal and complex series.
-/

namespace GapFamily.Regrouping

variable {ι κ : Type*} (coordinate : ι → κ) (height : κ → ℝ)

/-- Node local finiteness counts repeated nodes separately. -/
def LocallyFinite : Prop :=
  ∀ bound : ℝ, {i : ι | height (coordinate i) ≤ bound}.Finite

/-- Distinct coordinates, with membership witnessed by an original node. -/
abbrev Coordinate := Set.range coordinate

/-- The natural surjection from nodes onto distinct coordinates. -/
def nodeCoordinate : ι → Coordinate coordinate := Set.rangeFactorization coordinate

/-- The fibre contains every unit node at the indicated coordinate. -/
abbrev Fiber (p : Coordinate coordinate) := (nodeCoordinate coordinate) ⁻¹' {p}

/-- Physical multiplicity after merging coincident unit nodes. -/
noncomputable def multiplicity (p : Coordinate coordinate) : ℕ := Nat.card (Fiber coordinate p)

variable {coordinate height}

theorem fiber_finite (hlocal : LocallyFinite coordinate height)
    (p : Coordinate coordinate) : (Fiber coordinate p).Finite := by
  apply (hlocal (height p.val)).subset
  intro i hi
  have hc : coordinate i = p.val := congrArg Subtype.val hi
  change height (coordinate i) ≤ height p.val
  rw [hc]

theorem fiber_nonempty (p : Coordinate coordinate) : (Fiber coordinate p).Nonempty := by
  obtain ⟨i, hi⟩ := p.property
  refine ⟨i, ?_⟩
  exact Subtype.ext hi

theorem multiplicity_pos (hlocal : LocallyFinite coordinate height)
    (p : Coordinate coordinate) : 0 < multiplicity coordinate p := by
  let : Finite (Fiber coordinate p) := (fiber_finite hlocal p).to_subtype
  let : Nonempty (Fiber coordinate p) := (fiber_nonempty p).to_subtype
  exact Nat.card_pos

/-- Distinct coordinates inherit the same finite sublevel property. -/
theorem coordinate_locallyFinite (hlocal : LocallyFinite coordinate height) (bound : ℝ) :
    {p : Coordinate coordinate | height p.val ≤ bound}.Finite := by
  have heq : {p : Coordinate coordinate | height p.val ≤ bound} =
      nodeCoordinate coordinate '' {i : ι | height (coordinate i) ≤ bound} := by
    ext p
    constructor
    · intro hp
      obtain ⟨i, hi⟩ := p.property
      refine ⟨i, ?_, Subtype.ext hi⟩
      change height (coordinate i) ≤ bound
      change height p.val ≤ bound at hp
      simpa only [hi] using hp
    · rintro ⟨i, hi, rfl⟩
      exact hi
  rw [heq]
  exact (hlocal bound).image (nodeCoordinate coordinate)

/-- A countable node index gives a countable set of distinct coordinates. -/
theorem coordinate_countable [Countable ι] : Countable (Coordinate coordinate) :=
  (Set.countable_range coordinate).to_subtype

section Sum

variable {A : Type*} [NormedAddCommGroup A] [CompleteSpace A]

omit [CompleteSpace A] in
/-- Every fibre sum is exactly its natural multiplicity times the common term. -/
theorem fiber_tsum (hlocal : LocallyFinite coordinate height)
    (term : κ → A) (p : Coordinate coordinate) :
    (∑' i : Fiber coordinate p, term (coordinate i.val)) =
      multiplicity coordinate p • term p.val := by
  classical
  let := (fiber_finite hlocal p).fintype
  have hterm : (fun i : Fiber coordinate p ↦ term (coordinate i.val)) =
      fun _ : Fiber coordinate p ↦ term p.val := by
    funext i
    congr 1
    exact congrArg Subtype.val i.property
  rw [hterm, tsum_fintype]
  simp [multiplicity, Nat.card_eq_fintype_card]

/-- Summability supplies a valid regrouped sum, without relying on totalized `tsum`. -/
theorem hasSum_regroup (hlocal : LocallyFinite coordinate height) (term : κ → A)
    {total : A} (hsum : HasSum (fun i ↦ term (coordinate i)) total) :
    HasSum (fun p : Coordinate coordinate ↦ multiplicity coordinate p • term p.val) total := by
  have h := hsum.tsum_fiberwise (nodeCoordinate coordinate)
  simpa only [fiber_tsum hlocal term] using h

theorem summable_regroup (hlocal : LocallyFinite coordinate height) (term : κ → A)
    (hsum : Summable (fun i ↦ term (coordinate i))) :
    Summable (fun p : Coordinate coordinate ↦ multiplicity coordinate p • term p.val) :=
  (hasSum_regroup hlocal term hsum.hasSum).summable

theorem tsum_regroup (hlocal : LocallyFinite coordinate height) (term : κ → A)
    (hsum : Summable (fun i ↦ term (coordinate i))) :
    (∑' p : Coordinate coordinate, multiplicity coordinate p • term p.val) =
      ∑' i : ι, term (coordinate i) :=
  (hasSum_regroup hlocal term hsum.hasSum).tsum_eq

/-- Absolute convergence of unit nodes implies convergence after regrouping. -/
theorem summable_regroup_of_norm (hlocal : LocallyFinite coordinate height) (term : κ → A)
    (habs : Summable (fun i ↦ ‖term (coordinate i)‖)) :
    Summable (fun p : Coordinate coordinate ↦ multiplicity coordinate p • term p.val) :=
  summable_regroup hlocal term habs.of_norm

omit [CompleteSpace A] in
/-- Absolute convergence also holds for the regrouped series itself. -/
theorem summable_norm_regroup (hlocal : LocallyFinite coordinate height) (term : κ → A)
    (habs : Summable (fun i ↦ ‖term (coordinate i)‖)) :
    Summable (fun p : Coordinate coordinate ↦ ‖multiplicity coordinate p • term p.val‖) := by
  apply Summable.of_nonneg_of_le (fun p ↦ norm_nonneg _)
    (fun p ↦ norm_nsmul_le)
  simpa only [nsmul_eq_mul] using summable_regroup hlocal (fun p ↦ ‖term p‖) habs

/-- Absolute convergence certifies the equality of the two actual sums. -/
theorem tsum_regroup_of_norm (hlocal : LocallyFinite coordinate height) (term : κ → A)
    (habs : Summable (fun i ↦ ‖term (coordinate i)‖)) :
    (∑' p : Coordinate coordinate, multiplicity coordinate p • term p.val) =
      ∑' i : ι, term (coordinate i) :=
  tsum_regroup hlocal term habs.of_norm

omit [CompleteSpace A] in
/-- The absolute mass series itself is preserved under regrouping. -/
theorem tsum_norm_regroup (hlocal : LocallyFinite coordinate height) (term : κ → A)
    (habs : Summable (fun i ↦ ‖term (coordinate i)‖)) :
    (∑' p : Coordinate coordinate, (multiplicity coordinate p : ℝ) * ‖term p.val‖) =
      ∑' i : ι, ‖term (coordinate i)‖ := by
  simpa only [nsmul_eq_mul] using tsum_regroup hlocal (fun p ↦ ‖term p‖) habs

end Sum
end GapFamily.Regrouping
