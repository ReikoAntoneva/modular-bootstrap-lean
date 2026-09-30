import GapFamily.Contract
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Order.Compact

/-!
# The full-state smooth observable

The primary spectrum is inherited from `GapFamily`. Each left and right
Virasoro level is counted with its partition multiplicity. The vacuum uses
partitions with no part equal to one, so its null descendants are removed.
Cylinder energy is total dimension minus `c / 12`, rather than the reduced
primary energy used by the repair construction.

These definitions count the prescribed character modules. Identifying their
thermal generating function with `GapFamily.partitionFunction` is a separate
analytic theorem, not an assumption built into the observable.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace BTZEntropy

/-- A fixed, nonnegative, normalized smooth kernel of compact support. -/
structure SmoothKernel where
  toFun : ℝ → ℝ
  smooth : ContDiff ℝ ∞ toFun
  nonneg : ∀ u, 0 ≤ toFun u
  compactSupport : HasCompactSupport toFun
  normalized : ∫ u, toFun u = 1

instance : CoeFun SmoothKernel (fun _ => ℝ → ℝ) := ⟨SmoothKernel.toFun⟩

/-- The nondegenerate chiral Virasoro multiplicity at level `n`. -/
def partitionCount (n : ℕ) : ℕ := Fintype.card (Nat.Partition n)

/-- The vacuum chiral multiplicity: only modes of level at least two occur. -/
def vacuumPartitionCount (n : ℕ) : ℕ :=
  Fintype.card {p : Nat.Partition n // 1 ∉ p.parts}

@[simp] theorem partitionCount_zero : partitionCount 0 = 1 := by
  simp [partitionCount]

@[simp] theorem partitionCount_one : partitionCount 1 = 1 := by
  simp [partitionCount]

@[simp] theorem vacuumPartitionCount_zero : vacuumPartitionCount 0 = 1 := by
  classical
  simp [vacuumPartitionCount]

@[simp] theorem vacuumPartitionCount_one : vacuumPartitionCount 1 = 0 := by
  classical
  simp [vacuumPartitionCount]

/-- Removing one part equal to one identifies the vacuum null submodule.
The level-zero case is stated separately, so no `p(-1)` convention is needed. -/
theorem vacuumPartitionCount_eq_sub {n : ℕ} (hn : 0 < n) :
    vacuumPartitionCount n = partitionCount n - partitionCount (n - 1) := by
  unfold vacuumPartitionCount partitionCount
  rw [Fintype.card_subtype_compl (fun p : Nat.Partition n => 1 ∈ p.parts)]
  rw [Fintype.card_congr (Nat.Partition.partitionWithPartEquiv (by decide) hn)]

/-- The labels keep left and right levels separately and include every spin.
Different labels with the same energy are all included with their multiplicity. -/
abbrev StateLevel (s : GapFamily.Spectrum) :=
  (ℕ × ℕ) ⊕ (s.support × (ℕ × ℕ))

/-- Integer degeneracy for the vacuum or one primary and two descendant levels. -/
def stateMultiplicity (s : GapFamily.Spectrum) : StateLevel s → ℕ
  | .inl (nL, nR) => vacuumPartitionCount nL * vacuumPartitionCount nR
  | .inr (p, nL, nR) => s.multiplicity p * partitionCount nL * partitionCount nR

/-- Physical cylinder energy of the full state. -/
def stateEnergy (c : ℝ) (s : GapFamily.Spectrum) : StateLevel s → ℝ
  | .inl (nL, nR) => (nL : ℝ) + (nR : ℝ) - c / 12
  | .inr (p, nL, nR) =>
      GapFamily.dimension p + (nL : ℝ) + (nR : ℝ) - c / 12

/-- Total spin includes the signed difference of the two descendant levels. -/
def stateSpin (s : GapFamily.Spectrum) : StateLevel s → ℝ
  | .inl (nL, nR) => (nL : ℝ) - (nR : ℝ)
  | .inr (p, nL, nR) => GapFamily.spin p + (nL : ℝ) - (nR : ℝ)

/-- The finite-`c` difference between reduced primary and cylinder energy. -/
theorem stateEnergy_primary (c : ℝ) (s : GapFamily.Spectrum)
    (p : s.support) (nL nR : ℕ) :
    stateEnergy c s (.inr (p, nL, nR)) =
      GapFamily.energy c p - 1 / 12 + (nL : ℝ) + (nR : ℝ) := by
  dsimp [stateEnergy, GapFamily.energy, GapFamily.shift]
  ring

@[simp] theorem vacuum_ground_multiplicity (s : GapFamily.Spectrum) :
    stateMultiplicity s (.inl (0, 0)) = 1 := by
  simp [stateMultiplicity]

@[simp] theorem primary_ground_multiplicity (s : GapFamily.Spectrum)
    (p : s.support) : stateMultiplicity s (.inr (p, 0, 0)) = s.multiplicity p := by
  simp [stateMultiplicity]

/-- Integer primary spin implies integer spin for every full-state label. -/
theorem stateSpin_integral {c : ℝ} {s : GapFamily.Spectrum}
    (hs : GapFamily.TorusAdmissible c s) (v : StateLevel s) :
    ∃ j : ℤ, stateSpin s v = (j : ℝ) := by
  rcases v with ⟨nL, nR⟩ | ⟨p, nL, nR⟩
  · exact ⟨(nL : ℤ) - (nR : ℤ), by simp [stateSpin]⟩
  · obtain ⟨j, hj⟩ := hs.spin_integral p p.property
    exact ⟨j + (nL : ℤ) - (nR : ℤ), by simp [stateSpin, hj]⟩

/-- One contribution to the full-state smoothed density. -/
def smoothTerm (φ : SmoothKernel) (c : ℝ) (s : GapFamily.Spectrum)
    (E : ℝ) (v : StateLevel s) : ℝ :=
  (stateMultiplicity s v : ℝ) * φ (stateEnergy c s v - E)

/-- The sum includes the vacuum, every primary copy, both descendant towers,
and every spin. Local finiteness below will make this a finite sum. -/
def smoothCount (φ : SmoothKernel) (c : ℝ) (s : GapFamily.Spectrum)
    (E : ℝ) : ℝ := ∑' v : StateLevel s, smoothTerm φ c s E v

/-- Spectral entropy. Its asymptotic use additionally requires a positive count. -/
def smoothEntropy (φ : SmoothKernel) (c : ℝ) (s : GapFamily.Spectrum)
    (E : ℝ) : ℝ := Real.log (smoothCount φ c s E)

theorem smoothTerm_nonneg (φ : SmoothKernel) (c : ℝ)
    (s : GapFamily.Spectrum) (E : ℝ) (v : StateLevel s) :
    0 ≤ smoothTerm φ c s E v :=
  mul_nonneg (Nat.cast_nonneg _) (φ.nonneg _)

theorem smoothCount_nonneg (φ : SmoothKernel) (c : ℝ)
    (s : GapFamily.Spectrum) (E : ℝ) : 0 ≤ smoothCount φ c s E :=
  tsum_nonneg (smoothTerm_nonneg φ c s E)

/-- A compact kernel encounters only finitely many descendant-level labels of
an admissible spectrum. This proves that the defining `tsum` is an ordinary
finite sum, even before any large-charge asymptotics are considered. -/
theorem smoothTerm_hasFiniteSupport (φ : SmoothKernel) {c : ℝ}
    {s : GapFamily.Spectrum} (hs : GapFamily.TorusAdmissible c s) (E : ℝ) :
    Function.HasFiniteSupport (smoothTerm φ c s E) := by
  obtain ⟨R, hR⟩ := φ.compactSupport.bddAbove
  obtain ⟨N, hN⟩ := exists_nat_gt (E + R + c / 12)
  let P : Set s.support := {p | GapFamily.dimension p ≤ (N : ℝ)}
  let L : Set (ℕ × ℕ) := Set.Iic N ×ˢ Set.Iic N
  have hP : P.Finite := by
    have h := (hs.locally_finite (N : ℝ)).preimage
      (f := fun p : s.support => p.val) (fun _ _ _ _ h => Subtype.ext h)
    simpa [P] using h
  have hL : L.Finite := (Set.finite_Iic N).prod (Set.finite_Iic N)
  have hfin : (Sum.inl '' L ∪ Sum.inr '' (P ×ˢ L) : Set (StateLevel s)).Finite :=
    (hL.image Sum.inl).union ((hP.prod hL).image Sum.inr)
  apply hfin.subset
  intro v hv
  change smoothTerm φ c s E v ≠ 0 at hv
  have hφ : φ (stateEnergy c s v - E) ≠ 0 := (mul_ne_zero_iff.mp hv).2
  have hbound := hR (subset_tsupport φ hφ)
  rcases v with ⟨nL, nR⟩ | ⟨p, nL, nR⟩
  · dsimp [stateEnergy] at hbound
    have hnL : nL ≤ N := by
      apply (Nat.cast_le (α := ℝ)).mp
      linarith [Nat.cast_nonneg (α := ℝ) nR]
    have hnR : nR ≤ N := by
      apply (Nat.cast_le (α := ℝ)).mp
      linarith [Nat.cast_nonneg (α := ℝ) nL]
    exact Or.inl ⟨(nL, nR), ⟨hnL, hnR⟩, rfl⟩
  · dsimp [stateEnergy] at hbound
    have hp := hs.weight_pos p p.property
    have hdim : 0 ≤ GapFamily.dimension p := by
      dsimp [GapFamily.dimension]
      linarith [hp.1, hp.2]
    have hpN : GapFamily.dimension p ≤ (N : ℝ) := by
      linarith [Nat.cast_nonneg (α := ℝ) nL, Nat.cast_nonneg (α := ℝ) nR]
    have hnL : nL ≤ N := by
      apply (Nat.cast_le (α := ℝ)).mp
      linarith [Nat.cast_nonneg (α := ℝ) nR]
    have hnR : nR ≤ N := by
      apply (Nat.cast_le (α := ℝ)).mp
      linarith [Nat.cast_nonneg (α := ℝ) nL]
    exact Or.inr ⟨(p, nL, nR), ⟨hpN, hnL, hnR⟩, rfl⟩

/-- No convergence hypothesis is missing from the full-state count on an
admissible spectrum. Compact support and local finiteness suffice. -/
theorem smoothTerm_summable (φ : SmoothKernel) {c : ℝ}
    {s : GapFamily.Spectrum} (hs : GapFamily.TorusAdmissible c s) (E : ℝ) :
    Summable (smoothTerm φ c s E) :=
  summable_of_hasFiniteSupport (smoothTerm_hasFiniteSupport φ hs E)

/-- A finite-sum presentation of the observable follows from the proved
finite support and does not require a choice of state-counting cutoff. -/
theorem smoothCount_eq_finite_sum (φ : SmoothKernel) {c : ℝ}
    {s : GapFamily.Spectrum} (hs : GapFamily.TorusAdmissible c s) (E : ℝ) :
    ∃ F : Finset (StateLevel s),
      smoothCount φ c s E = ∑ v ∈ F, smoothTerm φ c s E v := by
  classical
  have h : (Function.support (smoothTerm φ c s E)).Finite :=
    smoothTerm_hasFiniteSupport φ hs E
  refine ⟨h.toFinset, tsum_eq_sum ?_⟩
  intro v hv
  simpa only [Set.Finite.mem_toFinset, Function.mem_support, not_not] using hv

/-- A single contributing full-state level makes the count positive. The
large-charge existence of such contributions is a later asymptotic theorem. -/
theorem smoothCount_pos_of_term_pos (φ : SmoothKernel) {c : ℝ}
    {s : GapFamily.Spectrum} (hs : GapFamily.TorusAdmissible c s) (E : ℝ)
    (v : StateLevel s) (hv : 0 < smoothTerm φ c s E v) :
    0 < smoothCount φ c s E :=
  hv.trans_le ((smoothTerm_summable φ hs E).le_tsum v
    (fun w _ => smoothTerm_nonneg φ c s E w))

/-- On the positive-count domain, the logarithm has its intended meaning. -/
theorem exp_smoothEntropy (φ : SmoothKernel) (c : ℝ)
    (s : GapFamily.Spectrum) (E : ℝ) (h : 0 < smoothCount φ c s E) :
    Real.exp (smoothEntropy φ c s E) = smoothCount φ c s E :=
  Real.exp_log h

end BTZEntropy
