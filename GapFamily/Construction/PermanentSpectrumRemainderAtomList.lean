import GapFamily.Construction.PermanentSpectrum

/-! The finite permanent unit-node prefix as its literal ordered atom list.
Every repeated energy-spin pair is retained as a separate list occurrence. -/

noncomputable section
namespace GapFamily.Construction.PermanentSpectrumData
open scoped UpperHalfPlane

variable {b : ℝ} (D : PermanentSpectrumData b)

/-- The marker, the finite initial block, and the first `n` complete layer
blocks, in their original finite-index order. -/
def permanentAtomList (n : ℕ) : List (ℝ × ℤ) :=
  (b, 0) :: (List.ofFn (fun i : Fin D.initialCount =>
      (D.initialEnergy i, D.initialSpin i)) ++
    (List.range n).flatMap (fun m => List.ofFn (fun i : Fin (D.layerCount m) =>
      (D.layerEnergy m i, D.layerSpin m i))))

@[simp] theorem permanentAtomList_zero :
    D.permanentAtomList 0 =
      (b, 0) :: List.ofFn (fun i : Fin D.initialCount =>
        (D.initialEnergy i, D.initialSpin i)) := by
  simp [permanentAtomList]

/-- Increasing the prefix appends precisely the actual next finite layer. -/
theorem permanentAtomList_succ (n : ℕ) :
    D.permanentAtomList (n + 1) = D.permanentAtomList n ++
      List.ofFn (fun i : Fin (D.layerCount n) =>
        (D.layerEnergy n i, D.layerSpin n i)) := by
  simp [permanentAtomList, List.range_succ, List.flatMap_append, List.append_assoc]

/-- Any additive atom contribution agrees with the literal permanent-node
sum, including all multiplicities from repeated list entries. -/
theorem sum_map_permanentAtomList {A : Type*} [AddCommMonoid A]
    (f : ℝ × ℤ → A) (n : ℕ) :
    ((D.permanentAtomList n).map f).sum =
      permanentNodePrefix (fun i => f (D.energy i, D.spin i)) n := by
  induction n with
  | zero =>
      simp only [permanentAtomList_zero, List.map_cons, List.sum_cons,
        List.map_ofFn, List.sum_ofFn, permanentNodePrefix_zero]
      rfl
  | succ n ih =>
      rw [permanentAtomList_succ, List.map_append, List.sum_append, ih,
        permanentNodePrefix_succ]
      congr 1
      simp only [List.map_ofFn, List.sum_ofFn]
      rfl

/-- The actual threshold seed sum over the literal finite atom history. -/
theorem pointSeed_sum_permanentAtomList (n : ℕ) (τ : ℍ) :
    ((D.permanentAtomList n).map
      (fun p => Analytic.pointSeed p.1 p.2 (1 / 2) τ)).sum =
      permanentNodePrefix (fun i => D.unitSeed i τ) n :=
  D.sum_map_permanentAtomList (fun p => Analytic.pointSeed p.1 p.2 (1 / 2) τ) n

/-- Adding the prescribed vacuum gives exactly the finite reduced prefix. -/
theorem vacuum_add_pointSeed_sum_permanentAtomList (c : ℝ) (n : ℕ) (τ : ℍ) :
    (Real.sqrt τ.im : ℂ) * vacuumNumerator c τ +
      ((D.permanentAtomList n).map
        (fun p => Analytic.pointSeed p.1 p.2 (1 / 2) τ)).sum =
      D.reducedPrefix c n τ := by
  rw [D.pointSeed_sum_permanentAtomList]
  rfl

/-- Data constructed from lists recover those very lists, in the same order
and with every repeated atom retained. -/
theorem ofLists_permanentAtomList (hb : 0 ≤ b)
    (initial : List (ℝ × ℤ)) (layer : ℕ → List (ℝ × ℤ))
    (hinitial : ∀ p ∈ initial, b ≤ p.1 ∧ |(p.2 : ℝ)| ≤ p.1)
    (hlayer : ∀ (m : ℕ) p, p ∈ layer m → b ≤ p.1 ∧ |(p.2 : ℝ)| ≤ p.1 ∧
      (m : ℝ) ≤ p.1 ∧ p.1 < (m : ℝ) + 2)
    (n : ℕ) :
    (ofLists hb initial layer hinitial hlayer).permanentAtomList n =
      (b, 0) :: (initial ++ (List.range n).flatMap layer) := by
  simp only [permanentAtomList, ofLists, Prod.mk.eta, List.ofFn_get]

end GapFamily.Construction.PermanentSpectrumData
