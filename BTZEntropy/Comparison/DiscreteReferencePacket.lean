import BTZEntropy.Comparison.InitialPacketFamily
import BTZEntropy.Comparison.DensityErrorTest

/-! The finite vacuum, marker and initial-node packet in the exact
reference comparison is bounded by its actual complete descendant count. -/

noncomputable section

open Set Real
open GapFamily GapFamily.Construction BTZEntropy.Construction
open scoped BigOperators

namespace BTZEntropy.Comparison

variable {B : ℝ} {g : FixedFamilyGeometry B} {a : ℝ} {δ : ℝ}

/-- Null-subtracted vacuum multiplicities remain nonnegative. -/
theorem vacuumFiniteLevelCount_nonneg (φ : SmoothKernel) (c E : ℝ)
    (F : Finset (ℕ × ℕ)) : 0 ≤ vacuumFiniteLevelCount φ c E F := by
  apply Finset.sum_nonneg
  intro l hl
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (φ.nonneg _)

/-- Every finite vacuum packet is bounded by its complete descendant
module, with the same cylinder ground energy and null subtraction. -/
theorem vacuumFiniteLevelCount_le (φ : SmoothKernel) (c E : ℝ)
    (F : Finset (ℕ × ℕ)) :
    vacuumFiniteLevelCount φ c E F ≤ vacuumSmoothCount φ c E := by
  obtain ⟨R, H, hR0, hH, hR, hφ⟩ := exists_kernel_upper_bound φ
  have hsum := moduleSmoothTerm_summable_of_partition φ
    (fun _ => Nat.cast_nonneg _) (fun n => Nat.cast_le.mpr (vacuumPartitionCount_le n))
    (e := -c / 12) (E := E) (β := 1) (by norm_num) hH hR hφ
    (summable_partitionThermalTerm (by norm_num))
  have hle := hsum.sum_le_tsum F
    (fun v _ => moduleSmoothTerm_nonneg φ (fun _ => Nat.cast_nonneg _) _ _ v)
  convert hle using 1
  · unfold vacuumFiniteLevelCount
    apply Finset.sum_congr rfl
    intro v hv
    simp only [moduleSmoothTerm]
    congr 1
    congr 1
    ring
  · rfl

/-- The finite packet appearing in the actual active-prefix decomposition.
The original initial list retains all repeated node occurrences. -/
def fixedFamilyFinitePacket (φ : SmoothKernel) (d : FixedFamilyDatum g a δ)
    (E : ℝ) (F : Finset (ℕ × ℕ)) : ℝ :=
  vacuumFiniteLevelCount φ (gapFamilyCharge a) E F + primaryDescendantTest φ E F δ +
    (d.initialState.nodes.map (fun p => primaryDescendantTest φ E F p.1)).sum

/-- The full initial module count is exactly the sum over occurrences in
the selected datum's initial node list. -/
theorem fixedFamilyInitialSmoothCount_eq_list (φ : SmoothKernel)
    (d : FixedFamilyDatum g a δ) (E : ℝ) :
    fixedFamilyInitialSmoothCount φ d E =
      (d.initialState.nodes.map (fun p =>
        moduleSmoothCount φ (fun n => (partitionCount n : ℝ)) (p.1 - 1 / 12) E)).sum := by
  conv_rhs => rw [← List.ofFn_get d.initialState.nodes]
  simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply,
    fixedFamilyInitialSmoothCount, initialPacketSmoothCount, Nat.cast_one, one_mul,
    fixedFamilyInitialEnergy]

/-- Arbitrary finite descendant packets are bounded by the complete
modules on precisely the same original initial-node occurrences. -/
theorem fixedFamily_initialFiniteLevelCount_le (φ : SmoothKernel)
    (d : FixedFamilyDatum g a δ) (E : ℝ) (F : Finset (ℕ × ℕ)) :
    (d.initialState.nodes.map (fun p => primaryDescendantTest φ E F p.1)).sum ≤
      fixedFamilyInitialSmoothCount φ d E := by
  rw [fixedFamilyInitialSmoothCount_eq_list]
  conv_lhs => rw [← List.ofFn_get d.initialState.nodes]
  conv_rhs => rw [← List.ofFn_get d.initialState.nodes]
  simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply]
  apply Finset.sum_le_sum
  intro p hp
  exact primaryDescendantTest_le_module φ _ E F

/-- Each initial-node occurrence contributes a nonnegative finite packet. -/
theorem fixedFamily_initialFiniteLevelCount_nonneg (φ : SmoothKernel)
    (d : FixedFamilyDatum g a δ) (E : ℝ) (F : Finset (ℕ × ℕ)) :
    0 ≤ (d.initialState.nodes.map (fun p => primaryDescendantTest φ E F p.1)).sum := by
  apply List.sum_nonneg
  intro t ht
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ht
  exact primaryDescendantTest_nonneg φ E F p.1

/-- The exact finite initial packet in the reference decomposition is
nonnegative for every descendant selection. -/
theorem fixedFamilyFinitePacket_nonneg (φ : SmoothKernel)
    (d : FixedFamilyDatum g a δ) (E : ℝ) (F : Finset (ℕ × ℕ)) :
    0 ≤ fixedFamilyFinitePacket φ d E F :=
  add_nonneg (add_nonneg (vacuumFiniteLevelCount_nonneg φ _ E F)
    (primaryDescendantTest_nonneg φ E F δ))
    (fixedFamily_initialFiniteLevelCount_nonneg φ d E F)

/-- The finite vacuum, marker and actual initial-node terms are bounded
by the corresponding complete packet. No cutoff or support bound is needed. -/
theorem fixedFamilyFinitePacket_le_complete (φ : SmoothKernel)
    (d : FixedFamilyDatum g a δ) (E : ℝ) (F : Finset (ℕ × ℕ)) :
    fixedFamilyFinitePacket φ d E F ≤
      fixedFamilyMarkedInitialSmoothCount φ d E +
        vacuumSmoothCount φ (gapFamilyCharge a) E := by
  have hv := vacuumFiniteLevelCount_le φ (gapFamilyCharge a) E F
  have hm := primaryDescendantTest_le_module φ δ E F
  have hi := fixedFamily_initialFiniteLevelCount_le φ d E F
  rw [fixedFamilyMarkedInitialSmoothCount_eq]
  unfold fixedFamilyFinitePacket
  linarith

/-- Absolute-value form for the exact finite packet in the smooth-count
comparison, ready for the uniform subexponential estimate. -/
theorem fixedFamilyFinitePacket_abs_le_complete (φ : SmoothKernel)
    (d : FixedFamilyDatum g a δ) (E : ℝ) (F : Finset (ℕ × ℕ)) :
    |fixedFamilyFinitePacket φ d E F| ≤
      fixedFamilyMarkedInitialSmoothCount φ d E +
        vacuumSmoothCount φ (gapFamilyCharge a) E := by
  rw [abs_of_nonneg (fixedFamilyFinitePacket_nonneg φ d E F)]
  exact fixedFamilyFinitePacket_le_complete φ d E F

end BTZEntropy.Comparison
