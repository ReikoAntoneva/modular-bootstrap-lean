import BTZEntropy.Observable
import GapFamily.SpectralClass
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Thermal sums of complete descendant modules

This module first proves generic sum algebra, including the exact vacuum null
subtraction. The Euler-product theorem supplies the partition-series
summability used in the public descendant endpoint.
-/

noncomputable section

namespace BTZEntropy

/-- The Boltzmann weight of one chiral nondegenerate descendant level. -/
def partitionThermalTerm (β : ℝ) (n : ℕ) : ℝ :=
  (partitionCount n : ℝ) * Real.exp (-β * (n : ℝ))

/-- The chiral descendant partition function before the ground-state energy. -/
def partitionThermal (β : ℝ) : ℝ := ∑' n, partitionThermalTerm β n

/-- The corresponding chiral vacuum level weight. -/
def vacuumThermalTerm (β : ℝ) (n : ℕ) : ℝ :=
  (vacuumPartitionCount n : ℝ) * Real.exp (-β * (n : ℝ))

/-- The null-subtracted chiral vacuum partition function. -/
def vacuumThermal (β : ℝ) : ℝ := ∑' n, vacuumThermalTerm β n

/-- Primary-only thermal weight, before adding the cylinder vacuum shift. -/
def primaryThermalTerm (β : ℝ) (s : GapFamily.Spectrum) (p : s.support) : ℝ :=
  (s.multiplicity p : ℝ) * Real.exp (-β * GapFamily.dimension p)

/-- The primary thermal sum uses the exact same support and multiplicities. -/
def primaryThermal (β : ℝ) (s : GapFamily.Spectrum) : ℝ :=
  ∑' p, primaryThermalTerm β s p

/-- Complete-state Boltzmann weight for the observable's state labels. -/
def stateThermalTerm (β c : ℝ) (s : GapFamily.Spectrum) (v : StateLevel s) : ℝ :=
  (stateMultiplicity s v : ℝ) * Real.exp (-β * stateEnergy c s v)

/-- The full-state thermal partition function. -/
def stateThermal (β c : ℝ) (s : GapFamily.Spectrum) : ℝ :=
  ∑' v, stateThermalTerm β c s v

theorem partitionCount_pred_le {n : ℕ} (hn : 0 < n) :
    partitionCount (n - 1) ≤ partitionCount n := by
  unfold partitionCount
  rw [← Fintype.card_congr (Nat.Partition.partitionWithPartEquiv (by decide) hn)]
  exact Fintype.card_subtype_le _

theorem vacuumPartitionCount_le (n : ℕ) : vacuumPartitionCount n ≤ partitionCount n :=
  Fintype.card_subtype_le _

theorem vacuumPartitionCount_cast_succ (n : ℕ) :
    (vacuumPartitionCount (n + 1) : ℝ) =
      (partitionCount (n + 1) : ℝ) - (partitionCount n : ℝ) := by
  rw [vacuumPartitionCount_eq_sub (Nat.succ_pos n),
    Nat.cast_sub (partitionCount_pred_le (Nat.succ_pos n))]
  simp

theorem partitionThermalTerm_nonneg (β : ℝ) (n : ℕ) :
    0 ≤ partitionThermalTerm β n := by unfold partitionThermalTerm; positivity

theorem vacuumThermalTerm_nonneg (β : ℝ) (n : ℕ) :
    0 ≤ vacuumThermalTerm β n := by unfold vacuumThermalTerm; positivity

theorem primaryThermalTerm_nonneg (β : ℝ) (s : GapFamily.Spectrum)
    (p : s.support) : 0 ≤ primaryThermalTerm β s p := by
  unfold primaryThermalTerm; positivity

theorem stateThermalTerm_nonneg (β c : ℝ) (s : GapFamily.Spectrum)
    (v : StateLevel s) : 0 ≤ stateThermalTerm β c s v := by
  unfold stateThermalTerm; positivity

theorem vacuumThermalTerm_le (β : ℝ) (n : ℕ) :
    vacuumThermalTerm β n ≤ partitionThermalTerm β n := by
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (vacuumPartitionCount_le n))
    (Real.exp_pos _).le

theorem summable_vacuumThermalTerm_of_partition {β : ℝ}
    (h : Summable (partitionThermalTerm β)) : Summable (vacuumThermalTerm β) :=
  h.of_nonneg_of_le (vacuumThermalTerm_nonneg β) (vacuumThermalTerm_le β)

theorem vacuumThermalTerm_succ (β : ℝ) (n : ℕ) :
    vacuumThermalTerm β (n + 1) = partitionThermalTerm β (n + 1) -
      Real.exp (-β) * partitionThermalTerm β n := by
  unfold vacuumThermalTerm partitionThermalTerm
  rw [vacuumPartitionCount_cast_succ, Nat.cast_add, Nat.cast_one,
    mul_add, mul_one, Real.exp_add]
  ring

/-- The vacuum null module removes precisely one shifted nondegenerate tower. -/
theorem vacuumThermal_eq_of_summable {β : ℝ}
    (h : Summable (partitionThermalTerm β)) :
    vacuumThermal β = (1 - Real.exp (-β)) * partitionThermal β := by
  have hv := summable_vacuumThermalTerm_of_partition h
  have hpShift := (summable_nat_add_iff 1).mpr h
  have hpart := h.sum_add_tsum_nat_add 1
  have hvac := hv.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, partitionThermalTerm, vacuumThermalTerm,
    partitionCount_zero, vacuumPartitionCount_zero, Nat.cast_one, Nat.cast_zero,
    mul_zero, Real.exp_zero, mul_one] at hpart hvac
  have htail : (∑' n, vacuumThermalTerm β (n + 1)) =
      (∑' n, partitionThermalTerm β (n + 1)) -
        Real.exp (-β) * partitionThermal β := by
    simp_rw [vacuumThermalTerm_succ]
    rw [hpShift.tsum_sub (h.mul_left _), tsum_mul_left]
    rfl
  change 1 + (∑' n, vacuumThermalTerm β (n + 1)) = vacuumThermal β at hvac
  change 1 + (∑' n, partitionThermalTerm β (n + 1)) = partitionThermal β at hpart
  rw [htail] at hvac
  linarith

/-- The admissible primary thermal summability uses any positive inverse temperature. -/
theorem summable_primaryThermalTerm {c β : ℝ} {s : GapFamily.Spectrum}
    (hs : GapFamily.TorusAdmissible c s) (hβ : 0 < β) :
    Summable (primaryThermalTerm β s) := hs.thermal_summable_exp β hβ

/-- Factorization of the actual full-state sum, assuming the chiral series
convergence that is later discharged by the Euler-product theorem. -/
theorem hasSum_stateThermalTerm_of_partition {c β : ℝ}
    {s : GapFamily.Spectrum} (hs : GapFamily.TorusAdmissible c s) (hβ : 0 < β)
    (h : Summable (partitionThermalTerm β)) :
    HasSum (stateThermalTerm β c s)
      (Real.exp (β * c / 12) *
        (vacuumThermal β ^ 2 + primaryThermal β s * partitionThermal β ^ 2)) := by
  have hv := summable_vacuumThermalTerm_of_partition h
  have hp := summable_primaryThermalTerm hs hβ
  have hvv := hv.mul_of_nonneg hv (vacuumThermalTerm_nonneg β)
    (vacuumThermalTerm_nonneg β)
  have hdd := h.mul_of_nonneg h (partitionThermalTerm_nonneg β)
    (partitionThermalTerm_nonneg β)
  have hddsum := h.hasSum.mul h.hasSum hdd
  have hpd := hp.mul_of_nonneg hdd (primaryThermalTerm_nonneg β s)
    (fun n => mul_nonneg (partitionThermalTerm_nonneg β n.1)
      (partitionThermalTerm_nonneg β n.2))
  have hvac : HasSum ((stateThermalTerm β c s) ∘ Sum.inl)
      (Real.exp (β * c / 12) * vacuumThermal β ^ 2) := by
    convert ((hv.hasSum.mul hv.hasSum hvv).mul_left (Real.exp (β * c / 12))) using 1
    · funext n
      rcases n with ⟨nL, nR⟩
      simp only [Function.comp_apply, stateThermalTerm, stateMultiplicity,
        stateEnergy, Nat.cast_mul, vacuumThermalTerm]
      rw [show -β * ((nL : ℝ) + (nR : ℝ) - c / 12) =
        β * c / 12 + (-β * (nL : ℝ)) + (-β * (nR : ℝ)) by ring,
        Real.exp_add, Real.exp_add]
      ring
    · simp [vacuumThermal, pow_two]
  have hprim : HasSum ((stateThermalTerm β c s) ∘ Sum.inr)
      (Real.exp (β * c / 12) * (primaryThermal β s * partitionThermal β ^ 2)) := by
    convert ((hp.hasSum.mul hddsum hpd).mul_left (Real.exp (β * c / 12))) using 1
    · funext n
      rcases n with ⟨p, nL, nR⟩
      simp only [Function.comp_apply, stateThermalTerm, stateMultiplicity,
        stateEnergy, Nat.cast_mul, primaryThermalTerm, partitionThermalTerm]
      rw [show -β * (GapFamily.dimension p + (nL : ℝ) + (nR : ℝ) - c / 12) =
        β * c / 12 + (-β * GapFamily.dimension p) +
          (-β * (nL : ℝ)) + (-β * (nR : ℝ)) by ring,
        Real.exp_add, Real.exp_add, Real.exp_add]
      ring
    · simp [primaryThermal, partitionThermal, pow_two]
  convert hvac.sum hprim using 1; ring

end BTZEntropy
