import BTZEntropy.Analytic.DescendantThermal
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Initial packets with their complete descendant towers

The estimate uses the actual partition multiplicities and the same cylinder
energy convention as `smoothCount`. Its finite-packet mass is an explicit
input: this module does not assert an unproved bound for the construction's
initial cells. Positions enter only through a lower bound, so all constants
are independent of a node selector satisfying the same mass bound.
-/

noncomputable section

open Set Real
open scoped BigOperators

namespace BTZEntropy.Comparison

/-- One left-right descendant contribution from cylinder ground energy `e`.
The coefficient sequence may be the primary or null-subtracted vacuum one. -/
def moduleSmoothTerm (φ : SmoothKernel) (d : ℕ → ℝ) (e E : ℝ)
    (v : ℕ × ℕ) : ℝ := d v.1 * d v.2 * φ (e + v.1 + v.2 - E)

/-- The complete all-spin count of one descendant module. -/
def moduleSmoothCount (φ : SmoothKernel) (d : ℕ → ℝ) (e E : ℝ) : ℝ :=
  ∑' v : ℕ × ℕ, moduleSmoothTerm φ d e E v

/-- A finite packet of primary occurrences, with natural multiplicity.
The supplied energies are shifted primary energies, before `-1/12`. -/
def initialPacketSmoothCount {ι : Type*} [Fintype ι] (φ : SmoothKernel)
    (energy : ι → ℝ) (weight : ι → ℕ) (E : ℝ) : ℝ :=
  ∑ i, (weight i : ℝ) * moduleSmoothCount φ (fun n => (partitionCount n : ℝ))
    (energy i - 1 / 12) E

/-- The unique vacuum module, with its level-one null submodule removed. -/
def vacuumSmoothCount (φ : SmoothKernel) (c E : ℝ) : ℝ :=
  moduleSmoothCount φ (fun n => (vacuumPartitionCount n : ℝ)) (-c / 12) E

/-- The vacuum packet is exactly the vacuum part of the full-state
observable, with the same null-subtracted multiplicities. -/
theorem vacuumSmoothCount_eq_observable (φ : SmoothKernel) (c E : ℝ)
    (s : GapFamily.Spectrum) :
    vacuumSmoothCount φ c E = ∑' v : ℕ × ℕ, smoothTerm φ c s E (.inl v) := by
  unfold vacuumSmoothCount moduleSmoothCount
  apply tsum_congr
  rintro ⟨n, m⟩
  simp only [moduleSmoothTerm, smoothTerm, stateMultiplicity, stateEnergy, Nat.cast_mul]
  congr 2
  ring

/-- A primary module is exactly its part of the full-state observable;
its natural multiplicity counts every primary occurrence. -/
theorem primaryModuleSmoothCount_eq_observable (φ : SmoothKernel) (c E : ℝ)
    (s : GapFamily.Spectrum) (p : s.support) :
    (s.multiplicity p : ℝ) *
        moduleSmoothCount φ (fun n => (partitionCount n : ℝ))
          (GapFamily.energy c p - 1 / 12) E =
      ∑' v : ℕ × ℕ, smoothTerm φ c s E (.inr (p, v)) := by
  unfold moduleSmoothCount
  rw [← tsum_mul_left]
  apply tsum_congr
  rintro ⟨n, m⟩
  simp only [smoothTerm, stateMultiplicity, stateEnergy_primary, moduleSmoothTerm, Nat.cast_mul]
  ring

/-- Every admissible kernel has fixed upper-support and supremum bounds. -/
theorem exists_kernel_upper_bound (φ : SmoothKernel) :
    ∃ R H : ℝ, 0 ≤ R ∧ 0 ≤ H ∧
      (∀ u, φ u ≠ 0 → u ≤ R) ∧ (∀ u, φ u ≤ H) := by
  obtain ⟨R, hR⟩ := φ.compactSupport.bddAbove
  obtain ⟨H, hH⟩ := (φ.compactSupport.isCompact_range φ.smooth.continuous).bddAbove
  refine ⟨max 0 R, max 0 H, le_max_left _ _, le_max_left _ _, ?_, ?_⟩
  · intro u hu
    exact (hR (subset_tsupport φ hu)).trans (le_max_right _ _)
  · intro u
    exact (hH (mem_range_self u)).trans (le_max_right _ _)

private theorem kernel_le_thermalTilt (φ : SmoothKernel) {β R H e E : ℝ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H) (hR : ∀ u, φ u ≠ 0 → u ≤ R)
    (hφ : ∀ u, φ u ≤ H) (n m : ℕ) :
    φ (e + n + m - E) ≤
      H * exp (β * (E + R - e)) * exp (-β * n) * exp (-β * m) := by
  rw [mul_assoc H, mul_assoc H, ← exp_add, ← exp_add]
  by_cases hz : φ (e + n + m - E) = 0
  · rw [hz]
    positivity
  have he := hR _ hz
  have harg : 0 ≤ β * (E + R - e) + -β * n + -β * m := by
    nlinarith [mul_nonneg hβ (show 0 ≤ E + R - e - n - m by linarith)]
  exact (hφ _).trans (le_mul_of_one_le_right hH (one_le_exp harg))

theorem moduleSmoothTerm_nonneg (φ : SmoothKernel) {d : ℕ → ℝ}
    (hd : ∀ n, 0 ≤ d n) (e E : ℝ) (v : ℕ × ℕ) :
    0 ≤ moduleSmoothTerm φ d e E v :=
  mul_nonneg (mul_nonneg (hd _) (hd _)) (φ.nonneg _)

theorem moduleSmoothCount_nonneg (φ : SmoothKernel) {d : ℕ → ℝ}
    (hd : ∀ n, 0 ≤ d n) (e E : ℝ) : 0 ≤ moduleSmoothCount φ d e E :=
  tsum_nonneg (moduleSmoothTerm_nonneg φ hd e E)

theorem initialPacketSmoothCount_nonneg {ι : Type*} [Fintype ι]
    (φ : SmoothKernel) (energy : ι → ℝ) (weight : ι → ℕ) (E : ℝ) :
    0 ≤ initialPacketSmoothCount φ energy weight E :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _)
    (moduleSmoothCount_nonneg φ (fun _ => Nat.cast_nonneg _) _ _)

theorem vacuumSmoothCount_nonneg (φ : SmoothKernel) (c E : ℝ) :
    0 ≤ vacuumSmoothCount φ c E :=
  moduleSmoothCount_nonneg φ (fun _ => Nat.cast_nonneg _) _ _

theorem moduleSmoothTerm_le_thermal (φ : SmoothKernel) {d : ℕ → ℝ}
    (hd : ∀ n, 0 ≤ d n) (hdp : ∀ n, d n ≤ partitionCount n)
    {β R H e E : ℝ} (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (hR : ∀ u, φ u ≠ 0 → u ≤ R) (hφ : ∀ u, φ u ≤ H) (v : ℕ × ℕ) :
    moduleSmoothTerm φ d e E v ≤ H * exp (β * (E + R - e)) *
      (partitionThermalTerm β v.1 * partitionThermalTerm β v.2) := by
  calc
    _ ≤ (partitionCount v.1 : ℝ) * partitionCount v.2 * φ (e + v.1 + v.2 - E) :=
      mul_le_mul_of_nonneg_right (mul_le_mul (hdp _) (hdp _) (hd _) (by positivity))
        (φ.nonneg _)
    _ ≤ (partitionCount v.1 : ℝ) * partitionCount v.2 *
        (H * exp (β * (E + R - e)) * exp (-β * v.1) * exp (-β * v.2)) :=
      mul_le_mul_of_nonneg_left (kernel_le_thermalTilt φ hβ hH hR hφ _ _) (by positivity)
    _ = _ := by unfold partitionThermalTerm; ring

/-- The ordinary sum converges by the same explicit thermal majorant. -/
theorem moduleSmoothTerm_summable_of_partition (φ : SmoothKernel) {d : ℕ → ℝ}
    (hd : ∀ n, 0 ≤ d n) (hdp : ∀ n, d n ≤ partitionCount n)
    {β R H e E : ℝ} (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (hR : ∀ u, φ u ≠ 0 → u ≤ R) (hφ : ∀ u, φ u ≤ H)
    (hs : Summable (partitionThermalTerm β)) :
    Summable (moduleSmoothTerm φ d e E) := by
  have hprod := hs.mul_of_nonneg hs (partitionThermalTerm_nonneg β)
    (partitionThermalTerm_nonneg β)
  exact (hprod.mul_left (H * exp (β * (E + R - e)))).of_nonneg_of_le
    (moduleSmoothTerm_nonneg φ hd e E)
    (moduleSmoothTerm_le_thermal φ hd hdp hβ hH hR hφ)

/-- A compact-kernel module count is bounded by the actual convergent
partition thermal function. No asymptotic partition formula is used. -/
theorem moduleSmoothCount_le_thermal (φ : SmoothKernel) {d : ℕ → ℝ}
    (hd : ∀ n, 0 ≤ d n) (hdp : ∀ n, d n ≤ partitionCount n)
    {β R H e E : ℝ} (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (hR : ∀ u, φ u ≠ 0 → u ≤ R) (hφ : ∀ u, φ u ≤ H)
    (hs : Summable (partitionThermalTerm β)) :
    moduleSmoothCount φ d e E ≤
      H * exp (β * (E + R - e)) * partitionThermal β ^ 2 := by
  have hprod := hs.mul_of_nonneg hs (partitionThermalTerm_nonneg β)
    (partitionThermalTerm_nonneg β)
  have hmajor := hprod.mul_left (H * exp (β * (E + R - e)))
  have hbound := moduleSmoothTerm_le_thermal φ hd hdp (e := e) (E := E) hβ hH hR hφ
  have hsum := hmajor.of_nonneg_of_le (moduleSmoothTerm_nonneg φ hd e E) hbound
  have h := hsum.tsum_le_tsum hbound hmajor
  simpa only [moduleSmoothCount, tsum_mul_left,
    ← hs.tsum_mul_tsum hs hprod, ← pow_two, partitionThermal] using h

/-- Total packet multiplicity is the only selector-dependent quantity in
this upper bound. Every primary descendant level and spin is included. -/
theorem initialPacketSmoothCount_le_thermal {ι : Type*} [Fintype ι]
    (φ : SmoothKernel) (energy : ι → ℝ) (weight : ι → ℕ)
    {β R H E : ℝ} (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (hR : ∀ u, φ u ≠ 0 → u ≤ R) (hφ : ∀ u, φ u ≤ H)
    (hs : Summable (partitionThermalTerm β)) (he : ∀ i, 0 ≤ energy i) :
    initialPacketSmoothCount φ energy weight E ≤
      (∑ i, (weight i : ℝ)) * H * exp (β * (E + R + 1 / 12)) * partitionThermal β ^ 2 := by
  unfold initialPacketSmoothCount
  calc
    _ ≤ ∑ i, (weight i : ℝ) *
        (H * exp (β * (E + R + 1 / 12)) * partitionThermal β ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply (moduleSmoothCount_le_thermal φ (fun _ => Nat.cast_nonneg _) (fun _ => le_rfl)
        hβ hH hR hφ hs).trans
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      apply mul_le_mul_of_nonneg_left _ hH
      apply exp_le_exp.mpr
      nlinarith [mul_nonneg hβ (he i)]
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- The vacuum is controlled by the same descendant product, while retaining
its physical cylinder ground energy `-c/12` and null-subtracted multiplicity. -/
theorem vacuumSmoothCount_le_thermal (φ : SmoothKernel) {β R H c E : ℝ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (hR : ∀ u, φ u ≠ 0 → u ≤ R) (hφ : ∀ u, φ u ≤ H)
    (hs : Summable (partitionThermalTerm β)) :
    vacuumSmoothCount φ c E ≤
      H * exp (β * (E + R + c / 12)) * partitionThermal β ^ 2 := by
  simpa only [vacuumSmoothCount, neg_div, sub_neg_eq_add] using
    moduleSmoothCount_le_thermal φ (fun _ => Nat.cast_nonneg _)
      (fun n => Nat.cast_le.mpr (vacuumPartitionCount_le n)) (e := -c / 12) (E := E)
      hβ hH hR hφ hs

end BTZEntropy.Comparison
