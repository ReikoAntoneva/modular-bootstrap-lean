import BTZEntropy.Comparison.InitialPacketSubexponential
import BTZEntropy.Comparison.SpectrumTestObservable

/-!
# Uniform descendant tests for density errors

The finite descendant packet may grow with the charge or contain all levels
that can contribute to the compact kernel. Its bound is independent of that
packet: the convergent, complete descendant thermal series dominates it.
-/

noncomputable section

open Real

namespace BTZEntropy.Comparison

theorem continuous_primaryDescendantTest (φ : SmoothKernel) (E : ℝ)
    (F : Finset (ℕ × ℕ)) : Continuous (primaryDescendantTest φ E F) := by
  unfold primaryDescendantTest
  apply continuous_finsetSum
  intro l hl
  exact (φ.smooth.continuous.comp (by fun_prop)).const_mul _

/-- Every finite descendant test is bounded by the same complete module. -/
theorem primaryDescendantTest_le_module (φ : SmoothKernel) (e E : ℝ)
    (F : Finset (ℕ × ℕ)) :
    primaryDescendantTest φ E F e ≤
      moduleSmoothCount φ (fun n => (partitionCount n : ℝ)) (e - 1 / 12) E := by
  obtain ⟨R, H, hR0, hH, hR, hφ⟩ := exists_kernel_upper_bound φ
  have hs := moduleSmoothTerm_summable_of_partition φ
    (fun n => Nat.cast_nonneg (partitionCount n)) (fun _ => le_rfl)
    (β := 1) (e := e - 1 / 12) (E := E) (by norm_num) hH hR hφ
    (summable_partitionThermalTerm (by norm_num))
  exact hs.sum_le_tsum F
    (fun l _ => moduleSmoothTerm_nonneg φ (fun n => Nat.cast_nonneg (partitionCount n)) _ _ l)

/-- At extensive energy, every nonnegative reduced primary ground energy and
every finite descendant packet share a root-exponential upper bound. -/
theorem primaryDescendantTest_le_sqrt (φ : SmoothKernel) (F : Finset (ℕ × ℕ))
    {e c x U R H : ℝ} (he : 0 ≤ e) (hc : 1 ≤ c) (hx : x ≤ U)
    (hR0 : 0 ≤ R) (hH : 0 ≤ H)
    (hR : ∀ u, φ u ≠ 0 → u ≤ R) (hφ : ∀ u, φ u ≤ H) :
    primaryDescendantTest φ (x * c) F e ≤
      H * exp ((U + R + 1 / 12 + 4) * sqrt c) :=
  (primaryDescendantTest_le_module φ e (x * c) F).trans
    (primaryModuleSmoothCount_le_sqrt φ he hc hx hR0 hH hR hφ)

end BTZEntropy.Comparison
