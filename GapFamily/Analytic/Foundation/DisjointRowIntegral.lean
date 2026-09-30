import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Nonnegative integrals over disjoint cells can be summed across measure rows.
The cell index is arbitrary: finite subsums suffice, so no countability
assumption on that index is needed.
-/

open MeasureTheory Set
open scoped BigOperators

namespace GapFamily.Analytic

/-- Any finite family of cells disjoint within each row is bounded by the
sum of the full row integrals. -/
theorem sum_integral_disjoint_rows_le {ι : Type*}
    (J : ι → ℤ) (s : ι → Set ℝ) (μ : ℤ → Measure ℝ) (f : ℤ → ℝ → ℝ)
    (hs : ∀ i, MeasurableSet (s i))
    (hdis : ∀ i k, i ≠ k → J i = J k → Disjoint (s i) (s k))
    (hf : ∀ j, Integrable (f j) (μ j))
    (hnonneg : ∀ j, 0 ≤ᵐ[μ j] f j)
    (hsum : Summable (fun j => ∫ x, f j x ∂μ j)) (T : Finset ι) :
    ∑ i ∈ T, ∫ x in s i, f (J i) x ∂μ (J i) ≤
      ∑' j, ∫ x, f j x ∂μ j := by
  classical
  have hfiber (j : ℤ) :
      ∑ i ∈ T with J i = j, ∫ x in s i, f j x ∂μ j ≤
        ∫ x, f j x ∂μ j := by
    rw [← integral_biUnion_finset (T.filter (fun i => J i = j))
      (fun i _ => hs i) (by
        intro i hi k hk hik
        exact hdis i k hik
          ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hk).2.symm))
      (fun i _ => (hf j).restrict)]
    exact setIntegral_le_integral (hf j) (hnonneg j)
  calc
    (∑ i ∈ T, ∫ x in s i, f (J i) x ∂μ (J i)) =
        ∑ j ∈ T.image J, ∑ i ∈ T with J i = j,
          ∫ x in s i, f (J i) x ∂μ (J i) :=
      (Finset.sum_fiberwise_of_maps_to
        (fun i hi => Finset.mem_image_of_mem J hi)
        (fun i => ∫ x in s i, f (J i) x ∂μ (J i))).symm
    _ = ∑ j ∈ T.image J, ∑ i ∈ T with J i = j,
          ∫ x in s i, f j x ∂μ j := by
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i hi => ?_
      rw [(Finset.mem_filter.mp hi).2]
    _ ≤ ∑ j ∈ T.image J, ∫ x, f j x ∂μ j :=
      Finset.sum_le_sum (fun j _ => hfiber j)
    _ ≤ ∑' j, ∫ x, f j x ∂μ j :=
      hsum.sum_le_tsum (T.image J) (fun j _ => integral_nonneg_of_ae (hnonneg j))

/-- A summable family of nonnegative row integrals controls all disjoint cell
integrals, even when the cells have an arbitrary index type. -/
theorem summable_integral_disjoint_rows {ι : Type*}
    (J : ι → ℤ) (s : ι → Set ℝ) (μ : ℤ → Measure ℝ) (f : ℤ → ℝ → ℝ)
    (hs : ∀ i, MeasurableSet (s i))
    (hdis : ∀ i k, i ≠ k → J i = J k → Disjoint (s i) (s k))
    (hf : ∀ j, Integrable (f j) (μ j))
    (hnonneg : ∀ j, 0 ≤ᵐ[μ j] f j)
    (hsum : Summable (fun j => ∫ x, f j x ∂μ j)) :
    Summable (fun i => ∫ x in s i, f (J i) x ∂μ (J i)) := by
  exact summable_of_sum_le
    (fun i => setIntegral_nonneg_of_ae (hnonneg (J i)))
    (sum_integral_disjoint_rows_le J s μ f hs hdis hf hnonneg hsum)

/-- Summing over disjoint cells never exceeds the sum of the full row
integrals. -/
theorem tsum_integral_disjoint_rows_le {ι : Type*}
    (J : ι → ℤ) (s : ι → Set ℝ) (μ : ℤ → Measure ℝ) (f : ℤ → ℝ → ℝ)
    (hs : ∀ i, MeasurableSet (s i))
    (hdis : ∀ i k, i ≠ k → J i = J k → Disjoint (s i) (s k))
    (hf : ∀ j, Integrable (f j) (μ j))
    (hnonneg : ∀ j, 0 ≤ᵐ[μ j] f j)
    (hsum : Summable (fun j => ∫ x, f j x ∂μ j)) :
    (∑' i, ∫ x in s i, f (J i) x ∂μ (J i)) ≤
      ∑' j, ∫ x, f j x ∂μ j := by
  exact Real.tsum_le_of_sum_le
    (fun i => setIntegral_nonneg_of_ae (hnonneg (J i)))
    (sum_integral_disjoint_rows_le J s μ f hs hdis hf hnonneg hsum)

end GapFamily.Analytic
