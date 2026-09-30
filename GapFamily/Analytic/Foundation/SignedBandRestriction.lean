import Mathlib.MeasureTheory.VectorMeasure.Operations
import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-! An ordinary signed-measure identity on an open band extends to the
complete lower interval when the lower tail and the edge atom agree.
-/

namespace GapFamily.Analytic

open MeasureTheory Set

/-- Restriction to a set carrying the actual variation preserves the signed measure. -/
theorem signedMeasure_restrict_eq_self_of_ae_mem (ν : SignedMeasure ℝ)
    (s : Set ℝ) (hs : MeasurableSet s) (hν : ∀ᵐ E ∂ν.variation, E ∈ s) :
    ν.restrict s = ν := by
  have hzero : ν.variation sᶜ = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    exact hν.mono fun _ hE hEc => hEc hE
  have hrestrict : ν.restrict sᶜ = 0 := by
    apply VectorMeasure.variation_eq_zero.mp
    rw [VectorMeasure.variation_restrict hs.compl, Measure.restrict_eq_zero]
    exact hzero
  simpa only [hrestrict, add_zero] using
    (VectorMeasure.restrict_add_restrict_compl (v := ν) hs)

/-- The lower closed restriction consists of the lower open tail and its
actual edge atom. -/
theorem signedMeasure_restrict_Iic_eq (α : SignedMeasure ℝ) (a : ℝ) :
    α.restrict (Iic a) = α.restrict (Iio a) + VectorMeasure.dirac a (α {a}) := by
  have hset : Iic a = Iio a ∪ {a} := by
    ext x
    simp only [mem_Iic, mem_union, mem_Iio, mem_singleton_iff, le_iff_lt_or_eq]
  have hd : Disjoint (Iio a) ({a} : Set ℝ) := by
    simp
  rw [hset, VectorMeasure.restrict_union hd measurableSet_Iio (measurableSet_singleton a),
    VectorMeasure.restrict_singleton]

/-- Agreement below the edge, at the edge atom, and on the open band implies
agreement below the upper cutoff. No ordering assumption on the cutoffs is needed. -/
theorem signedMeasure_restrict_Iio_eq_of_band
    (α β : SignedMeasure ℝ) (a B : ℝ)
    (hbelow : α.restrict (Iio a) = β.restrict (Iio a))
    (hband : α.restrict (Ioo a B) = β.restrict (Ioo a B))
    (hatom : α {a} = β {a}) :
    α.restrict (Iio B) = β.restrict (Iio B) := by
  by_cases hab : a < B
  · have hd : Disjoint (Iic a) (Ioo a B) := by
      refine disjoint_left.mpr ?_
      intro x hx hy
      exact (not_lt_of_ge hx) hy.1
    have hclosed : α.restrict (Iic a) = β.restrict (Iic a) := by
      rw [signedMeasure_restrict_Iic_eq, signedMeasure_restrict_Iic_eq, hbelow, hatom]
    rw [← Iic_union_Ioo_eq_Iio hab,
      VectorMeasure.restrict_union hd measurableSet_Iic measurableSet_Ioo,
      VectorMeasure.restrict_union hd measurableSet_Iic measurableSet_Ioo,
      hclosed, hband]
  · have hinter : Iio B ∩ Iio a = Iio B :=
      inter_eq_left.mpr (Iio_subset_Iio (le_of_not_gt hab))
    have h := congrArg (fun ν : SignedMeasure ℝ => ν.restrict (Iio B)) hbelow
    simpa only [VectorMeasure.restrict_restrict _ measurableSet_Iio measurableSet_Iio,
      hinter] using h

/-- A measure supported above the physical edge is determined below a cutoff
by its ordinary open-band restriction and the preserved physical-edge atom. -/
theorem signedMeasure_restrict_Iio_eq_of_physical_band
    (α β : SignedMeasure ℝ) (a B : ℝ)
    (hα : α.restrict (Iio a) = 0)
    (hβ : β.restrict (Iio a) = 0)
    (hband : α.restrict (Ioo a B) = β.restrict (Ioo a B))
    (hatom : α {a} = β {a}) :
    α.restrict (Iio B) = β.restrict (Iio B) :=
  signedMeasure_restrict_Iio_eq_of_band α β a B (hα.trans hβ.symm) hband hatom

end GapFamily.Analytic
