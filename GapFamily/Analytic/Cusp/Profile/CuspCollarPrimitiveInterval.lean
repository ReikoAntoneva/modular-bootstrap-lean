import GapFamily.Analytic.Cusp.Profile.CuspCollarPrimitive

/-!
# Real-coordinate evaluation of collar primitives

The measured-collar primitive agrees with ordinary interval integration.
The real-coordinate representative of a continuous collar value needs no
regularity outside that collar.
-/

noncomputable section

namespace GapFamily.Analytic

open Set MeasureTheory

/-- A collar slice is the literal real interval cut off at the source endpoint. -/
theorem cuspCollarPrimitiveSlice_integral (T t : ℝ) (f : ℝ → ℂ) :
    (∫ u : CuspGreenCollar 0 T in {u | (u : ℝ) ≤ t},
      f u ∂cuspGreenCollarMeasure 0 T) =
      ∫ u : ℝ in Icc 0 (min T t), f u := by
  rw [← integral_indicator (measurableSet_cuspCollarPrimitiveSlice T t)]
  change (∫ u : CuspGreenCollar 0 T, (Iic t).indicator f u
    ∂volume.comap (Subtype.val : CuspGreenCollar 0 T → ℝ)) = _
  rw [integral_subtype_comap measurableSet_Icc, setIntegral_indicator measurableSet_Iic]
  have hset : Icc (0 : ℝ) T ∩ Iic t = Icc 0 (min T t) := by
    ext u
    simp only [mem_inter_iff, mem_Icc, mem_Iic, le_min_iff, and_assoc]
  rw [hset]

/-- Evaluation on a continuous collar value uses any matching real-coordinate
representative, without a regularity assumption outside the source collar. -/
theorem cuspCollarPrimitive_apply_toLp (L T : ℝ)
    (c : C(CuspGreenCollar 0 T, ℂ)) (v : ℝ → ℂ)
    (hc : ∀ u : CuspGreenCollar 0 T, c u = v u) (t : CuspGreenCollar 0 L) :
    cuspCollarPrimitive L T
      (ContinuousMap.toLp 2 (cuspGreenCollarMeasure 0 T) ℂ c) t =
      ∫ u : ℝ in Icc 0 (min T (t : ℝ)), v u := by
  rw [cuspCollarPrimitive_apply]
  refine (integral_congr_ae ?_).trans (cuspCollarPrimitiveSlice_integral T t v)
  filter_upwards [ae_restrict_of_ae
    (ContinuousMap.coeFn_toLp (p := 2) (μ := cuspGreenCollarMeasure 0 T) (𝕜 := ℂ) c)]
    with u hu
  exact hu.trans (hc u)

/-- Matching a continuous collar value suffices for ordinary interval
integrability, regardless of the representative outside that collar. -/
theorem cuspCollarRepresentative_intervalIntegrable (L : ℝ)
    (c : C(CuspGreenCollar 0 L, ℂ)) (v : ℝ → ℂ)
    (hc : ∀ u : CuspGreenCollar 0 L, c u = v u) (t : CuspGreenCollar 0 L) :
    IntervalIntegrable v volume 0 (t : ℝ) := by
  have hv : ContinuousOn v (Icc 0 L) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have heq : (Icc 0 L).domRestrict v = c := funext fun u => (hc u).symm
    rw [heq]
    exact c.continuous
  exact ContinuousOn.intervalIntegrable_of_Icc t.property.1
    (hv.mono (Icc_subset_Icc le_rfl t.property.2))

/-- On the same collar, the bounded primitive is the ordinary interval integral. -/
theorem cuspCollarPrimitive_toLp_eq_intervalIntegral (L : ℝ)
    (c : C(CuspGreenCollar 0 L, ℂ)) (v : ℝ → ℂ)
    (hc : ∀ u : CuspGreenCollar 0 L, c u = v u) (t : CuspGreenCollar 0 L) :
    cuspCollarPrimitive L L
      (ContinuousMap.toLp 2 (cuspGreenCollarMeasure 0 L) ℂ c) t =
      ∫ u in (0 : ℝ)..(t : ℝ), v u := by
  rw [cuspCollarPrimitive_apply_toLp L L c v hc t, min_eq_right t.property.2,
    intervalIntegral.integral_of_le t.property.1, integral_Icc_eq_integral_Ioc]

/-- Evaluation on an ordinary continuous source retains its literal real
coordinate and truncates only at the source collar endpoint. -/
theorem cuspCollarPrimitive_apply_source (L T : ℝ) (f : ℝ → ℂ) (hf : Continuous f)
    (t : CuspGreenCollar 0 L) :
    cuspCollarPrimitive L T (cuspGreenCollarSource 0 T f hf) t =
      ∫ u : ℝ in Icc 0 (min T (t : ℝ)), f u :=
  cuspCollarPrimitive_apply_toLp L T
    ⟨fun u : CuspGreenCollar 0 T => f u, hf.comp continuous_subtype_val⟩
    f (fun _ => rfl) t

/-- A source vanishing beyond its collar has the ordinary primitive at every
observation point, including points beyond the source endpoint. -/
theorem cuspCollarPrimitive_source_eq_intervalIntegral (L T : ℝ)
    (f : ℝ → ℂ) (hf : Continuous f) (hfT : ∀ u : ℝ, T < u → f u = 0)
    (t : CuspGreenCollar 0 L) :
    cuspCollarPrimitive L T (cuspGreenCollarSource 0 T f hf) t =
      ∫ u in (0 : ℝ)..(t : ℝ), f u := by
  rw [cuspCollarPrimitive_apply_source,
    intervalIntegral.integral_of_le t.property.1, ← integral_Icc_eq_integral_Ioc]
  symm
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Icc
    (Icc_subset_Icc le_rfl (min_le_right _ _))
  intro u hu
  apply hfT u
  by_contra h
  exact hu.2 ⟨hu.1.1, le_min (le_of_not_gt h) hu.1.2⟩

end GapFamily.Analytic
