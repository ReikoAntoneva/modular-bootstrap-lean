import GapFamily.Analytic.Cusp.Green.CuspGreenSourceEmbedding
import GapFamily.Analytic.Cusp.Profile.CuspProfileFormLimit
import GapFamily.Analytic.Modular.Geometry.ModularTruncatedTransportWeight
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Topology.Sequences

noncomputable section
namespace GapFamily.Analytic
open Set Filter MeasureTheory ModularGradient
open scoped Topology ContDiff

/-- Null exceptional sets in logarithmic collar coordinates remain null in height. -/
theorem cuspGreenCollar_ae_log_height {T : ℝ} {P : ℝ → Prop}
    (hP : ∀ᵐ t ∂volume.restrict (Icc 0 T), P t) :
    ∀ᵐ y ∂(volume : Measure ℝ), y ∈ Icc 1 (Real.exp T) → P (Real.log y) := by
  have hmap := map_withDensity_abs_det_fderiv_eq_addHaar (volume : Measure ℝ)
    (s := Icc (0 : ℝ) T) measurableSet_Icc.nullMeasurableSet
    (fun t _ => (Real.hasDerivAt_exp t).hasFDerivAt.hasFDerivWithinAt)
    Real.exp_injective.injOn
  have hh : ∀ᵐ y ∂volume.restrict (Icc 1 (Real.exp T)), P (Real.log y) := by
    rw [← Real.exp_zero, ← Real.image_exp_Icc, ← hmap]
    apply (Real.continuous_exp.measurableEmbedding Real.exp_injective).ae_map_iff.mpr
    apply (withDensity_absolutelyContinuous _ _).ae_le
    filter_upwards [hP] with t ht
    simpa only [Real.log_exp] using ht
  exact (ae_restrict_iff' measurableSet_Icc).mp hh

/-- Logarithmic collar exceptional sets remain null for the actual modular measure. -/
theorem cuspGreenCollar_ae_log_modular {T : ℝ} {P : ℝ → Prop}
    (hP : ∀ᵐ t ∂volume.restrict (Icc 0 T), P t) :
    ∀ᵐ τ : UpperHalfPlane ∂modularMeasure,
      1 < τ.im ∧ τ.im ≤ Real.exp T → P (Real.log τ.im) := by
  have hy := cuspGreenCollar_ae_log_height hP
  have hxy := (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ))
    (ν := (volume : Measure ℝ))).ae hy
  have hz := Complex.volume_preserving_equiv_real_prod.quasiMeasurePreserving.ae hxy
  have hm := modularCoordinateMeasure_absolutelyContinuous_volume.ae_le hz
  have hu := (ae_modularCoordinate_iff
    (fun z : ℂ => z.im ∈ Icc 1 (Real.exp T) → P (Real.log z.im))).mp hm
  filter_upwards [hu] with τ hτ hbound
  exact hτ ⟨hbound.1.le, hbound.2⟩

/-- The extension has its literal truncated lift for every continuous collar source. -/
theorem cuspGreenSourceEmbedding_continuous_ae (T : ℝ) (_hT : 0 ≤ T)
    (ψ : ℝ → ℂ) (hψ : Continuous ψ) :
    cuspGreenSourceEmbedding T (cuspGreenCollarSource 0 T ψ hψ) =ᵐ[modularMeasure]
      (fun τ : UpperHalfPlane => if 1 < τ.im ∧ τ.im ≤ Real.exp T then
        cuspLift ψ τ.im else 0) := by
  let f := cuspGreenCollarSource 0 T ψ hψ
  obtain ⟨fs, hmem, hfs⟩ := mem_closure_iff_seq_limit.mp
    (cuspGreenSourceRestriction_denseRange T f)
  choose gs hgs using hmem
  have hgs_limit : Tendsto (fun n => cuspGreenSourceRestriction T (gs n)) atTop (𝓝 f) := by
    simpa only [hgs] using hfs
  obtain ⟨ns, hns, hae⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hgs_limit).exists_seq_tendsto_ae
  have hpoint : ∀ᵐ t : CuspGreenCollar 0 T ∂cuspGreenCollarMeasure 0 T,
      Tendsto (fun n => (gs (ns n) : ℝ → ℂ) t) atTop (𝓝 (ψ t)) := by
    filter_upwards [hae,
      ae_all_iff.mpr (fun n => cuspGreenSourceRestriction_coeFn T (gs n)),
      cuspGreenCollarSource_coeFn 0 T ψ hψ] with t ht heq hf
    simpa only [heq, f, hf] using ht
  have hreal : ∀ᵐ t ∂volume.restrict (Icc 0 T),
      Tendsto (fun n => (gs (ns n) : ℝ → ℂ) t) atTop (𝓝 (ψ t)) :=
    (ae_restrict_iff_subtype measurableSet_Icc).mpr hpoint
  have hmod := cuspGreenCollar_ae_log_modular hreal
  have hlim : Tendsto
      (fun n => cuspGreenSourceEmbedding T (cuspGreenSourceRestriction T (gs (ns n))))
      atTop (𝓝 (cuspGreenSourceEmbedding T f)) :=
    ((cuspGreenSourceEmbedding T).continuous.tendsto f).comp
      (hgs_limit.comp hns.tendsto_atTop)
  obtain ⟨ks, hks, hkae⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  have hemb (n : ℕ) :
      cuspGreenSourceEmbedding T (cuspGreenSourceRestriction T (gs n)) =ᵐ[modularMeasure]
        (fun τ : UpperHalfPlane => if 1 < τ.im then
          cuspLift (gs n : ℝ → ℂ) τ.im else 0) :=
    cuspGreenSourceEmbedding_smooth_ae T (gs n) (gs n).property.1
      (gs n).property.2.1 (gs n).property.2.2
  filter_upwards [hkae, ae_all_iff.mpr hemb, hmod] with τ hk heq hp
  have hk' : Tendsto (fun n => if 1 < τ.im then
      cuspLift (gs (ns (ks n)) : ℝ → ℂ) τ.im else 0) atTop
      (𝓝 (cuspGreenSourceEmbedding T f τ)) := by
    simpa only [heq] using hk
  apply tendsto_nhds_unique hk'
  by_cases hy : 1 < τ.im
  · simp only [ite_eq_left hy]
    by_cases hT : τ.im ≤ Real.exp T
    · simp only [hy, hT, and_self, ite_true, cuspLift]
      exact ((hp ⟨hy, hT⟩).comp hks.tendsto_atTop).const_smul (Real.sqrt τ.im)
    · simp only [hT, and_false, ite_false]
      have hlog : T < Real.log τ.im :=
        (Real.lt_log_iff_exp_lt τ.im_pos).mpr (lt_of_not_ge hT)
      have hzero (n : ℕ) : (gs n : ℝ → ℂ) (Real.log τ.im) = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro ht
        have := ((gs n).property.2.2 ht).2
        exact (not_lt_of_ge hlog.le) this
      simpa only [cuspLift, hzero, smul_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
  · simpa only [ite_eq_right hy, hy, false_and, ite_false] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))

end GapFamily.Analytic
