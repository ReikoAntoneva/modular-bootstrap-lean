import GapFamily.Analytic.Cusp.Scalar.CuspScalarUpperCore
import GapFamily.Analytic.Cusp.Green.CuspGreenCollarOutput

/-! Ordinary upper-plane lifting of actual collar sources by density, including all side seams. -/
noncomputable section
namespace GapFamily.Analytic.CuspScalarUpperLift
open Set Filter MeasureTheory ModularGradient CuspScalarUpperCore
open scoped Topology ContDiff

/-- Logarithmic collar null sets pull back to null sets for ordinary area on the full plane. -/
theorem collar_ae_log_upper {T : ℝ} {P : ℝ → Prop}
    (hP : ∀ᵐ t ∂volume.restrict (Icc 0 T), P t) :
    ∀ᵐ z : ℂ ∂volume, z.im ∈ Icc 1 (Real.exp T) → P (Real.log z.im) := by
  have hy := cuspGreenCollar_ae_log_height hP
  have hxy := (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ))
    (ν := (volume : Measure ℝ))).ae hy
  exact Complex.volume_preserving_equiv_real_prod.quasiMeasurePreserving.ae hxy

/-- Smooth source density and actual L² limits identify the upper Hilbert lift
of every continuous collar source at all high points, with ordinary-area AE scope. -/
theorem upperCutoff_sourceEmbedding_continuous_ae_high
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ UpperHalfPlane.upperHalfPlaneSet)
    (T : ℝ) (ψ : ℝ → ℂ) (hψ : Continuous ψ) :
    ∀ᵐ z : ℂ ∂volume, 1 < z.im →
      upperCutoffHilbertValueOperator χ hχ hc hs
        (cuspGreenSourceEmbedding T (cuspGreenCollarSource 0 T ψ hψ)) z =
          χ z * (if z.im ≤ Real.exp T then Real.sqrt z.im • ψ (Real.log z.im) else 0) := by
  let f := cuspGreenCollarSource 0 T ψ hψ
  obtain ⟨fs, hmem, hfs⟩ := mem_closure_iff_seq_limit.mp
    (cuspGreenSourceRestriction_denseRange T f)
  choose gs hgs using hmem
  have hgs_limit : Tendsto (fun n => cuspGreenSourceRestriction T (gs n)) atTop (𝓝 f) := by
    simpa only [hgs] using hfs
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hgs_limit).exists_seq_tendsto_ae
  have hpoint : ∀ᵐ t : CuspGreenCollar 0 T ∂cuspGreenCollarMeasure 0 T,
      Tendsto (fun n => (gs (ns n) : ℝ → ℂ) t) atTop (𝓝 (ψ t)) := by
    filter_upwards [hae, ae_all_iff.mpr (fun n => cuspGreenSourceRestriction_coeFn T (gs n)),
      cuspGreenCollarSource_coeFn 0 T ψ hψ] with t ht heq hf
    simpa only [heq, f, hf] using ht
  have hreal : ∀ᵐ t ∂volume.restrict (Icc 0 T),
      Tendsto (fun n => (gs (ns n) : ℝ → ℂ) t) atTop (𝓝 (ψ t)) :=
    (ae_restrict_iff_subtype measurableSet_Icc).mpr hpoint
  have hupper := collar_ae_log_upper hreal
  let B : Lp ℂ 2 (cuspGreenCollarMeasure 0 T) →L[ℂ] Lp ℂ 2 (volume : Measure ℂ) :=
    (upperCutoffHilbertValueOperator χ hχ hc hs).comp (cuspGreenSourceEmbedding T).toContinuousLinearMap
  have hlim : Tendsto (fun n => B (cuspGreenSourceRestriction T (gs (ns n))))
      atTop (𝓝 (B f)) := (B.continuous.tendsto f).comp (hgs_limit.comp hns.tendsto_atTop)
  obtain ⟨ks, hks, hkae⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  have hemb (n : ℕ) : ∀ᵐ z : ℂ ∂volume, 1 < z.im →
      B (cuspGreenSourceRestriction T (gs n)) z =
        χ z * (Real.sqrt z.im • (gs n : ℝ → ℂ) (Real.log z.im)) := by
    change ∀ᵐ z : ℂ ∂volume, 1 < z.im →
      upperCutoffHilbertValueOperator χ hχ hc hs
        (cuspGreenSourceEmbedding T
          (cuspGreenCollarSource 0 T (gs n) (gs n).property.1.continuous)) z = _
    rw [cuspGreenSourceEmbedding_smooth T (gs n) (gs n).property.1
      (gs n).property.2.1 (gs n).property.2.2]
    exact upperCutoff_sourceLift_ae_high χ hχ hc hs (gs n) (gs n).property.1
      (gs n).property.2.1 ((gs n).property.2.2.trans Ioo_subset_Ioi_self)
  filter_upwards [hkae, ae_all_iff.mpr hemb, hupper] with z hk heq hp
  intro hy
  have hk' : Tendsto (fun n => χ z * (Real.sqrt z.im • (gs (ns (ks n)) : ℝ → ℂ) (Real.log z.im)))
      atTop (𝓝 (B f z)) := by
    simpa only [fun n => heq n hy] using hk
  change B f z = _
  apply tendsto_nhds_unique hk'
  by_cases hcap : z.im ≤ Real.exp T
  · simp only [hcap, ite_true]
    exact (((hp ⟨hy.le, hcap⟩).comp hks.tendsto_atTop).const_smul (Real.sqrt z.im)).const_mul (χ z)
  · simp only [hcap, ite_false, mul_zero]
    have hlog : T < Real.log z.im :=
      (Real.lt_log_iff_exp_lt (by linarith : 0 < z.im)).mpr (lt_of_not_ge hcap)
    have hzero (n : ℕ) : (gs n : ℝ → ℂ) (Real.log z.im) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro ht
      exact (not_lt_of_ge hlog.le) (((gs n).property.2.2 ht).2)
    simpa only [hzero, smul_zero, mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))

/-- The same upper-plane identity for an actual continuous collar value, with
no regularity imposed on the matching real-coordinate function outside the collar. -/
theorem upperCutoff_sourceEmbedding_toLp_ae_high
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ UpperHalfPlane.upperHalfPlaneSet)
    (L : ℝ) (hL : 0 ≤ L) (c : C(CuspGreenCollar 0 L, ℂ)) (v : ℝ → ℂ)
    (hv : ∀ t : CuspGreenCollar 0 L, c t = v t) :
    ∀ᵐ z : ℂ ∂volume, 1 < z.im →
      upperCutoffHilbertValueOperator χ hχ hc hs
        (cuspGreenSourceEmbedding L (ContinuousMap.toLp 2 (cuspGreenCollarMeasure 0 L) ℂ c)) z =
          χ z * (if z.im ≤ Real.exp L then Real.sqrt z.im • v (Real.log z.im) else 0) := by
  let ψ : ℝ → ℂ := fun t => c (Set.projIcc 0 L hL t)
  have hψ : Continuous ψ := c.continuous.comp continuous_projIcc
  have hsource : cuspGreenCollarSource 0 L ψ hψ =
      ContinuousMap.toLp 2 (cuspGreenCollarMeasure 0 L) ℂ c := by
    unfold cuspGreenCollarSource
    congr 1
    ext t
    change c (Set.projIcc 0 L hL t) = c t
    rw [Set.projIcc_val]
  have hrep := upperCutoff_sourceEmbedding_continuous_ae_high χ hχ hc hs L ψ hψ
  rw [hsource] at hrep
  filter_upwards [hrep] with z hz
  intro hy
  rw [hz hy]
  by_cases hcap : z.im ≤ Real.exp L
  · simp only [hcap, ite_true]
    have hlog : Real.log z.im ∈ Icc 0 L :=
      ⟨(Real.log_pos hy).le, (Real.log_le_iff_le_exp (by linarith : 0 < z.im)).mpr hcap⟩
    change χ z * (Real.sqrt z.im • c (Set.projIcc 0 L hL (Real.log z.im))) = _
    rw [Set.projIcc_of_mem hL hlog]
    exact congrArg (fun w : ℂ => χ z * (Real.sqrt z.im • w)) (hv ⟨Real.log z.im, hlog⟩)
  · simp only [hcap, ite_false]

end GapFamily.Analytic.CuspScalarUpperLift
