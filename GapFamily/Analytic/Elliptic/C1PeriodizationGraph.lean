import GapFamily.Analytic.Elliptic.C1PeriodizationGraphBound
import GapFamily.Analytic.Elliptic.C1PeriodizationGraphLimit
import GapFamily.Analytic.Elliptic.C1PeriodizationGraphLp
import GapFamily.Analytic.Elliptic.CompactC1UpperApproximation
import GapFamily.Analytic.Modular.Elliptic.ModularInteriorCompactCore

noncomputable section
namespace GapFamily.Analytic.C1Periodization
open Set Filter MeasureTheory UpperHalfPlane ModularGradient
open scoped ContDiff MatrixGroups Topology

private lemma compactSupport_of_subset_compact {ψ : ℂ → ℂ} {K : Set ℂ}
    (hK : IsCompact K) (hs : tsupport ψ ⊆ K) : HasCompactSupport ψ :=
  hK.of_isClosed_subset (isClosed_tsupport ψ) hs

private lemma continuous_periodization_value {ψ : ℂ → ℂ}
    (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ upperHalfPlaneSet) :
    Continuous (fun τ : UpperHalfPlane => modularPeriodization ψ τ) :=
  (contDiffOn_periodization hψ hc hs).continuousOn.comp_continuous UpperHalfPlane.continuous_coe
    (fun τ => τ.im_pos)

private lemma continuous_periodization_directional {ψ : ℂ → ℂ}
    (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ upperHalfPlaneSet)
    (v : ℂ) : Continuous (directional (modularPeriodization ψ) v) := by
  have hD := (contDiffOn_periodization hψ hc hs).continuousOn_fderiv_of_isOpen
    isOpen_upperHalfPlaneSet (by simp)
  have hDc : Continuous (fun τ : UpperHalfPlane => fderiv ℝ (modularPeriodization ψ) τ) :=
    hD.comp_continuous UpperHalfPlane.continuous_coe (fun τ => τ.im_pos)
  exact (Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im).mul
    (hDc.clm_apply continuous_const)

/-- Common compact support and actual C¹ approximation place the periodized limit
in the genuine closed-gradient graph. The witnesses are its literal derivatives. -/
theorem exists_form_periodization_of_approximation
    (ψ : ℂ → ℂ) (hψ : ContDiff ℝ 1 ψ)
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ upperHalfPlaneSet)
    (hψK : tsupport ψ ⊆ K) (C : ℝ) (hC : 0 ≤ C)
    (ψn : ℕ → ℂ → ℂ) (hψn : ∀ n, ContDiff ℝ ∞ (ψn n) ∧ tsupport (ψn n) ⊆ K)
    (hlim : ∀ z, Tendsto (fun n => ψn n z) atTop (𝓝 (ψ z)))
    (hdlim : ∀ z, Tendsto (fun n => fderiv ℝ (ψn n) z) atTop (𝓝 (fderiv ℝ ψ z)))
    (hbound : ∀ n z, ‖ψn n z‖ ≤ C ∧ ‖fderiv ℝ (ψn n) z‖ ≤ C) :
    ∃ u : FormDomain,
      formEmbedding u =ᵐ[modularMeasure] (fun τ : UpperHalfPlane => modularPeriodization ψ τ) ∧
      (WithLp.ofLp (formGradient u)).1 =ᵐ[modularMeasure] directional (modularPeriodization ψ) 1 ∧
      (WithLp.ofLp (formGradient u)).2 =ᵐ[modularMeasure] directional (modularPeriodization ψ) Complex.I := by
  obtain ⟨χ, hχ, hcχ, hsχ, hone⟩ := exists_upperCutoff_eq_one hK hKU
  obtain ⟨H, hH, hKH⟩ := hK.isBounded.exists_pos_norm_le
  have hheight : ∀ z ∈ K, z.im ≤ H := fun z hz =>
    (le_abs_self _).trans ((Complex.abs_im_le_norm z).trans (hKH z hz))
  have hcψ := compactSupport_of_subset_compact hK hψK
  have hsψ := hψK.trans hKU
  have htarget (z : ℂ) : ‖ψ z‖ ≤ C ∧ ‖fderiv ℝ ψ z‖ ≤ C :=
    ⟨le_of_tendsto (hlim z).norm (Filter.Eventually.of_forall fun n => (hbound n z).1),
      le_of_tendsto (hdlim z).norm (Filter.Eventually.of_forall fun n => (hbound n z).2)⟩
  let B : UpperHalfPlane → ℝ := fun τ => (modularPeriodization (normSquareSeed χ) τ).re
  have hB : MemLp B 2 modularMeasure :=
    (modularPeriodization_mem_smoothCore_of_upper_support
      (normSquareSeed_contDiff hχ) (hasCompactSupport_normSquareSeed hcχ)
      (by simpa only [tsupport_normSquareSeed] using hsχ)).2.2.1.re
  have hvbound : ∀ τ : UpperHalfPlane, ‖modularPeriodization ψ τ‖ ≤ C * B τ :=
    norm_periodization_le_cutoff hC hcχ hsχ hψK hone (fun z => (htarget z).1)
  have hv : MemLp (fun τ : UpperHalfPlane => modularPeriodization ψ τ) 2 modularMeasure :=
    (hB.const_mul C).mono' (continuous_periodization_value hψ hcψ hsψ).aestronglyMeasurable
      (Filter.Eventually.of_forall hvbound)
  have hdbound (v : ℂ) (τ : UpperHalfPlane) :
      ‖directional (modularPeriodization ψ) v τ‖ ≤ (H * C * ‖v‖) * B τ :=
    norm_directional_periodization_le_cutoff hC hH.le hψ hcψ hsψ hcχ hsχ hψK hone hheight
      (fun z => (htarget z).2) τ v
  have hd (v : ℂ) : MemLp (directional (modularPeriodization ψ) v) 2 modularMeasure :=
    (hB.const_mul (H * C * ‖v‖)).mono'
      (continuous_periodization_directional hψ hcψ hsψ v).aestronglyMeasurable
      (Filter.Eventually.of_forall (hdbound v))
  let Fn : ℕ → smoothCore := fun n =>
    ⟨modularPeriodization (ψn n), modularPeriodization_mem_smoothCore_of_upper_support
      (hψn n).1 (compactSupport_of_subset_compact hK (hψn n).2) ((hψn n).2.trans hKU)⟩
  let U : ModularHilbert := hv.toLp (fun τ : UpperHalfPlane => modularPeriodization ψ τ)
  let Gx : ModularHilbert := (hd 1).toLp (directional (modularPeriodization ψ) 1)
  let Gy : ModularHilbert := (hd Complex.I).toLp (directional (modularPeriodization ψ) Complex.I)
  let G : GradientSpace := WithLp.toLp 2 (Gx, Gy)
  have hvalue : Tendsto (fun n => value (Fn n)) atTop (𝓝 U) := by
    apply tendsto_toLp_of_dominated
      (fun (n : ℕ) (τ : UpperHalfPlane) => modularPeriodization (ψn n) τ)
      (fun τ : UpperHalfPlane => modularPeriodization ψ τ)
      (fun n => (Fn n).property.2.2.1) hv (fun τ => C * B τ) (hB.const_mul C)
    · intro n
      exact Filter.Eventually.of_forall
        (norm_periodization_le_cutoff hC hcχ hsχ (hψn n).2 hone (fun z => (hbound n z).1))
    · exact Filter.Eventually.of_forall hvbound
    · exact Filter.Eventually.of_forall (fun τ => tendsto_periodization hK hKU hψK
        (fun n => (hψn n).2) hlim τ)
  have hdx : Tendsto (fun n => xComponent (Fn n)) atTop (𝓝 Gx) := by
    apply tendsto_toLp_of_dominated
      (fun n => directional (modularPeriodization (ψn n)) 1)
      (directional (modularPeriodization ψ) 1)
      (fun n => (Fn n).property.2.2.2.1) (hd 1)
      (fun τ => (H * C * ‖(1 : ℂ)‖) * B τ) (hB.const_mul _)
    · intro n
      exact Filter.Eventually.of_forall fun τ => norm_directional_periodization_le_cutoff
        hC hH.le ((hψn n).1.of_le (by simp)) (compactSupport_of_subset_compact hK (hψn n).2)
        ((hψn n).2.trans hKU) hcχ hsχ (hψn n).2 hone hheight (fun z => (hbound n z).2) τ 1
    · exact Filter.Eventually.of_forall (hdbound 1)
    · exact Filter.Eventually.of_forall fun τ => tendsto_directional_periodization hK hKU
        hψ (fun n => (hψn n).1.of_le (by simp)) hψK (fun n => (hψn n).2) hdlim τ 1
  have hdy : Tendsto (fun n => yComponent (Fn n)) atTop (𝓝 Gy) := by
    apply tendsto_toLp_of_dominated
      (fun n => directional (modularPeriodization (ψn n)) Complex.I)
      (directional (modularPeriodization ψ) Complex.I)
      (fun n => (Fn n).property.2.2.2.2) (hd Complex.I)
      (fun τ => (H * C * ‖Complex.I‖) * B τ) (hB.const_mul _)
    · intro n
      exact Filter.Eventually.of_forall fun τ => norm_directional_periodization_le_cutoff
        hC hH.le ((hψn n).1.of_le (by simp)) (compactSupport_of_subset_compact hK (hψn n).2)
        ((hψn n).2.trans hKU) hcχ hsχ (hψn n).2 hone hheight (fun z => (hbound n z).2) τ Complex.I
    · exact Filter.Eventually.of_forall (hdbound Complex.I)
    · exact Filter.Eventually.of_forall fun τ => tendsto_directional_periodization hK hKU
        hψ (fun n => (hψn n).1.of_le (by simp)) hψK (fun n => (hψn n).2) hdlim τ Complex.I
  have hgrad : Tendsto (fun n => coreGradient (Fn n)) atTop (𝓝 G) := by
    exact (WithLp.prodContinuousLinearEquiv 2 ℂ ModularHilbert ModularHilbert).symm.continuous.continuousAt.tendsto.comp
      (hdx.prodMk_nhds hdy)
  have hgraph : (U, G) ∈ closedGradient.graph := by
    apply closedGradient_isClosed.mem_of_tendsto (hvalue.prodMk_nhds hgrad)
    exact Filter.Eventually.of_forall fun n => by
      change (value (Fn n), coreGradient (Fn n)) ∈ closedGradient.graph
      rw [← closedGradient_apply_value]
      exact closedGradient.mem_graph ⟨value (Fn n), gradient_le_closedGradient.1 (LinearMap.mem_range_self value (Fn n))⟩
  let u : FormDomain := ⟨WithLp.toLp 2 (U, G), hgraph⟩
  refine ⟨u, hv.coeFn_toLp, (hd 1).coeFn_toLp, (hd Complex.I).coeFn_toLp⟩

/-- Every genuinely C¹ compact upper seed has a periodization in the actual
closed-gradient form domain, with its literal frame derivatives. -/
theorem exists_form_periodization_of_C1
    (ψ : ℂ → ℂ) (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ upperHalfPlaneSet) :
    ∃ u : FormDomain,
      formEmbedding u =ᵐ[modularMeasure] (fun τ : UpperHalfPlane => modularPeriodization ψ τ) ∧
      (WithLp.ofLp (formGradient u)).1 =ᵐ[modularMeasure] directional (modularPeriodization ψ) 1 ∧
      (WithLp.ofLp (formGradient u)).2 =ᵐ[modularMeasure] directional (modularPeriodization ψ) Complex.I := by
  obtain ⟨K, hK, hKU, hψK, C, hC, ψn, hψn, hlim, hdlim, hbound⟩ :=
    CompactC1UpperApproximation.exists_compactC1UpperApproximation ψ hψ hc hs
  exact exists_form_periodization_of_approximation ψ hψ K hK hKU hψK C hC ψn hψn hlim hdlim hbound

end GapFamily.Analytic.C1Periodization
