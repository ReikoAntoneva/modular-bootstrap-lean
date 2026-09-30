import GapFamily.Analytic.Modular.Elliptic.ModularUpperEvaluationCoherence
import GapFamily.Analytic.Modular.ModularMeasureSupport
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

noncomputable section
namespace GapFamily.Analytic.ModularGradient
open Set Filter MeasureTheory UpperHalfPlane Dirichlet
open scoped Topology ContDiff MatrixGroups

theorem quasiMeasurePreserving_upperHalfPlane_coe :
    Measure.QuasiMeasurePreserving UpperHalfPlane.coe (volume : Measure UpperHalfPlane)
      (volume : Measure ℂ) := by
  have hm : MeasurePreserving UpperHalfPlane.coe
      ((volume : Measure ℂ).comap UpperHalfPlane.coe)
      ((volume : Measure ℂ).restrict (Set.range UpperHalfPlane.coe)) :=
    ⟨UpperHalfPlane.measurable_coe, UpperHalfPlane.measurableEmbedding_coe.map_comap _⟩
  have hd : (volume : Measure UpperHalfPlane) ≪ (volume : Measure ℂ).comap UpperHalfPlane.coe := by
    rw [UpperHalfPlane.volume_def]
    exact withDensity_absolutelyContinuous _ _
  exact (hm.quasiMeasurePreserving.mono_left hd).mono_right
    Measure.absolutelyContinuous_restrict

/-- Actual cutoff fields retain automorphy after Hilbert completion. The cutoff
factors make the identity meaningful globally, including outside either chart. -/
theorem upperCutoffHilbertValueOperator_modular
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ upperHalfPlaneSet)
    (η : ℂ → ℂ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (hsη : tsupport η ⊆ upperHalfPlaneSet)
    (f : ModularHilbert) (γ : SL(2, ℤ)) :
    ∀ᵐ τ : UpperHalfPlane ∂volume,
      η τ * upperCutoffHilbertValueOperator χ hχ hcχ hsχ f (γ • τ : UpperHalfPlane) =
        χ (γ • τ : UpperHalfPlane) * upperCutoffHilbertValueOperator η hη hcη hsη f τ := by
  let A := upperCutoffHilbertValueOperator χ hχ hcχ hsχ
  let B := upperCutoffHilbertValueOperator η hη hcη hsη
  have hd : DenseRange value := by
    simpa only [DenseRange, LinearMap.coe_range] using value_dense_range
  obtain ⟨p, hp, ht⟩ := mem_closure_iff_seq_limit.mp (hd f)
  choose F hF using hp
  have hseq : Tendsto (fun n => value (F n)) atTop (𝓝 f) := by
    have he : (fun n => value (F n)) = p := funext hF
    rwa [he]
  have hA := A.continuous.continuousAt.tendsto.comp hseq
  have hB := B.continuous.continuousAt.tendsto.comp hseq
  obtain ⟨n₁, hn₁, ha⟩ := (tendstoInMeasure_of_tendsto_Lp hA).exists_seq_tendsto_ae
  obtain ⟨n₂, hn₂, hb⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (hB.comp hn₁.tendsto_atTop)).exists_seq_tendsto_ae
  have hcoreA : ∀ᵐ z : ℂ ∂volume, ∀ n : ℕ,
      A (value (F (n₁ (n₂ n)))) z = χ z * (F (n₁ (n₂ n))).val z :=
    ae_all_iff.mpr fun n => upperCutoffHilbertValueOperator_value_ae χ hχ hcχ hsχ _
  have hcoreB : ∀ᵐ z : ℂ ∂volume, ∀ n : ℕ,
      B (value (F (n₁ (n₂ n)))) z = η z * (F (n₁ (n₂ n))).val z :=
    ae_all_iff.mpr fun n => upperCutoffHilbertValueOperator_value_ae η hη hcη hsη _
  have hq := quasiMeasurePreserving_upperHalfPlane_coe
  have hqγ := hq.comp (measurePreserving_modularAction γ).quasiMeasurePreserving
  filter_upwards [hqγ.ae ha, hq.ae hb, hqγ.ae hcoreA, hq.ae hcoreB]
    with τ haτ hbτ hcA hcB
  simp only [Function.comp_apply] at hcA
  have hleft := (haτ.comp hn₂.tendsto_atTop).const_mul (η τ)
  have hright := hbτ.const_mul (χ (γ • τ : UpperHalfPlane))
  have he : (fun n => η τ * A (value (F (n₁ (n₂ n)))) (γ • τ : UpperHalfPlane)) =
      (fun n => χ (γ • τ : UpperHalfPlane) * B (value (F (n₁ (n₂ n)))) τ) := by
    funext n
    rw [hcA n, hcB n, (F (n₁ (n₂ n))).property.2.1 γ τ]
    ring
  change Tendsto (fun n => η τ * A (value (F (n₁ (n₂ n)))) (γ • τ : UpperHalfPlane))
    atTop (𝓝 (η τ * A f (γ • τ : UpperHalfPlane))) at hleft
  rw [he] at hleft
  exact tendsto_nhds_unique hleft hright

/-- The actual continuous graph representative is automorphic wherever its
two observation charts contain the corresponding modular points. -/
theorem laplacianUpperRepresentative_modular
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ upperHalfPlaneSet)
    (η : ℂ → ℂ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (hsη : tsupport η ⊆ upperHalfPlaneSet)
    (U V : Set ℂ) (hU : IsOpen U) (hV : IsOpen V)
    (hχU : EqOn χ (fun _ => 1) U) (hηV : EqOn η (fun _ => 1) V)
    (u : LaplacianGraphDomain) (γ : SL(2, ℤ)) (τ : UpperHalfPlane)
    (hτU : ((γ • τ : UpperHalfPlane) : ℂ) ∈ U) (hτV : (τ : ℂ) ∈ V) :
    laplacianUpperRepresentative χ hχ hcχ hsχ U hU hχU u (γ • τ : UpperHalfPlane) =
      laplacianUpperRepresentative η hη hcη hsη V hV hηV u τ := by
  have hγ : Continuous (fun ξ : UpperHalfPlane => γ • ξ) := by
    simpa only [ModularGroup.sl_moeb] using
      (continuous_const_smul (γ : GL (Fin 2) ℝ) :
        Continuous (fun ξ : UpperHalfPlane => (γ : GL (Fin 2) ℝ) • ξ))
  have hcγ := UpperHalfPlane.continuous_coe.comp hγ
  let W : Set UpperHalfPlane :=
    {ξ | ((γ • ξ : UpperHalfPlane) : ℂ) ∈ U ∧ (ξ : ℂ) ∈ V}
  have hW : IsOpen W := (hU.preimage hcγ).inter (hV.preimage UpperHalfPlane.continuous_coe)
  have hq := quasiMeasurePreserving_upperHalfPlane_coe
  have hqγ := hq.comp (measurePreserving_modularAction γ).quasiMeasurePreserving
  have ha := hqγ.ae (ae_imp_of_ae_restrict
    (laplacianUpperRepresentative_ae χ hχ hcχ hsχ U hU hχU u))
  have hb := hq.ae (ae_imp_of_ae_restrict
    (laplacianUpperRepresentative_ae η hη hcη hsη V hV hηV u))
  have hcov := upperCutoffHilbertValueOperator_modular χ hχ hcχ hsχ η hη hcη hsη
    (gradientEmbedding laplacian u) γ
  have he : (fun ξ : UpperHalfPlane =>
      laplacianUpperRepresentative χ hχ hcχ hsχ U hU hχU u (γ • ξ : UpperHalfPlane))
      =ᵐ[(volume : Measure UpperHalfPlane).restrict W]
      (fun ξ => laplacianUpperRepresentative η hη hcη hsη V hV hηV u ξ) := by
    filter_upwards [ae_restrict_of_ae ha, ae_restrict_of_ae hb,
      ae_restrict_of_ae hcov, ae_restrict_mem hW.measurableSet] with ξ haξ hbξ hcξ hξ
    change ((γ • ξ : UpperHalfPlane) : ℂ) ∈ U ∧ (ξ : ℂ) ∈ V at hξ
    simp only [Function.comp_apply] at haξ
    rw [haξ hξ.1, hbξ hξ.2]
    rw [hχU hξ.1, hηV hξ.2, one_mul, one_mul] at hcξ
    exact hcξ
  let : (volume : Measure UpperHalfPlane).IsOpenPosMeasure :=
    ⟨fun O hO hne => (upperHalfPlane_volume_pos_of_isOpen O hO hne).ne'⟩
  exact Measure.eqOn_open_of_ae_eq (μ := (volume : Measure UpperHalfPlane)) he hW
    ((laplacianUpperRepresentative_continuousOn χ hχ hcχ hsχ U hU hχU u).comp
      hcγ.continuousOn (fun _ hξ => hξ.1))
    ((laplacianUpperRepresentative_continuousOn η hη hcη hsη V hV hηV u).comp
      UpperHalfPlane.continuous_coe.continuousOn (fun _ hξ => hξ.2)) ⟨hτU, hτV⟩

/-- Actual bounded compact graph evaluations agree at modularly equivalent
points, including observation sets of zero area and seam points. -/
theorem laplacianUpperCompactEvaluation_modular
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ upperHalfPlaneSet)
    (η : ℂ → ℂ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (hsη : tsupport η ⊆ upperHalfPlaneSet)
    (U V : Set ℂ) (hU : IsOpen U) (hV : IsOpen V)
    (hχU : EqOn χ (fun _ => 1) U) (hηV : EqOn η (fun _ => 1) V)
    (K₁ K₂ : Set ℂ) [CompactSpace K₁] [CompactSpace K₂]
    (h₁U : K₁ ⊆ U) (h₂V : K₂ ⊆ V)
    (u : LaplacianGraphDomain) (γ : SL(2, ℤ)) (τ : UpperHalfPlane)
    (hτ₁ : ((γ • τ : UpperHalfPlane) : ℂ) ∈ K₁) (hτ₂ : (τ : ℂ) ∈ K₂) :
    laplacianUpperCompactEvaluation χ hχ hcχ hsχ U hU hχU K₁ h₁U
      ⟨((γ • τ : UpperHalfPlane) : ℂ), hτ₁⟩ u =
    laplacianUpperCompactEvaluation η hη hcη hsη V hV hηV K₂ h₂V
      ⟨(τ : ℂ), hτ₂⟩ u :=
  laplacianUpperRepresentative_modular χ hχ hcχ hsχ η hη hcη hsη U V hU hV hχU hηV
    u γ τ (h₁U hτ₁) (h₂V hτ₂)

end GapFamily.Analytic.ModularGradient
