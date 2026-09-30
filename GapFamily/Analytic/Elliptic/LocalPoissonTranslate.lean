import GapFamily.Analytic.Elliptic.FixedPoissonPointBound
import Mathlib.MeasureTheory.Group.Integral

/-! Translation of actual Euclidean Poisson jets preserves all four field norms.
The point-bound constant is chosen on one fixed square before its center varies. -/

noncomputable section
namespace GapFamily.Analytic.LocalPoissonTranslate

open Set MeasureTheory ModularGradient LocalPoisson FixedPoissonPointBound
open scoped ContDiff Topology

/-- Pull back a genuine ordinary L² field by translation. -/
def translateField (p : ℂ) : Field →ₗᵢ[ℂ] Field :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun z : ℂ => z + p) (measurePreserving_add_right volume p)

theorem translateField_ae (p : ℂ) (f : Field) :
    (translateField p f : ℂ → ℂ) =ᵐ[volume] fun z => f (z + p) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_add_right volume p)

@[simp] theorem norm_translateField (p : ℂ) (f : Field) : ‖translateField p f‖ = ‖f‖ :=
  (translateField p).norm_map f

private theorem integral_translateField (p : ℂ) (ψ : ℂ → ℂ) (f : Field) :
    (∫ z : ℂ, star (ψ z) * translateField p f z) =
      ∫ z : ℂ, star (ψ (z - p)) * f z := by
  calc
    (∫ z : ℂ, star (ψ z) * translateField p f z) =
        ∫ z : ℂ, star (ψ z) * f (z + p) := by
      apply integral_congr_ae
      filter_upwards [translateField_ae p f] with z hz
      rw [hz]
    _ = ∫ z : ℂ, star (ψ (z - p)) * f z := by
      simpa only [add_sub_cancel_right] using
        integral_add_right_eq_self (fun z : ℂ => star (ψ (z - p)) * f z) p

private theorem fderiv_translate_test (p : ℂ) (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (z v : ℂ) :
    fderiv ℝ (fun w => ψ (w - p)) z v = fderiv ℝ ψ (z - p) v := by
  have h := ((hψ.differentiable (by simp)).differentiableAt.hasFDerivAt).comp z
    ((hasFDerivAt_id z).sub_const p)
  simpa [Function.comp_def] using congrArg (fun A : ℂ →L[ℝ] ℂ => A v) h.fderiv

/-- Translate every field of the actual four-field jet. -/
def translateJet (p : ℂ) (j : Jet) : Jet :=
  (translateField p j.1, translateField p j.2.1,
    translateField p j.2.2.1, translateField p j.2.2.2)

/-- Translation preserves all three distributional equations against arbitrary
smooth compact tests in the translated region. -/
theorem translateJet_mem (p : ℂ) (U : Set ℂ) (j : Jet)
    (hj : j ∈ jetSubmodule {z : ℂ | z - p ∈ U}) :
    translateJet p j ∈ jetSubmodule U := by
  intro ψ hψ hc hs
  let φ : ℂ → ℂ := fun z => ψ (z - p)
  have hφ : ContDiff ℝ ∞ φ := hψ.comp (contDiff_id.sub contDiff_const)
  have hcφ : HasCompactSupport φ := hc.comp_homeomorph (Homeomorph.subRight p)
  have hsφ : tsupport φ ⊆ {z : ℂ | z - p ∈ U} := by
    intro z hz
    exact hs (tsupport_comp_subset_preimage ψ (continuous_id.sub continuous_const) hz)
  obtain ⟨hx, hy, hf⟩ := hj φ hφ hcφ hsφ
  have hv (f : Field) :
      inner ℂ (euclideanCompactTest ψ hψ.continuous hc) (translateField p f) =
        inner ℂ (euclideanCompactTest φ hφ.continuous hcφ) f := by
    rw [euclideanCompactTest_inner, euclideanCompactTest_inner]
    exact integral_translateField p ψ f
  have hd (f : Field) (v : ℂ) :
      inner ℂ (upperTestDerivativeL2 ψ hψ hc v) (translateField p f) =
        inner ℂ (upperTestDerivativeL2 φ hφ hcφ v) f := by
    rw [inner_derivativeTest_eq_integral, inner_derivativeTest_eq_integral,
      integral_translateField]
    congr 1
    funext z
    rw [fderiv_translate_test p ψ hψ z v]
  change inner ℂ _ (translateField p j.2.1) = -inner ℂ _ (translateField p j.1) ∧
    inner ℂ _ (translateField p j.2.2.1) = -inner ℂ _ (translateField p j.1) ∧
    inner ℂ _ (translateField p j.2.1) + inner ℂ _ (translateField p j.2.2.1) =
      inner ℂ _ (translateField p j.2.2.2)
  rw [hv, hv, hv, hd, hd, hd, hd]
  exact ⟨hx, hy, hf⟩

/-- A genuine jet on a translated region becomes a genuine jet on the reference region. -/
def translateJetSpace (p : ℂ) (U : Set ℂ)
    (j : JetSpace {z : ℂ | z - p ∈ U}) : JetSpace U :=
  ⟨translateJet p j.val, translateJet_mem p U j.val j.property⟩

/-- Translation preserves each of the four global ordinary L² norms. -/
theorem translateJetSpace_field_norm (p : ℂ) (U : Set ℂ)
    (j : JetSpace {z : ℂ | z - p ∈ U}) :
    ‖valueCLM U (translateJetSpace p U j)‖ = ‖valueCLM {z : ℂ | z - p ∈ U} j‖ ∧
    ‖dxCLM U (translateJetSpace p U j)‖ = ‖dxCLM {z : ℂ | z - p ∈ U} j‖ ∧
    ‖dyCLM U (translateJetSpace p U j)‖ = ‖dyCLM {z : ℂ | z - p ∈ U} j‖ ∧
    ‖sourceCLM U (translateJetSpace p U j)‖ =
      ‖sourceCLM {z : ℂ | z - p ∈ U} j‖ := by
  simp [translateJetSpace, translateJet]

private theorem translated_ae {E : Type*} (p : ℂ) (U : Set ℂ) (f g : ℂ → E)
    (h : g =ᵐ[volume.restrict {z | z - p ∈ U}] f) :
    (fun w => g (w + p)) =ᵐ[volume.restrict U] (fun w => f (w + p)) := by
  have hm := (measurePreserving_add_right (volume : Measure ℂ) p).restrict_preimage_emb
    (Homeomorph.addRight p).measurableEmbedding {z | z - p ∈ U}
  have ha := hm.quasiMeasurePreserving.ae h
  change ∀ᵐ w ∂volume.restrict U, g (w + p) = f (w + p)
  simpa using ha

/-- A single constant controls the center of every translated reference square.
The inputs are genuine Poisson jets and continuous representatives of their
value field; the four global field norms remain the original unshifted norms. -/
theorem exists_translated_point_sq_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℂ)
      (j : JetSpace {z : ℂ | z - p ∈ referenceSquare}) (g : ℂ → ℂ),
      ContinuousOn g {z : ℂ | z - p ∈ referenceSquare} →
      g =ᵐ[volume.restrict {z : ℂ | z - p ∈ referenceSquare}]
        (fun w => valueCLM {z : ℂ | z - p ∈ referenceSquare} j w) →
      ‖g p‖ ^ 2 ≤ C *
        (‖valueCLM {z : ℂ | z - p ∈ referenceSquare} j‖ ^ 2 +
         ‖dxCLM {z : ℂ | z - p ∈ referenceSquare} j‖ ^ 2 +
         ‖dyCLM {z : ℂ | z - p ∈ referenceSquare} j‖ ^ 2 +
         ‖sourceCLM {z : ℂ | z - p ∈ referenceSquare} j‖ ^ 2) := by
  obtain ⟨C, hC, hbound⟩ := exists_point_sq_bound referenceSquare
    isOpen_referenceSquare 0 zero_mem_referenceSquare
  refine ⟨C, hC, fun p j g hg hga => ?_⟩
  let j' := translateJetSpace p referenceSquare j
  have hg' : ContinuousOn (fun w => g (w + p)) referenceSquare :=
    hg.comp (continuous_id.add continuous_const).continuousOn
      (by intro w hw; simpa using hw)
  have hga' : (fun w => g (w + p)) =ᵐ[volume.restrict referenceSquare]
      (fun w => valueCLM referenceSquare j' w) := by
    filter_upwards [translated_ae p referenceSquare _ _ hga,
      ae_restrict_of_ae (translateField_ae p j.val.1)] with w hw ht
    exact hw.trans ht.symm
  have hb := hbound j' (fun w => g (w + p)) hg' hga'
  obtain ⟨h0, hx, hy, hf⟩ := translateJetSpace_field_norm p referenceSquare j
  simpa only [zero_add, j', h0, hx, hy, hf] using hb

end GapFamily.Analytic.LocalPoissonTranslate
