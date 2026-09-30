import GapFamily.Analytic.Spatial.SpatialOrbitPointResolvent
import GapFamily.Analytic.Modular.ModularCompactEvaluationAE
import GapFamily.Analytic.Modular.Elliptic.ModularUpperEvaluationModular

/-! Physical point values of the actual orbit-source graph vector. -/
noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open Set Filter MeasureTheory UpperHalfPlane ModularGradient Dirichlet
open scoped Topology ContDiff MatrixGroups

private theorem continuousOn_eq_of_ae_on_support
    {f g : UpperHalfPlane → ℂ} {U : Set UpperHalfPlane}
    (hU : IsOpen U) (hf : ContinuousOn f U) (hg : ContinuousOn g U)
    (he : ∀ᵐ x ∂modularMeasure, x ∈ U → f x = g x)
    {x : UpperHalfPlane} (hx : x ∈ U) (hxs : x ∈ modularMeasure.support) :
    f x = g x := by
  by_contra hne
  have hn : {y | f y ≠ g y} ∈ 𝓝 x :=
    (hf.continuousAt (hU.mem_nhds hx)).prodMk_nhds
      (hg.continuousAt (hU.mem_nhds hx))
      (isClosed_diagonal.isOpen_compl.mem_nhds hne)
  have hzero : modularMeasure (U ∩ {y | f y ≠ g y}) = 0 := by
    simpa only [ae_iff, Classical.not_imp, Set.ofPred_and, Set.ofPred_mem_eq] using he
  exact ((Measure.mem_support_iff_forall x).mp hxs _
    (inter_mem (hU.mem_nhds hx) hn)).ne' hzero

private theorem spatialOrbitPoint_representative_of_support
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ upperHalfPlaneSet)
    (U : Set ℂ) (hU : IsOpen U) (hχU : EqOn χ (fun _ => 1) U)
    (s : ℂ) (hs : 1 < s.re) (w : UpperHalfPlane)
    (hdom : spatialOrbitPointSource s w ∈ laplacian.domain)
    (z : UpperHalfPlane) (hz : (z : ℂ) ∈ U)
    (hzs : z ∈ modularMeasure.support) :
    laplacianUpperRepresentative χ hχ hcχ hsχ U hU hχU
      (gradientLift laplacian ⟨spatialOrbitPointSource s w, hdom⟩) z =
        spatialOrbitKernel s z w := by
  let u := gradientLift laplacian ⟨spatialOrbitPointSource s w, hdom⟩
  have hrep : ∀ᵐ τ : UpperHalfPlane ∂modularMeasure, (τ : ℂ) ∈ U →
      laplacianUpperRepresentative χ hχ hcχ hsχ U hU hχU u τ =
        laplacianUpperGraphValue χ hχ hcχ hsχ u τ :=
    (ae_modularCoordinate_iff _).mp
      (modularCoordinateMeasure_absolutelyContinuous_volume.ae_le
        (ae_imp_of_ae_restrict
          (laplacianUpperRepresentative_ae χ hχ hcχ hsχ U hU hχU u)))
  have hkernel : ContinuousOn (fun τ : UpperHalfPlane => spatialOrbitKernel s τ w)
      (UpperHalfPlane.coe ⁻¹' U) := by
    simpa only [Function.comp_def, ofComplex_apply] using
      (contDiffOn_spatialOrbitKernel_left s hs w).continuousOn.comp
        UpperHalfPlane.continuous_coe.continuousOn (fun τ _ => τ.im_pos)
  apply continuousOn_eq_of_ae_on_support
    (hU.preimage UpperHalfPlane.continuous_coe)
    ((laplacianUpperRepresentative_continuousOn χ hχ hcχ hsχ U hU hχU u).comp
      UpperHalfPlane.continuous_coe.continuousOn (fun _ h => h))
    hkernel _ hz hzs
  filter_upwards [hrep,
    upperCutoffHilbertValueOperator_modular_ae χ hχ hcχ hsχ
      (spatialOrbitPointSource s w), spatialOrbitPointSource_ae s hs w]
    with τ hr hv hf
  intro hτ
  simp only [Function.comp_apply]
  rw [hr hτ]
  change upperCutoffHilbertValueOperator χ hχ hcχ hsχ
    (gradientEmbedding laplacian u) τ = _
  simp only [u, gradientEmbedding_lift]
  rw [hv, hχU hτ, one_mul, hf]

/-- The graph evaluator of the actual convergent orbit source has the literal
orbit sum at every point of an arbitrary compact observation set. -/
theorem laplacianUpperCompactRestriction_spatialOrbitPointSource
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ upperHalfPlaneSet)
    (U : Set ℂ) (hU : IsOpen U) (hχU : EqOn χ (fun _ => 1) U)
    (K : Set ℂ) [CompactSpace K] (hKU : K ⊆ U)
    (s : ℂ) (hs : 1 < s.re) (w : UpperHalfPlane)
    (hdom : spatialOrbitPointSource s w ∈ laplacian.domain)
    (z : UpperHalfPlane) (hz : (z : ℂ) ∈ K) :
    laplacianUpperCompactRestriction χ hχ hcχ hsχ U hU hχU K hKU
      (gradientLift laplacian ⟨spatialOrbitPointSource s w, hdom⟩)
      ⟨(z : ℂ), hz⟩ = spatialOrbitKernel s z w := by
  obtain ⟨γ, hγ⟩ := ModularGroup.exists_smul_mem_fd z
  let p : UpperHalfPlane := γ • z
  obtain ⟨L, V, η, _hL, _hreg, hpL, hV, hLV, _hVc, _hVH, hη, hcη, hsη, hηV⟩ :=
    exists_upperEvaluationCutoff (isCompact_singleton (x := (p : ℂ)))
      (show {(p : ℂ)} ⊆ upperHalfPlaneSet from fun q h => by
        rw [Set.mem_singleton_iff.mp h]
        exact p.im_pos)
  have hpV : (p : ℂ) ∈ V := hLV (interior_subset (hpL (by simp)))
  have hps : p ∈ modularMeasure.support := by
    rw [modularMeasure_support]
    exact hγ
  change laplacianUpperRepresentative χ hχ hcχ hsχ U hU hχU
    (gradientLift laplacian ⟨spatialOrbitPointSource s w, hdom⟩) z = _
  calc
    _ = laplacianUpperRepresentative η hη hcη hsη V hV hηV
        (gradientLift laplacian ⟨spatialOrbitPointSource s w, hdom⟩) p :=
      (laplacianUpperRepresentative_modular η hη hcη hsη χ hχ hcχ hsχ
        V U hV hU hηV hχU _ γ z hpV (hKU hz)).symm
    _ = spatialOrbitKernel s p w :=
      spatialOrbitPoint_representative_of_support η hη hcη hsη V hV hηV
        s hs w hdom p hpV hps
    _ = spatialOrbitKernel s z w := spatialOrbitKernel_modular_left s γ z w

end GapFamily.Analytic.SpatialPoint
