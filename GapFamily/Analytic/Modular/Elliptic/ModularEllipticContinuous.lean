import GapFamily.Analytic.Modular.Elliptic.ModularEllipticContinuousGeometry
import GapFamily.Analytic.Elliptic.LocalWeakHessianApproximation

/-!
# Continuous representatives of actual modular operator-domain fields

The ordinary local weak Hessians construct a common smooth approximation. The
rectangle trace estimate makes its values converge uniformly on an inner
rectangle. Measure-preserving centered coordinates then identify its continuous
limit almost everywhere with the original modular field.
-/

noncomputable section
namespace GapFamily.Analytic.ModularGradient
open Set MeasureTheory Homogenization ModularElliptic LocalWeakHessian

/-- Every actual operator-domain vector has a continuous representative near each
interior point, on a neighborhood with compact closure in the modular interior. -/
theorem laplacian_exists_local_continuousRepresentative
    (u : laplacian.domain) (z : ℂ) (hz : z ∈ modularInterior) :
    ∃ V : Set ℂ, IsOpen V ∧ z ∈ V ∧ IsCompact (closure V) ∧
      closure V ⊆ modularInterior ∧
      ∃ G : ℂ → ℂ, ContinuousOn G V ∧
        G =ᵐ[volume.restrict V]
          (fun w => coordinateValue ⟨u, laplacian_domain_le u.property⟩ w) := by
  obtain ⟨Q, hcenter, hQ, uR, uI, HR, HI, hRv, hIv, _hRg, _hIg⟩ :=
    laplacian_exists_centered_hessian_data u z hz
  let a := ellipticInnerRadius Q
  have ha : 0 < a := ellipticInnerRadius_pos Q
  have hU := scaledOpenCubeSet_isOpenBoundedConvexDomain Q (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨g, hgc, hgf⟩ := exists_continuousOn_pair_of_weakHessian hU uR uI HR HI
    (ellipticInnerRadius_closedBall_subset Q hcenter) ha
    (ellipticInnerRadius_rectangle_subset Q hcenter)
    (show 0 < a / 2 by positivity) (show 0 < a / 2 by positivity)
    (show -a < a - a / 2 by linarith) (show -a < a - a / 2 by linarith)
  let W : Set (ℝ × ℝ) := Ioo (-a) (a - a / 2) ×ˢ Ioo (-a) (a - a / 2)
  let R : Set (ℝ × ℝ) := Icc (-a) (a - a / 2) ×ˢ Icc (-a) (a - a / 2)
  let e := ellipticPairChart z
  have hWR : W ⊆ R := by
    rintro q ⟨hx, hy⟩
    exact ⟨⟨hx.1.le, hx.2.le⟩, ⟨hy.1.le, hy.2.le⟩⟩
  have hRbig : R ⊆ Icc (-a) a ×ˢ Icc (-a) a := by
    rintro q ⟨hx, hy⟩
    exact ⟨⟨hx.1, by linarith [hx.2]⟩, ⟨hy.1, by linarith [hy.2]⟩⟩
  have hRint : e '' R ⊆ modularInterior := by
    rintro w ⟨q, hq, rfl⟩
    apply hQ
    refine ⟨pairToVec q, ?_, rfl⟩
    have hhalf := ellipticInnerRadius_rectangle_subset Q hcenter (hRbig hq)
    intro i
    have hi := hhalf i
    have hp := cubeRadius_pos Q
    change |pairToVec q i - cubeCenter Q i| ≤ (1 : ℝ) * cubeRadius Q
    linarith
  have hRc : IsCompact (e '' R) :=
    (isCompact_Icc.prod isCompact_Icc).image e.continuous
  have hclosure : closure (e '' W) ⊆ e '' R :=
    closure_minimal (image_mono hWR) hRc.isClosed
  have hzero : (0 : ℝ × ℝ) ∈ W := by
    change (-a < (0 : ℝ) ∧ (0 : ℝ) < a - a / 2) ∧
      (-a < (0 : ℝ) ∧ (0 : ℝ) < a - a / 2)
    constructor <;> constructor <;> linarith
  have hactual (q : ℝ × ℝ) : combinedValue uR uI (pairToVec q) =
      coordinateValue ⟨u, laplacian_domain_le u.property⟩ (e q) := by
    dsimp [combinedValue]
    rw [hRv, hIv]
    exact Complex.re_add_im _
  have hgfW : g =ᵐ[volume.restrict W]
      (fun q => coordinateValue ⟨u, laplacian_domain_le u.property⟩ (e q)) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hWR hgf] with q hq
    exact hq.trans (hactual q)
  have hinv : MeasurePreserving e.symm (volume.restrict (e '' W)) (volume.restrict W) :=
    (ellipticPairChart_measurePreserving_restrict_image z W).symm e.toMeasurableEquiv
  refine ⟨e '' W, e.isOpenMap _ (isOpen_Ioo.prod isOpen_Ioo), ?_,
    hRc.of_isClosed_subset isClosed_closure hclosure, hclosure.trans hRint,
    fun w => g (e.symm w), ?_, ?_⟩
  · exact ⟨0, hzero, ellipticPairChart_zero z⟩
  · apply (hgc.mono hWR).comp e.symm.continuous.continuousOn
    rintro w ⟨q, hq, rfl⟩
    simpa using hq
  · filter_upwards [hinv.quasiMeasurePreserving.ae hgfW] with w hw
    simpa using hw

end GapFamily.Analytic.ModularGradient
