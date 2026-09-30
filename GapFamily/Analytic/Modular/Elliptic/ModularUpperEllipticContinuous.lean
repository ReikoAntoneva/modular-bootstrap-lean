import GapFamily.Analytic.Modular.Elliptic.ModularUpperEllipticHessian
import GapFamily.Analytic.Modular.Elliptic.ModularEllipticContinuousGeometry
import GapFamily.Analytic.Elliptic.LocalWeakHessianApproximation
import GapFamily.Analytic.Elliptic.LocalContinuousRepresentative

/-!
# Continuous representatives on actual upper-half-plane cutoff plateaus

The actual upper elliptic value has genuine weak Hessians on centered cubes
inside an open cutoff plateau. Smooth approximation on a smaller rectangle
gives local continuous representatives; their proved almost-everywhere
agreement glues them on the whole plateau, including modular seams.
-/

noncomputable section
namespace GapFamily.Analytic.ModularGradient
open Set MeasureTheory Homogenization ModularElliptic LocalWeakHessian
open scoped ContDiff

/-- The actual upper elliptic value has a continuous representative near every
point of an open cutoff plateau, with compact closure inside that plateau. -/
theorem laplacian_upper_exists_local_continuousRepresentative
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ UpperHalfPlane.upperHalfPlaneSet)
    (U : Set ℂ) (hU : IsOpen U) (hχU : EqOn χ (fun _ => 1) U)
    (u : laplacian.domain) (z : ℂ) (hz : z ∈ U) :
    ∃ V : Set ℂ, IsOpen V ∧ z ∈ V ∧ IsCompact (closure V) ∧ closure V ⊆ U ∧
      ∃ G : ℂ → ℂ, ContinuousOn G V ∧
        G =ᵐ[volume.restrict V] (fun w => upperEllipticValue χ hχ hcχ hsχ u w) := by
  obtain ⟨Q, hcenter, hQ, uR, uI, HR, HI, hRv, hIv, _hRg, _hIg⟩ :=
    laplacian_upper_exists_centered_hessian_data χ hχ hcχ hsχ U hU hχU u z hz
  let a := ellipticInnerRadius Q
  have ha : 0 < a := ellipticInnerRadius_pos Q
  have hCube := scaledOpenCubeSet_isOpenBoundedConvexDomain Q (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨g, hgc, hgf⟩ := exists_continuousOn_pair_of_weakHessian hCube uR uI HR HI
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
  have hRU : e '' R ⊆ U := by
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
      upperEllipticValue χ hχ hcχ hsχ u (e q) := by
    dsimp [combinedValue]
    rw [hRv, hIv]
    exact Complex.re_add_im _
  have hgfW : g =ᵐ[volume.restrict W]
      (fun q => upperEllipticValue χ hχ hcχ hsχ u (e q)) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hWR hgf] with q hq
    exact hq.trans (hactual q)
  have hinv : MeasurePreserving e.symm (volume.restrict (e '' W)) (volume.restrict W) :=
    (ellipticPairChart_measurePreserving_restrict_image z W).symm e.toMeasurableEquiv
  refine ⟨e '' W, e.isOpenMap _ (isOpen_Ioo.prod isOpen_Ioo), ?_,
    hRc.of_isClosed_subset isClosed_closure hclosure, hclosure.trans hRU,
    fun w => g (e.symm w), ?_, ?_⟩
  · exact ⟨0, hzero, ellipticPairChart_zero z⟩
  · apply (hgc.mono hWR).comp e.symm.continuous.continuousOn
    rintro w ⟨q, hq, rfl⟩
    simpa using hq
  · filter_upwards [hinv.quasiMeasurePreserving.ae hgfW] with w hw
    simpa using hw


/-- Local regularity glues to one continuous representative of the actual upper
elliptic value on the entire open plateau. -/
theorem laplacian_upper_exists_continuousRepresentative
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ UpperHalfPlane.upperHalfPlaneSet)
    (U : Set ℂ) (hU : IsOpen U) (hχU : EqOn χ (fun _ => 1) U)
    (u : laplacian.domain) :
    ∃ G : ℂ → ℂ, ContinuousOn G U ∧
      G =ᵐ[volume.restrict U] (fun w => upperEllipticValue χ hχ hcχ hsχ u w) := by
  apply exists_continuousOn_ae_eq_of_locally U hU
  intro z hz
  obtain ⟨V, hVo, hzV, _hVc, hVU, G, hGc, hGae⟩ :=
    laplacian_upper_exists_local_continuousRepresentative χ hχ hcχ hsχ U hU hχU u z hz
  exact ⟨V, hVo, hzV, (fun w hw => hVU (subset_closure hw)), G, hGc, hGae⟩

end GapFamily.Analytic.ModularGradient
