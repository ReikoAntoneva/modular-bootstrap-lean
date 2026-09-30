import GapFamily.Analytic.Elliptic.LocalPoissonRegularityH1
import GapFamily.Analytic.Modular.Elliptic.ModularEllipticCube
import GapFamily.Analytic.Modular.Elliptic.ModularEllipticContinuousGeometry
import GapFamily.Analytic.Elliptic.LocalWeakHessianApproximation
import GapFamily.Analytic.Elliptic.LocalContinuousRepresentative

/-!
# Actual local regularity of ordinary global L² Poisson jets

The proved ordinary jet equations build H¹ data and genuine weak Hessians on
centered cubes. Smooth approximation gives local continuous representatives,
which agree almost everywhere with the actual jet value and glue on the open domain.
-/

noncomputable section
namespace GapFamily.Analytic.LocalPoisson
open Set MeasureTheory Homogenization ModularElliptic LocalWeakHessian ModularGradient
open scoped ContDiff

/-- The actual real and imaginary weak Hessians on one common centered cube. -/
theorem exists_centered_hessian_data
    (U : Set ℂ) (hU : IsOpen U) (u : JetSpace U) (z : ℂ) (hz : z ∈ U) :
    ∃ Q : TriadicCube 2, cubeCenter Q = 0 ∧
      ellipticChart z '' scaledClosedCubeSet Q 1 ⊆ U ∧
      ∃ (uR uI : H1Function (scaledOpenCubeSet Q (1 / 2)))
        (_HR : HasWeakHessianOn (scaledOpenCubeSet Q (1 / 2)) uR)
        (_HI : HasWeakHessianOn (scaledOpenCubeSet Q (1 / 2)) uI),
        uR.toFun = (fun v =>
          (valueCLM U u (ellipticChart z v)).re) ∧
        uI.toFun = (fun v =>
          (valueCLM U u (ellipticChart z v)).im) ∧
        uR.grad = (fun v =>
          ![(dxCLM U u (ellipticChart z v)).re,
            (dyCLM U u (ellipticChart z v)).re]) ∧
        uI.grad = (fun v =>
          ![(dxCLM U u (ellipticChart z v)).im,
            (dyCLM U u (ellipticChart z v)).im]) := by
  obtain ⟨Q, hcenter, hQ, _⟩ := exists_centered_cube_closed_subset
    (hU.preimage (ellipticChart z).continuous)
    (by simpa using hz : (0 : Fin 2 → ℝ) ∈ ellipticChart z ⁻¹' U)
  let K := ellipticChart z '' scaledClosedCubeSet Q 1
  have hKU : K ⊆ U := by
    rintro w ⟨v, hv, rfl⟩
    exact hQ hv
  have hUK : ellipticChart z '' openCubeSet Q ⊆ K := by
    apply Set.image_mono
    intro v hv
    have hv' : v ∈ scaledOpenCubeSet Q 1 := by
      simpa only [scaledOpenCubeSet_eq_metricBall Q (by norm_num : (0 : ℝ) < 1),
        one_mul, ball_cubeCenter_eq_openCubeSet] using hv
    exact fun i => (hv' i).le
  obtain ⟨uR, hRv, hRg, ⟨HR⟩⟩ := halfCube_weakHessian Q
    (chartH1 Complex.reCLM U u z _ (hUK.trans hKU))
    (fun v => (sourceCLM U u (ellipticChart z v)).re)
    (chartH1_weakPoisson Complex.reCLM U u z _ (hUK.trans hKU))
    (chartH1_source_memL2 Complex.reCLM U u z _)
  obtain ⟨uI, hIv, hIg, ⟨HI⟩⟩ := halfCube_weakHessian Q
    (chartH1 Complex.imCLM U u z _ (hUK.trans hKU))
    (fun v => (sourceCLM U u (ellipticChart z v)).im)
    (chartH1_weakPoisson Complex.imCLM U u z _ (hUK.trans hKU))
    (chartH1_source_memL2 Complex.imCLM U u z _)
  exact ⟨Q, hcenter, hKU, uR, uI, HR, HI, hRv, hIv, hRg, hIg⟩


/-- The actual Poisson jet value has a continuous representative near every
point of the open domain, with compact closure inside that domain. -/
theorem exists_local_continuousRepresentative
    (U : Set ℂ) (hU : IsOpen U) (u : JetSpace U) (z : ℂ) (hz : z ∈ U) :
    ∃ V : Set ℂ, IsOpen V ∧ z ∈ V ∧ IsCompact (closure V) ∧ closure V ⊆ U ∧
      ∃ G : ℂ → ℂ, ContinuousOn G V ∧
        G =ᵐ[volume.restrict V] (fun w => valueCLM U u w) := by
  obtain ⟨Q, hcenter, hQ, uR, uI, HR, HI, hRv, hIv, _hRg, _hIg⟩ :=
    exists_centered_hessian_data U hU u z hz
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
      valueCLM U u (e q) := by
    dsimp [combinedValue]
    rw [hRv, hIv]
    exact Complex.re_add_im _
  have hgfW : g =ᵐ[volume.restrict W]
      (fun q => valueCLM U u (e q)) := by
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


/-- Local regularity glues to one continuous representative of the actual Poisson jet
value on the entire open domain. -/
theorem exists_continuousRepresentative
    (U : Set ℂ) (hU : IsOpen U) (u : JetSpace U) :
    ∃ G : ℂ → ℂ, ContinuousOn G U ∧
      G =ᵐ[volume.restrict U] (fun w => valueCLM U u w) := by
  apply exists_continuousOn_ae_eq_of_locally U hU
  intro z hz
  obtain ⟨V, hVo, hzV, _hVc, hVU, G, hGc, hGae⟩ :=
    exists_local_continuousRepresentative U hU u z hz
  exact ⟨V, hVo, hzV, (fun w hw => hVU (subset_closure hw)), G, hGc, hGae⟩

end GapFamily.Analytic.LocalPoisson
