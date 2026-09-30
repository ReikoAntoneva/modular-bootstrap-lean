import GapFamily.Analytic.Modular.Elliptic.ModularEllipticContinuousGeometry
import GapFamily.Analytic.Elliptic.LocalWeakHessianApproximation

noncomputable section

namespace GapFamily.Analytic.WeakHessianContinuousGradient

open Set MeasureTheory Homogenization ModularElliptic LocalWeakHessian ModularGradient

/-- Actual weak Hessians of two real `H¹` fields give a continuous complex
representative on a neighborhood of the center, with compact closure in the half cube.
The representative is constructed by the proved local approximation theorem. -/
theorem exists_local_continuous_pair_halfCube (Q : TriadicCube 2)
    (hcenter : cubeCenter Q = 0)
    (uR uI : H1Function (scaledOpenCubeSet Q (1 / 2)))
    (HR : HasWeakHessianOn (scaledOpenCubeSet Q (1 / 2)) uR)
    (HI : HasWeakHessianOn (scaledOpenCubeSet Q (1 / 2)) uI) :
    ∃ W : Set (Vec 2), IsOpen W ∧ (0 : Vec 2) ∈ W ∧ IsCompact (closure W) ∧
      closure W ⊆ scaledOpenCubeSet Q (1 / 2) ∧
      ∃ g : Vec 2 → ℂ, ContinuousOn g W ∧
        g =ᵐ[volume.restrict W] combinedValue uR uI := by
  let a := ellipticInnerRadius Q
  have ha : 0 < a := ellipticInnerRadius_pos Q
  have hCube := scaledOpenCubeSet_isOpenBoundedConvexDomain Q
    (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨g, hgc, hgf⟩ := exists_continuousOn_pair_of_weakHessian hCube uR uI HR HI
    (ellipticInnerRadius_closedBall_subset Q hcenter) ha
    (ellipticInnerRadius_rectangle_subset Q hcenter)
    (show 0 < a / 2 by positivity) (show 0 < a / 2 by positivity)
    (show -a < a - a / 2 by linarith) (show -a < a - a / 2 by linarith)
  let W : Set (ℝ × ℝ) := Ioo (-a) (a - a / 2) ×ˢ Ioo (-a) (a - a / 2)
  let R : Set (ℝ × ℝ) := Icc (-a) (a - a / 2) ×ˢ Icc (-a) (a - a / 2)
  let e := pairToVec.toHomeomorph
  have hWR : W ⊆ R := by
    rintro q ⟨hx, hy⟩
    exact ⟨⟨hx.1.le, hx.2.le⟩, ⟨hy.1.le, hy.2.le⟩⟩
  have hRbig : R ⊆ Icc (-a) a ×ˢ Icc (-a) a := by
    rintro q ⟨hx, hy⟩
    exact ⟨⟨hx.1, by linarith [hx.2]⟩, ⟨hy.1, by linarith [hy.2]⟩⟩
  have hRU : e '' R ⊆ scaledOpenCubeSet Q (1 / 2) := by
    rintro v ⟨q, hq, rfl⟩
    exact ellipticInnerRadius_rectangle_subset Q hcenter (hRbig hq)
  have hRc : IsCompact (e '' R) :=
    (isCompact_Icc.prod isCompact_Icc).image e.continuous
  have hclosure : closure (e '' W) ⊆ e '' R :=
    closure_minimal (image_mono hWR) hRc.isClosed
  have hzero : (0 : ℝ × ℝ) ∈ W := by
    change (-a < (0 : ℝ) ∧ (0 : ℝ) < a - a / 2) ∧
      (-a < (0 : ℝ) ∧ (0 : ℝ) < a - a / 2)
    constructor <;> constructor <;> linarith
  have hgfW : g =ᵐ[volume.restrict W]
      (fun q => combinedValue uR uI (pairToVec q)) :=
    ae_restrict_of_ae_restrict_of_subset hWR hgf
  have hinv : MeasurePreserving e.symm (volume.restrict (e '' W)) (volume.restrict W) :=
    (pairToVec_measurePreserving.restrict_image_emb e.toMeasurableEquiv.measurableEmbedding W).symm
      e.toMeasurableEquiv
  refine ⟨e '' W, e.isOpenMap _ (isOpen_Ioo.prod isOpen_Ioo), ?_,
    hRc.of_isClosed_subset isClosed_closure hclosure, hclosure.trans hRU,
    fun v => g (e.symm v), ?_, ?_⟩
  · exact ⟨0, hzero, pairToVec.map_zero⟩
  · apply (hgc.mono hWR).comp e.symm.continuous.continuousOn
    rintro v ⟨q, hq, rfl⟩
    simpa using hq
  · filter_upwards [hinv.quasiMeasurePreserving.ae hgfW] with v hv
    change g (e.symm v) = combinedValue uR uI (e (e.symm v)) at hv
    simpa only [e.apply_symm_apply] using hv

/-- A real weak-Hessian field has a real continuous local representative as well. -/
theorem exists_local_continuous_real_halfCube (Q : TriadicCube 2)
    (hcenter : cubeCenter Q = 0)
    (u : H1Function (scaledOpenCubeSet Q (1 / 2)))
    (H : HasWeakHessianOn (scaledOpenCubeSet Q (1 / 2)) u) :
    ∃ W : Set (Vec 2), IsOpen W ∧ (0 : Vec 2) ∈ W ∧ IsCompact (closure W) ∧
      closure W ⊆ scaledOpenCubeSet Q (1 / 2) ∧
      ∃ g : Vec 2 → ℝ, ContinuousOn g W ∧ g =ᵐ[volume.restrict W] u.toFun := by
  obtain ⟨W, hWo, hzero, hWc, hWU, g, hgc, hgf⟩ :=
    exists_local_continuous_pair_halfCube Q hcenter u u H H
  refine ⟨W, hWo, hzero, hWc, hWU, fun v => (g v).re,
    Complex.continuous_re.comp_continuousOn hgc, ?_⟩
  filter_upwards [hgf] with v hv
  rw [hv, combinedValue_re]

end GapFamily.Analytic.WeakHessianContinuousGradient
