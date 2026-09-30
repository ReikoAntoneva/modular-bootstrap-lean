import GapFamily.Analytic.Spatial.SpatialOrbitFirstDerivative

/-!
# Joint continuity of the actual orbit frame derivative

Joint point-kernel smoothness makes each partial derivative operator continuous.
The existing joint normal majorant controls the operator series locally, and
the actual derivative formula transfers that continuity to the orbit kernel.
-/

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open Set Filter UpperHalfPlane MeasureTheory
open scoped Topology ContDiff MatrixGroups

private theorem continuous_pointKernel_orbit_fderiv (s : ℂ) (γ : SL(2, ℤ)) :
    Continuous (fun p : UpperHalfPlane × UpperHalfPlane =>
      fderiv ℝ (fun z : ℂ => pointKernel s z (γ • p.2 : UpperHalfPlane)) (p.1 : ℂ)) := by
  have hγ : Continuous (fun w : UpperHalfPlane => (γ • w : UpperHalfPlane)) := by
    change Continuous (fun w : UpperHalfPlane => ((γ : SL(2, ℝ)) : GL (Fin 2) ℝ) • w)
    exact continuous_const_smul _
  apply continuous_iff_continuousAt.mpr
  intro p
  let w : ℂ := (γ • p.2 : UpperHalfPlane)
  have hw : 0 < w.im := (γ • p.2 : UpperHalfPlane).im_pos
  have hf : ContDiffAt ℝ ∞
      (fun q : (ℂ × ℂ) × ℂ => pointKernel s q.2 q.1.2) (((p.1 : ℂ), w), (p.1 : ℂ)) := by
    have hbase : ContDiffAt ℝ ∞ (fun q : ℂ × ℂ => pointKernel s q.1 q.2)
        ((p.1 : ℂ), w) := pointKernel_contDiffAt s p.1.im_pos hw
    have hmap : ContDiffAt ℝ ∞ (fun q : (ℂ × ℂ) × ℂ => (q.2, q.1.2))
        (((p.1 : ℂ), w), (p.1 : ℂ)) :=
      contDiffAt_snd.prodMk contDiffAt_fst.snd
    exact hbase.comp (f := fun q : (ℂ × ℂ) × ℂ => (q.2, q.1.2))
      (((p.1 : ℂ), w), (p.1 : ℂ)) hmap
  have hD : ContinuousAt
      (fun q : ℂ × ℂ => fderiv ℝ (fun z : ℂ => pointKernel s z q.2) q.1)
      ((p.1 : ℂ), w) :=
    (hf.fderiv (m := 0) (g := fun q : ℂ × ℂ => q.1) contDiffAt_fst (by simp)).continuousAt
  have hm : ContinuousAt (fun q : UpperHalfPlane × UpperHalfPlane =>
      ((q.1 : ℂ), ((γ • q.2 : UpperHalfPlane) : ℂ))) p :=
    ((UpperHalfPlane.continuous_coe.comp continuous_fst).prodMk
      (UpperHalfPlane.continuous_coe.comp (hγ.comp continuous_snd))).continuousAt
  exact hD.comp (f := fun q : UpperHalfPlane × UpperHalfPlane =>
    ((q.1 : ℂ), ((γ • q.2 : UpperHalfPlane) : ℂ))) hm

private theorem continuous_spatialOrbit_fderiv_tsum (s : ℂ) (hs : 1 < s.re) :
    Continuous (fun p : UpperHalfPlane × UpperHalfPlane =>
      ∑' γ : SL(2, ℤ),
        fderiv ℝ (fun z : ℂ => pointKernel s z (γ • p.2 : UpperHalfPlane)) (p.1 : ℂ)) := by
  apply continuous_iff_continuousAt.mpr
  intro p₀
  obtain ⟨r, σ, hr, _hσ, hsum, hbound⟩ :=
    exists_pointKernel_orbit_joint_majorant s hs p₀.1 p₀.2
  let V : Set (UpperHalfPlane × UpperHalfPlane) :=
    {p | ‖(p.1 : ℂ) - (p₀.1 : ℂ)‖ < p₀.1.im / 2 ∧
      ‖(p.2 : ℂ) - (p₀.2 : ℂ)‖ < p₀.2.im / 2}
  have hV : V ∈ 𝓝 p₀ := by
    have hopen : IsOpen V :=
      (isOpen_lt ((UpperHalfPlane.continuous_coe.comp continuous_fst).sub
        continuous_const).norm continuous_const).inter
      (isOpen_lt ((UpperHalfPlane.continuous_coe.comp continuous_snd).sub
        continuous_const).norm continuous_const)
    apply hopen.mem_nhds
    simp only [V, mem_ofPred_eq, sub_self, norm_zero]
    exact ⟨half_pos p₀.1.im_pos, half_pos p₀.2.im_pos⟩
  let C : ℝ := (2 * ‖s‖) / (p₀.1.im / 2)
  have hcont : ContinuousOn
      (fun p : UpperHalfPlane × UpperHalfPlane =>
        ∑' γ : SL(2, ℤ),
          fderiv ℝ (fun z : ℂ => pointKernel s z (γ • p.2 : UpperHalfPlane)) (p.1 : ℂ)) V := by
    apply continuousOn_tsum (fun γ => (continuous_pointKernel_orbit_fderiv s γ).continuousOn)
      (hsum.mul_left C)
    intro γ p hp
    have hval := hbound s p.1 p.2
      (by simpa only [sub_self, norm_zero] using hr) hp.1 hp.2 γ
    have hheight : p₀.1.im / 2 ≤ p.1.im := by
      have hi := (Complex.abs_im_le_norm ((p.1 : ℂ) - (p₀.1 : ℂ))).trans_lt hp.1
      simp only [Complex.sub_im] at hi
      have hlo := (abs_lt.mp hi).1
      change -(p₀.1.im / 2) < p.1.im - p₀.1.im at hlo
      linarith
    have hframe := pointKernel_frame_fderiv_norm_le s p.1.im_pos
      (γ • p.2 : UpperHalfPlane).im_pos
    have hb : (p₀.1.im / 2) *
        ‖fderiv ℝ (fun z : ℂ => pointKernel s z (γ • p.2 : UpperHalfPlane)) (p.1 : ℂ)‖ ≤
        (2 * ‖s‖) * ((64 : ℝ) ^ σ * ‖pointKernel (σ : ℂ) p₀.1 (γ • p₀.2 : UpperHalfPlane)‖) :=
      ((mul_le_mul_of_nonneg_right hheight (norm_nonneg _)).trans hframe).trans
        (mul_le_mul_of_nonneg_left hval (by positivity))
    calc
      _ ≤ ((2 * ‖s‖) * ((64 : ℝ) ^ σ *
          ‖pointKernel (σ : ℂ) p₀.1 (γ • p₀.2 : UpperHalfPlane)‖)) / (p₀.1.im / 2) :=
        (le_div_iff₀ (half_pos p₀.1.im_pos)).mpr (by simpa only [mul_comm] using hb)
      _ = _ := by dsimp [C]; ring
  exact hcont.continuousAt hV

/-- The actual first partial derivative operator is jointly continuous on the upper plane. -/
theorem continuous_spatialOrbit_fderiv_left (s : ℂ) (hs : 1 < s.re) :
    Continuous (fun p : UpperHalfPlane × UpperHalfPlane =>
      fderiv ℝ (fun z : ℂ => spatialOrbitKernel s (UpperHalfPlane.ofComplex z) p.2) (p.1 : ℂ)) := by
  have he : (fun p : UpperHalfPlane × UpperHalfPlane =>
      fderiv ℝ (fun z : ℂ => spatialOrbitKernel s (UpperHalfPlane.ofComplex z) p.2) (p.1 : ℂ)) =
      (fun p => (1 / 2 : ℂ) • ∑' γ : SL(2, ℤ),
        fderiv ℝ (fun z : ℂ => pointKernel s z (γ • p.2 : UpperHalfPlane)) (p.1 : ℂ)) := by
    funext p
    exact fderiv_spatialOrbitKernel s hs p.1 p.2
  rw [he]
  exact (continuous_spatialOrbit_fderiv_tsum s hs).const_smul (1 / 2 : ℂ)

/-- The literal hyperbolic-frame directional derivative of the actual orbit kernel. -/
def spatialOrbitFrameKernel (s : ℂ) (v : ℂ) (p : UpperHalfPlane × UpperHalfPlane) : ℂ :=
  p.1.im • fderiv ℝ (fun z : ℂ => spatialOrbitKernel s (UpperHalfPlane.ofComplex z) p.2)
    (p.1 : ℂ) v

theorem continuous_spatialOrbitFrameKernel (s : ℂ) (hs : 1 < s.re) (v : ℂ) :
    Continuous (spatialOrbitFrameKernel s v) := by
  have heval : Continuous (fun p : UpperHalfPlane × UpperHalfPlane =>
      fderiv ℝ (fun z : ℂ => spatialOrbitKernel s (UpperHalfPlane.ofComplex z) p.2)
        (p.1 : ℂ) v) :=
    (continuous_spatialOrbit_fderiv_left s hs).clm_apply continuous_const
  exact (UpperHalfPlane.continuous_im.comp continuous_fst).smul heval

theorem measurable_spatialOrbitFrameKernel (s : ℂ) (hs : 1 < s.re) (v : ℂ) :
    Measurable (spatialOrbitFrameKernel s v) :=
  (continuous_spatialOrbitFrameKernel s hs v).measurable

theorem stronglyMeasurable_spatialOrbitFrameKernel (s : ℂ) (hs : 1 < s.re) (v : ℂ) :
    StronglyMeasurable (spatialOrbitFrameKernel s v) :=
  (continuous_spatialOrbitFrameKernel s hs v).stronglyMeasurable

theorem aestronglyMeasurable_spatialOrbitFrameKernel (s : ℂ) (hs : 1 < s.re) (v : ℂ)
    (μ : Measure (UpperHalfPlane × UpperHalfPlane)) :
    AEStronglyMeasurable (spatialOrbitFrameKernel s v) μ :=
  (stronglyMeasurable_spatialOrbitFrameKernel s hs v).aestronglyMeasurable

end GapFamily.Analytic.SpatialPoint
