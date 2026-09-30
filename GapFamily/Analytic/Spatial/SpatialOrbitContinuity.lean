import GapFamily.Analytic.Spatial.SpatialOrbitNormal

/-!
Joint spatial continuity and ordinary measurability of the actual half-normalized
orbit kernel in its convergence half-plane.
-/

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open Set Filter UpperHalfPlane MeasureTheory
open scoped Topology MatrixGroups

private theorem continuous_pointKernel_orbit_term (s : ℂ) (γ : SL(2, ℤ)) :
    Continuous (fun p : UpperHalfPlane × UpperHalfPlane =>
      pointKernel s p.1 (γ • p.2 : UpperHalfPlane)) := by
  have hγ : Continuous (fun w : UpperHalfPlane => (γ • w : UpperHalfPlane)) := by
    change Continuous (fun w : UpperHalfPlane => ((γ : SL(2, ℝ)) : GL (Fin 2) ℝ) • w)
    exact continuous_const_smul _
  apply continuous_iff_continuousAt.mpr
  intro p
  have hf : ContinuousAt (fun q : ℂ × ℂ => pointKernel s q.1 q.2)
      ((p.1 : ℂ), ((γ • p.2 : UpperHalfPlane) : ℂ)) :=
    (pointKernel_contDiffAt s p.1.im_pos (γ • p.2 : UpperHalfPlane).im_pos).continuousAt
  have hm : ContinuousAt (fun q : UpperHalfPlane × UpperHalfPlane =>
      ((q.1 : ℂ), ((γ • q.2 : UpperHalfPlane) : ℂ))) p :=
    ((UpperHalfPlane.continuous_coe.comp continuous_fst).prodMk
      (UpperHalfPlane.continuous_coe.comp (hγ.comp continuous_snd))).continuousAt
  exact hf.comp (f := fun q : UpperHalfPlane × UpperHalfPlane =>
    ((q.1 : ℂ), ((γ • q.2 : UpperHalfPlane) : ℂ))) hm

/-- The literal normalized orbit kernel is jointly continuous in its two points. -/
theorem continuous_spatialOrbitKernel (s : ℂ) (hs : 1 < s.re) :
    Continuous (fun p : UpperHalfPlane × UpperHalfPlane => spatialOrbitKernel s p.1 p.2) := by
  simp_rw [spatialOrbitKernel_eq_half_tsum_right]
  apply continuous_const.mul
  apply continuous_iff_continuousAt.mpr
  intro p₀
  obtain ⟨r, σ, hr, hσ, hsum, hbound⟩ :=
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
  have hcont : ContinuousOn
      (fun p : UpperHalfPlane × UpperHalfPlane =>
        ∑' γ : SL(2, ℤ), pointKernel s p.1 (γ • p.2 : UpperHalfPlane)) V := by
    apply continuousOn_tsum (fun γ => (continuous_pointKernel_orbit_term s γ).continuousOn)
      hsum
    intro γ p hp
    exact hbound s p.1 p.2 (by simpa only [sub_self, norm_zero] using hr) hp.1 hp.2 γ
  exact hcont.continuousAt hV

theorem measurable_spatialOrbitKernel (s : ℂ) (hs : 1 < s.re) :
    Measurable (fun p : UpperHalfPlane × UpperHalfPlane => spatialOrbitKernel s p.1 p.2) :=
  (continuous_spatialOrbitKernel s hs).measurable

theorem stronglyMeasurable_spatialOrbitKernel (s : ℂ) (hs : 1 < s.re) :
    StronglyMeasurable (fun p : UpperHalfPlane × UpperHalfPlane =>
      spatialOrbitKernel s p.1 p.2) :=
  (continuous_spatialOrbitKernel s hs).stronglyMeasurable

theorem aestronglyMeasurable_spatialOrbitKernel (s : ℂ) (hs : 1 < s.re)
    (μ : Measure (UpperHalfPlane × UpperHalfPlane)) :
    AEStronglyMeasurable (fun p : UpperHalfPlane × UpperHalfPlane =>
      spatialOrbitKernel s p.1 p.2) μ :=
  (stronglyMeasurable_spatialOrbitKernel s hs).aestronglyMeasurable

end GapFamily.Analytic.SpatialPoint
