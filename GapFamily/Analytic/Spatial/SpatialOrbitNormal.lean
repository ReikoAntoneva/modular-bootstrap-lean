import GapFamily.Analytic.Spatial.SpatialOrbitSummable
import GapFamily.Analytic.Spatial.SpatialPointKernelCovariance
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
Explicit joint local normal convergence of the literal spatial point-kernel
series. The summable majorant is fixed at the center of the neighborhood.
-/

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open Set Filter UpperHalfPlane
open scoped Topology MatrixGroups

/-- Increasing the real part of the exponent decreases the kernel norm. -/
theorem pointKernel_norm_le_real_exponent {σ : ℝ} {s : ℂ}
    (hσs : σ ≤ s.re) (z w : UpperHalfPlane) :
    ‖pointKernel s z w‖ ≤ ‖pointKernel (σ : ℂ) z w‖ := by
  rw [norm_pointKernel_eq_realPart, norm_pointKernel_real_exponent,
    norm_pointKernel_real_exponent]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (pointParameter_ge_one z.im_pos w.im_pos)
      (neg_le_neg hσs)) (by norm_num)

/-- Moving both spatial points uses two uniform factors of 8^σ. -/
theorem pointKernel_orbit_norm_joint_bound {σ : ℝ} (hσ : 0 ≤ σ) {s : ℂ}
    (hσs : σ ≤ s.re) (z₀ z w₀ w : UpperHalfPlane)
    (hz : ‖(z : ℂ) - (z₀ : ℂ)‖ ≤ z₀.im / 2)
    (hw : ‖(w : ℂ) - (w₀ : ℂ)‖ ≤ w₀.im / 2) (γ : SL(2, ℤ)) :
    ‖pointKernel s z (γ • w : UpperHalfPlane)‖ ≤
      (64 : ℝ) ^ σ * ‖pointKernel (σ : ℂ) z₀ (γ • w₀ : UpperHalfPlane)‖ := by
  have hmove (v : UpperHalfPlane) :
      pointKernel (σ : ℂ) z₀ (γ • v : UpperHalfPlane) =
        pointKernel (σ : ℂ) (γ⁻¹ • z₀ : UpperHalfPlane) v := by
    simpa only [smul_inv_smul] using
      pointKernel_modular_smul (σ : ℂ) γ (γ⁻¹ • z₀) v
  have hright : ‖pointKernel (σ : ℂ) z₀ (γ • w : UpperHalfPlane)‖ ≤
      (8 : ℝ) ^ σ * ‖pointKernel (σ : ℂ) z₀ (γ • w₀ : UpperHalfPlane)‖ := by
    rw [hmove w, hmove w₀, pointKernel_symm (σ : ℂ) (γ⁻¹ • z₀ : UpperHalfPlane) w,
      pointKernel_symm (σ : ℂ) (γ⁻¹ • z₀ : UpperHalfPlane) w₀]
    exact (pointKernel_norm_local_comparison hσ w₀ w (γ⁻¹ • z₀) hw).1
  calc
    _ ≤ ‖pointKernel (σ : ℂ) z (γ • w : UpperHalfPlane)‖ :=
      pointKernel_norm_le_real_exponent hσs _ _
    _ ≤ (8 : ℝ) ^ σ * ‖pointKernel (σ : ℂ) z₀ (γ • w : UpperHalfPlane)‖ :=
      (pointKernel_norm_local_comparison hσ z₀ z (γ • w) hz).1
    _ ≤ (8 : ℝ) ^ σ * ((8 : ℝ) ^ σ *
        ‖pointKernel (σ : ℂ) z₀ (γ • w₀ : UpperHalfPlane)‖) :=
      mul_le_mul_of_nonneg_left hright (Real.rpow_nonneg (by norm_num) _)
    _ = _ := by
      rw [← mul_assoc, ← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 8)
        (by norm_num : (0 : ℝ) ≤ 8)]
      norm_num

/-- A concrete summable majorant on a neighborhood of the exponent and both points. -/
theorem exists_pointKernel_orbit_joint_majorant (s₀ : ℂ) (hs₀ : 1 < s₀.re)
    (z₀ w₀ : UpperHalfPlane) :
    ∃ r σ : ℝ, 0 < r ∧ 1 < σ ∧
      Summable (fun γ : SL(2, ℤ) =>
        (64 : ℝ) ^ σ * ‖pointKernel (σ : ℂ) z₀ (γ • w₀ : UpperHalfPlane)‖) ∧
      ∀ (s : ℂ) (z w : UpperHalfPlane), ‖s - s₀‖ < r →
        ‖(z : ℂ) - (z₀ : ℂ)‖ < z₀.im / 2 →
        ‖(w : ℂ) - (w₀ : ℂ)‖ < w₀.im / 2 →
        ∀ γ : SL(2, ℤ), ‖pointKernel s z (γ • w : UpperHalfPlane)‖ ≤
          (64 : ℝ) ^ σ * ‖pointKernel (σ : ℂ) z₀ (γ • w₀ : UpperHalfPlane)‖ := by
  let σ : ℝ := (1 + s₀.re) / 2
  let r : ℝ := (s₀.re - 1) / 2
  have hσ : 1 < σ := by dsimp [σ]; linarith
  have hr : 0 < r := by dsimp [r]; linarith
  refine ⟨r, σ, hr, hσ, (summable_norm_spatialOrbit_real σ hσ z₀ w₀).mul_left _, ?_⟩
  intro s z w hs hz hw γ
  have hre := (Complex.abs_re_le_norm (s - s₀)).trans hs.le
  simp only [Complex.sub_re] at hre
  have hσs : σ ≤ s.re := by
    have hlo := (abs_le.mp hre).1
    dsimp [σ, r] at *
    linarith
  exact pointKernel_orbit_norm_joint_bound (by linarith) hσs z₀ z w₀ w hz.le hw.le γ

/-- Finite sums converge uniformly on an actual joint neighborhood of every point
in the half-plane Re(s)>1. -/
theorem exists_pointKernel_orbit_tendstoUniformlyOn (s₀ : ℂ) (hs₀ : 1 < s₀.re)
    (z₀ w₀ : UpperHalfPlane) :
    ∃ U ∈ 𝓝 (s₀, (z₀, w₀)),
      TendstoUniformlyOn
        (fun t : Finset (SL(2, ℤ)) => fun p : ℂ × (UpperHalfPlane × UpperHalfPlane) =>
          ∑ γ ∈ t, pointKernel p.1 p.2.1 (γ • p.2.2 : UpperHalfPlane))
        (fun p => ∑' γ : SL(2, ℤ), pointKernel p.1 p.2.1 (γ • p.2.2 : UpperHalfPlane))
        atTop U := by
  obtain ⟨r, σ, hr, hσ, hsum, hbound⟩ :=
    exists_pointKernel_orbit_joint_majorant s₀ hs₀ z₀ w₀
  let U : Set (ℂ × (UpperHalfPlane × UpperHalfPlane)) :=
    {p | ‖p.1 - s₀‖ < r ∧ ‖(p.2.1 : ℂ) - (z₀ : ℂ)‖ < z₀.im / 2 ∧
      ‖(p.2.2 : ℂ) - (w₀ : ℂ)‖ < w₀.im / 2}
  have hU : U ∈ 𝓝 (s₀, (z₀, w₀)) := by
    have hopen : IsOpen U := by
      apply (isOpen_lt (continuous_fst.sub continuous_const).norm continuous_const).inter
      exact (isOpen_lt ((UpperHalfPlane.continuous_coe.comp
        (continuous_fst.comp continuous_snd)).sub continuous_const).norm
        continuous_const).inter
        (isOpen_lt ((UpperHalfPlane.continuous_coe.comp
          (continuous_snd.comp continuous_snd)).sub continuous_const).norm continuous_const)
    apply hopen.mem_nhds
    simp only [U, mem_ofPred_eq, sub_self, norm_zero]
    exact ⟨hr, half_pos z₀.im_pos, half_pos w₀.im_pos⟩
  refine ⟨U, hU, tendstoUniformlyOn_tsum hsum ?_⟩
  intro γ p hp
  exact hbound p.1 p.2.1 p.2.2 hp.1 hp.2.1 hp.2.2 γ

end GapFamily.Analytic.SpatialPoint
