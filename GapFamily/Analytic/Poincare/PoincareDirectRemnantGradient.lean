import GapFamily.Analytic.Poincare.PoincareTermRegularity
import GapFamily.Analytic.Cusp.Fourier.CuspFourierCutoffProfile
import GapFamily.Analytic.Modular.Geometry.ModularTruncatedTransportBasic

/-!
# The actual complementary direct seed has a bounded frame gradient

Smoothness supplies an operator-norm bound on the compact truncated closed
fundamental domain. Above the cutoff transition the literal field has a zero
germ, so its actual derivative vanishes. No spectral half-plane restriction
or infinite-series regularity assumption is needed.
-/

noncomputable section
namespace GapFamily.Analytic.PoincareGreen
open Set Filter MeasureTheory UpperHalfPlane ModularGradient PoincareSeedGradient
open scoped ContDiff Topology

/-- The literal complementary-cutoff direct seed in ambient coordinates. -/
def directRemnant (J : ℤ) (s : ℂ) (z : ℂ) : ℂ :=
  ((1 - CuspFourierCutoff.cutoff z.im : ℝ) : ℂ) * rawSeed J s z

/-- The actual raw seed is real smooth throughout positive height. -/
theorem contDiffOn_rawSeed (J : ℤ) (s : ℂ) :
    ContDiffOn ℝ ∞ (rawSeed J s) upperHalfPlaneSet := by
  intro z hz
  exact (PoincareTermRegularity.contDiffAt_rawSeed (n := ∞) J s ⟨z, hz⟩).contDiffWithinAt

/-- The actual direct complement is smooth for every complex spectral exponent. -/
theorem contDiffOn_directRemnant (J : ℤ) (s : ℂ) :
    ContDiffOn ℝ ∞ (directRemnant J s) upperHalfPlaneSet := by
  have hc : ContDiff ℝ ∞ (fun z : ℂ => ((1 - CuspFourierCutoff.cutoff z.im : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      (contDiff_const.sub (CuspFourierCutoff.contDiff_cutoff.comp Complex.imCLM.contDiff))
  exact hc.contDiffOn.mul (contDiffOn_rawSeed J s)

theorem differentiableAt_directRemnant (J : ℤ) (s : ℂ) (τ : UpperHalfPlane) :
    DifferentiableAt ℝ (directRemnant J s) (τ : ℂ) :=
  ((contDiffOn_directRemnant J s).differentiableOn (by simp) τ τ.im_pos).differentiableAt
    (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)

theorem continuousOn_fderiv_directRemnant (J : ℤ) (s : ℂ) :
    ContinuousOn (fderiv ℝ (directRemnant J s)) upperHalfPlaneSet :=
  (contDiffOn_directRemnant J s).continuousOn_fderiv_of_isOpen
    isOpen_upperHalfPlaneSet (by simp)

/-- At and above the terminal cutoff height the literal direct complement is zero. -/
theorem directRemnant_eq_zero_of_three_le (J : ℤ) (s : ℂ) {z : ℂ} (hz : 3 ≤ z.im) :
    directRemnant J s z = 0 := by
  simp only [directRemnant, CuspFourierCutoff.cutoff_eq_one hz, sub_self,
    Complex.ofReal_zero, zero_mul]

/-- Strictly above the cutoff, the actual ambient derivative is the zero map. -/
theorem fderiv_directRemnant_eq_zero_of_three_lt (J : ℤ) (s : ℂ)
    {z : ℂ} (hz : 3 < z.im) : fderiv ℝ (directRemnant J s) z = 0 := by
  have heq : directRemnant J s =ᶠ[𝓝 z] fun _ => (0 : ℂ) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz]
      with w hw
    exact directRemnant_eq_zero_of_three_le J s hw.le
  rw [heq.fderiv_eq]
  exact (hasFDerivAt_const (0 : ℂ) z).fderiv

/-- A true frame-gradient bound on the complete closed fundamental domain, uniform in direction. -/
theorem exists_frame_bound_directRemnant (J : ℤ) (s : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : UpperHalfPlane, τ ∈ ModularGroup.fd → ∀ v : ℂ,
      τ.im * ‖fderiv ℝ (directRemnant J s) (τ : ℂ) v‖ ≤ C * ‖v‖ := by
  obtain ⟨B, hB⟩ := (isCompact_modularTruncatedTarget 3).exists_bound_of_continuousOn
    ((continuousOn_fderiv_directRemnant J s).mono
      (modularTruncatedTarget_subset_upperHalfPlane 3))
  refine ⟨3 * max B 0, by positivity, ?_⟩
  intro τ hτ v
  by_cases hy : τ.im ≤ 3
  · have hD : ‖fderiv ℝ (directRemnant J s) (τ : ℂ)‖ ≤ max B 0 :=
      (hB τ ((coe_mem_modularTruncatedTarget_iff 3 τ).mpr ⟨hτ, hy⟩)).trans (le_max_left B 0)
    calc
      _ ≤ τ.im * (‖fderiv ℝ (directRemnant J s) (τ : ℂ)‖ * ‖v‖) :=
        mul_le_mul_of_nonneg_left ((fderiv ℝ (directRemnant J s) (τ : ℂ)).le_opNorm v)
          τ.im_pos.le
      _ ≤ τ.im * (max B 0 * ‖v‖) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hD (norm_nonneg v)) τ.im_pos.le
      _ ≤ 3 * (max B 0 * ‖v‖) := mul_le_mul_of_nonneg_right hy
        (mul_nonneg (le_max_right B 0) (norm_nonneg v))
      _ = (3 * max B 0) * ‖v‖ := (mul_assoc _ _ _).symm
  · rw [fderiv_directRemnant_eq_zero_of_three_lt J s (lt_of_not_ge hy)]
    simp only [zero_apply, norm_zero, mul_zero]
    positivity

/-- The actual frame derivative is continuous as a function on the upper half-plane. -/
theorem continuous_frame_directRemnant (J : ℤ) (s : ℂ) (v : ℂ) :
    Continuous (fun τ : UpperHalfPlane =>
      (τ.im : ℂ) * fderiv ℝ (directRemnant J s) (τ : ℂ) v) := by
  have hD : Continuous (fun τ : UpperHalfPlane => fderiv ℝ (directRemnant J s) (τ : ℂ)) :=
    (continuousOn_fderiv_directRemnant J s).comp_continuous UpperHalfPlane.continuous_coe
      (fun τ => τ.im_pos)
  exact (Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im).mul
    (hD.clm_apply continuous_const)

/-- Every frame direction of the actual direct complement belongs to modular L². -/
theorem memLp_frame_directRemnant (J : ℤ) (s : ℂ) (v : ℂ) :
    MemLp (fun τ : UpperHalfPlane =>
      (τ.im : ℂ) * fderiv ℝ (directRemnant J s) (τ : ℂ) v) 2 modularMeasure := by
  obtain ⟨C, _hC, hbound⟩ := exists_frame_bound_directRemnant J s
  apply MemLp.of_bound (continuous_frame_directRemnant J s v).aestronglyMeasurable (C * ‖v‖)
  filter_upwards [ae_mem_fdo] with τ hτ
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos τ.im_pos] using
    hbound τ (ModularGroup.fdo_subset_fd hτ) v

end GapFamily.Analytic.PoincareGreen
