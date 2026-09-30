import BTZEntropy.Analytic.ReferenceInversionKernel
import BTZEntropy.Analytic.ContourKernel
import Mathlib.Analysis.Calculus.Deriv.Support

/-!
# Uniform integrability of the smoothing transform on vertical contours

Two ordinary integrations by parts give a quadratic Fourier bound. The tilted
kernel and its second derivative have one fixed compact support, and their
derivative mass is uniformly bounded on every compact interval of real tilts.
-/

noncomputable section

open MeasureTheory Set
open scoped FourierTransform ContDiff

namespace BTZEntropy

private theorem norm_fourier_le (f : ℝ → ℂ) (x : ℝ) :
    ‖𝓕 f x‖ ≤ ∫ u : ℝ, ‖f u‖ := by
  exact VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _

private theorem fourier_second_deriv (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    𝓕 (deriv (deriv (f : ℝ → ℂ))) x =
      (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) ^ 2 * 𝓕 (f : ℝ → ℂ) x := by
  have hf1 : Integrable (deriv (f : ℝ → ℂ)) := (SchwartzMap.derivCLM ℂ ℂ f).integrable
  have hf2 : Integrable (deriv (deriv (f : ℝ → ℂ))) :=
    (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ f)).integrable
  have hd1 : Differentiable ℝ (deriv (f : ℝ → ℂ)) :=
    (SchwartzMap.derivCLM ℂ ℂ f).differentiable
  have h1 := congrFun (Real.fourier_deriv f.integrable f.differentiable hf1) x
  have h2 := congrFun (Real.fourier_deriv hf1 hd1 hf2) x
  rw [h1] at h2
  simpa only [smul_eq_mul, pow_two, mul_assoc] using h2

theorem sq_mul_norm_complexKernelTransform_le (φ : SmoothKernel) (β t : ℝ) :
    t ^ 2 * ‖complexKernelTransform φ (saddleContour β t)‖ ≤
      ∫ u : ℝ, ‖deriv (deriv (tiltedKernelSchwartz φ β : ℝ → ℂ)) u‖ := by
  let f := tiltedKernelSchwartz φ β
  let x := -(t / (2 * Real.pi))
  have h := norm_fourier_le (deriv (deriv (f : ℝ → ℂ))) x
  rw [fourier_second_deriv f x, norm_mul, norm_pow] at h
  have hc : ‖2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)‖ ^ 2 = t ^ 2 := by
    dsimp [x]
    simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, Complex.norm_I, mul_one, abs_neg, abs_div,
      abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [mul_div_cancel₀ _ (by positivity : 2 * Real.pi ≠ 0), sq_abs]
  rw [hc] at h
  simpa only [complexKernelTransform_eq_fourierInv, Real.fourierInv_eq_fourier_neg, f, x] using h

private theorem second_deriv_tiltedKernel (φ : SmoothKernel) (β u : ℝ) :
    deriv (deriv (tiltedKernelSchwartz φ β : ℝ → ℂ)) u =
      ((deriv (deriv φ) u + 2 * β * deriv φ u + β ^ 2 * φ u : ℝ) : ℂ) *
        Complex.exp ((β : ℂ) * (u : ℂ)) := by
  have hφ : Differentiable ℝ φ := φ.smooth.differentiable (by norm_num)
  have hφ' : Differentiable ℝ (deriv φ) :=
    ((contDiff_infty_iff_deriv.mp φ.smooth).2).differentiable (by norm_num)
  have he (v : ℝ) : HasDerivAt
      (fun x : ℝ => Complex.exp ((β : ℂ) * (x : ℂ)))
      (Complex.exp ((β : ℂ) * (v : ℂ)) * (β : ℂ)) v := by
    simpa using (((hasDerivAt_id v).ofReal_comp).const_mul (β : ℂ)).cexp
  have h1 : deriv (fun v : ℝ => (φ v : ℂ) * Complex.exp ((β : ℂ) * (v : ℂ))) =
      fun v => ((deriv φ v + β * φ v : ℝ) : ℂ) *
        Complex.exp ((β : ℂ) * (v : ℂ)) := by
    funext v
    convert ((hφ v).hasDerivAt.ofReal_comp.mul (he v)).deriv using 1 <;>
      push_cast <;> ring
  rw [tiltedKernelSchwartz_coe, h1]
  have hg := ((hφ' u).hasDerivAt.add ((hφ u).hasDerivAt.const_mul β)).ofReal_comp
  convert (hg.mul (he u)).deriv using 1 <;>
    simp only [Pi.add_apply] <;> push_cast <;> ring

private theorem continuous_second_deriv_tiltedKernel (φ : SmoothKernel) :
    Continuous (fun p : ℝ × ℝ =>
      deriv (deriv (tiltedKernelSchwartz φ p.1 : ℝ → ℂ)) p.2) := by
  simp only [second_deriv_tiltedKernel]
  have h0 : Continuous φ := φ.smooth.continuous
  have h1 : Continuous (deriv φ) := by
    simpa only [iteratedDeriv_one] using φ.smooth.continuous_iteratedDeriv 1 (by norm_num)
  have h2 : Continuous (deriv (deriv φ)) := by
    simpa only [show (2 : ℕ) = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one,
      iteratedDeriv_zero] using φ.smooth.continuous_iteratedDeriv 2 (by norm_num)
  fun_prop

private theorem second_deriv_tiltedKernel_eq_zero (φ : SmoothKernel) (β u : ℝ)
    (hu : u ∉ tsupport φ) :
    deriv (deriv (tiltedKernelSchwartz φ β : ℝ → ℂ)) u = 0 := by
  have hsup : tsupport (tiltedKernelSchwartz φ β : ℝ → ℂ) ⊆ tsupport φ := by
    change tsupport (fun u : ℝ => (φ u : ℂ) * Complex.exp ((β : ℂ) * (u : ℂ))) ⊆ _
    exact tsupport_mul_subset_left.trans (tsupport_comp_subset (g := Complex.ofReal) (by simp) φ)
  apply image_eq_zero_of_notMem_tsupport
  intro h
  exact hu (hsup (tsupport_deriv_subset (tsupport_deriv_subset h)))

private theorem exists_pos_bound_second_deriv_integral (φ : SmoothKernel) (L U : ℝ) :
    ∃ C > 0, ∀ β ∈ Icc L U,
      (∫ u : ℝ, ‖deriv (deriv (tiltedKernelSchwartz φ β : ℝ → ℂ)) u‖) ≤ C := by
  have hc : ContinuousOn
      (fun β : ℝ => ∫ u : ℝ, ‖deriv (deriv (tiltedKernelSchwartz φ β : ℝ → ℂ)) u‖)
      (Icc L U) := by
    apply continuousOn_integral_of_compact_support φ.compactSupport
      (continuous_second_deriv_tiltedKernel φ).norm.continuousOn
    intro β u _ hu
    rw [second_deriv_tiltedKernel_eq_zero φ β u hu, norm_zero]
  obtain ⟨C, hC, hb⟩ := (isCompact_Icc.image_of_continuousOn hc).isBounded.exists_pos_norm_le
  refine ⟨C, hC, fun β hβ => ?_⟩
  exact (le_abs_self _).trans (hb _ ⟨β, hβ, rfl⟩)

/-- The actual vertical kernel transform has one finite `L¹` bound on any
compact real interval, with no sign restriction on the interval endpoints. -/
theorem exists_pos_bound_integral_norm_complexKernelTransform
    (φ : SmoothKernel) (L U : ℝ) :
    ∃ M > 0, ∀ β ∈ Icc L U,
      (∫ t : ℝ, ‖complexKernelTransform φ (saddleContour β t)‖) ≤ M := by
  obtain ⟨C0, hC0, hb0⟩ := complexKernelTransform_contour_bounded φ L U
  obtain ⟨C2, hC2, hb2⟩ := exists_pos_bound_second_deriv_integral φ L U
  let J : ℝ := ∫ t : ℝ, (1 + t ^ 2)⁻¹
  have hJ : 0 ≤ J := integral_nonneg fun _ => by positivity
  refine ⟨(C0 + C2) * J + 1, by positivity, ?_⟩
  intro β hβ
  have hmajor : ∀ t : ℝ, ‖complexKernelTransform φ (saddleContour β t)‖ ≤
      (C0 + C2) * (1 + t ^ 2)⁻¹ := by
    intro t
    have h0 := hb0 β hβ t
    have h2 := (sq_mul_norm_complexKernelTransform_le φ β t).trans (hb2 β hβ)
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 1 + t ^ 2)).mpr
    nlinarith
  have hm : Integrable (fun t : ℝ => (C0 + C2) * (1 + t ^ 2)⁻¹) := by
    simpa only [one_pow] using
      (integrable_contour_majorant (by norm_num : (0 : ℝ) < 1)).const_mul (C0 + C2)
  calc
    _ ≤ ∫ t : ℝ, (C0 + C2) * (1 + t ^ 2)⁻¹ :=
      integral_mono (integrable_complexKernelTransform_contour φ β).norm hm hmajor
    _ = (C0 + C2) * J := by rw [integral_const_mul]
    _ ≤ _ := by linarith

end BTZEntropy
