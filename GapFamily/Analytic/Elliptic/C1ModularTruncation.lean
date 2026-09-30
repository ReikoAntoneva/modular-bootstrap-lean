import GapFamily.Analytic.Modular.ModularFormTruncationCore
import GapFamily.Analytic.Foundation.FormTruncationLp

noncomputable section
namespace GapFamily.Analytic.C1ModularForm
open Set Filter MeasureTheory UpperHalfPlane ModularGradient FormTruncation
open scoped Topology ContDiff MatrixGroups

/-- The actual invariant height cutoff applied to an arbitrary C1 field. -/
def truncateC1 (n : ℕ) (F : ℂ → ℂ) (z : ℂ) : ℂ := truncationMultiplier n z * F z

theorem contDiffOn_truncateC1 {F : ℂ → ℂ} (hF : ContDiffOn ℝ 1 F upperHalfPlaneSet) (n : ℕ) :
    ContDiffOn ℝ 1 (truncateC1 n F) upperHalfPlaneSet :=
  ((truncationMultiplier_contDiffOn n).of_le (by simp)).mul hF

theorem truncateC1_invariant {F : ℂ → ℂ}
    (hinv : ∀ γ : SL(2, ℤ), ∀ τ : UpperHalfPlane, F (γ • τ : UpperHalfPlane) = F τ)
    (n : ℕ) (γ : SL(2, ℤ)) (τ : UpperHalfPlane) :
    truncateC1 n F (γ • τ : UpperHalfPlane) = truncateC1 n F τ := by
  simp only [truncateC1, truncationMultiplier_invariant, hinv]

theorem truncateC1_eq_on_fd (n : ℕ) (F : ℂ → ℂ) {τ : UpperHalfPlane} (hτ : τ ∈ ModularGroup.fd) :
    truncateC1 n F τ = lowProfile n τ.im * F τ := by
  rw [truncateC1, truncationMultiplier_eq_on_fd n hτ]

theorem truncateC1_zero_above (n : ℕ) (F : ℂ → ℂ) (τ : UpperHalfPlane)
    (hτ : τ ∈ ModularGroup.fd) (ht : 2 * scale n ≤ τ.im) : truncateC1 n F τ = 0 := by
  rw [truncateC1_eq_on_fd n F hτ, lowProfile_eq_zero_of_ge n ht, zero_mul]

theorem truncateC1_value_ae (n : ℕ) (F : ℂ → ℂ) :
    (fun τ : UpperHalfPlane => truncateC1 n F τ) =ᵐ[modularMeasure]
      fun τ => lowProfile n τ.im * F τ := by
  filter_upwards [ae_mem_fdo] with τ hτ
  exact truncateC1_eq_on_fd n F (ModularGroup.fdo_subset_fd hτ)

theorem continuous_C1_value {F : ℂ → ℂ} (hF : ContDiffOn ℝ 1 F upperHalfPlaneSet) :
    Continuous (fun τ : UpperHalfPlane => F τ) :=
  hF.continuousOn.comp_continuous UpperHalfPlane.continuous_coe (fun τ => τ.im_pos)

theorem continuous_C1_directional {F : ℂ → ℂ} (hF : ContDiffOn ℝ 1 F upperHalfPlaneSet) (v : ℂ) :
    Continuous (directional F v) := by
  have hD := (hF.continuousOn_fderiv_of_isOpen isOpen_upperHalfPlaneSet le_rfl).clm_apply
    (continuousOn_const (c := v))
  exact (Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im).mul
    (hD.comp_continuous UpperHalfPlane.continuous_coe (fun τ => τ.im_pos))

theorem truncateC1_directional_ae {F : ℂ → ℂ}
    (hF : ContDiffOn ℝ 1 F upperHalfPlaneSet) (n : ℕ) (v : ℂ) :
    directional (truncateC1 n F) v =ᵐ[modularMeasure]
      fun τ : UpperHalfPlane => lowProfile n τ.im * directional F v τ -
        (τ.im : ℂ) * (v.im • deriv (highProfile n) τ.im) * F τ := by
  let G : ℂ → ℂ := fun z => lowProfile n z.im * F z
  have hg : ContDiffOn ℝ 1 G upperHalfPlaneSet :=
    ((((lowProfile_contDiff n).comp Complex.imCLM.contDiff).of_le (by simp)).contDiffOn).mul hF
  have heq : (fun τ : UpperHalfPlane => truncateC1 n F τ) =ᵐ[modularMeasure] (fun τ => G τ) :=
    truncateC1_value_ae n F
  have hdir := modularDirectional_ae_eq
    ((contDiffOn_truncateC1 hF n).continuousOn.mono (fun _ hz => im_pos_of_mem_modularInterior hz))
    (hg.continuousOn.mono (fun _ hz => im_pos_of_mem_modularInterior hz)) heq v
  apply hdir.trans
  apply Eventually.of_forall
  intro τ
  have hl : DifferentiableAt ℝ (fun z : ℂ => lowProfile n z.im) τ :=
    (((lowProfile_contDiff n).comp Complex.imCLM.contDiff).differentiable (by simp)) τ
  have hd := (((lowProfile_contDiff n).differentiable (by simp)) τ.im).hasFDerivAt.comp
    (τ : ℂ) Complex.imCLM.hasFDerivAt
  have hdv : fderiv ℝ (fun z : ℂ => lowProfile n z.im) τ v =
      -(v.im • deriv (highProfile n) τ.im) := by
    change fderiv ℝ (lowProfile n ∘ Complex.im) τ v = _
    rw [hd.fderiv]
    change fderiv ℝ (lowProfile n) τ.im v.im = _
    rw [fderiv_eq_smul_deriv]
    have hdlo : deriv (lowProfile n) τ.im = -deriv (highProfile n) τ.im := deriv_const_sub 1
    rw [hdlo, smul_neg]
  have hFd : DifferentiableAt ℝ F (τ : ℂ) :=
    (hF.differentiableOn (by norm_num) τ τ.im_pos).differentiableAt (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)
  change (τ.im : ℂ) * fderiv ℝ G τ v = _
  rw [show G = (fun z : ℂ => lowProfile n z.im) * F by rfl, fderiv_mul hl hFd]
  simp only [add_apply, smul_apply, smul_eq_mul, hdv, directional, UpperHalfPlane.coe_im]
  ring

theorem truncateC1_memLp_value {F : ℂ → ℂ} (hF : ContDiffOn ℝ 1 F upperHalfPlaneSet)
    (hf : MemLp (fun τ : UpperHalfPlane => F τ) 2 modularMeasure) (n : ℕ) :
    MemLp (fun τ : UpperHalfPlane => truncateC1 n F τ) 2 modularMeasure := by
  apply hf.of_le (continuous_C1_value (contDiffOn_truncateC1 hF n)).aestronglyMeasurable
  filter_upwards [truncateC1_value_ae n F] with τ hτ
  rw [hτ, norm_mul]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (norm_lowProfile_le_one n τ.im) (norm_nonneg (F τ))

/-- A common quantitative majorant for the actual cutoff derivative and its limit error. -/
theorem truncateC1_directional_bound {F : ℂ → ℂ} (hF : ContDiffOn ℝ 1 F upperHalfPlaneSet)
    (v : ℂ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ᵐ τ : UpperHalfPlane ∂modularMeasure,
      ‖directional (truncateC1 n F) v τ‖ ≤ ‖directional F v τ‖ + C * ‖F τ‖ ∧
      ‖directional (truncateC1 n F) v τ - directional F v τ‖ ≤ 2 * ‖directional F v τ‖ + C * ‖F τ‖ := by
  obtain ⟨B, hB, hb⟩ := highProfile_weighted_deriv_bound
  refine ⟨B * ‖v.im‖, mul_nonneg hB (norm_nonneg _), ?_⟩
  intro n
  filter_upwards [truncateC1_directional_ae hF n v] with τ hτ
  have hcoef : ‖(τ.im : ℂ) * (v.im • deriv (highProfile n) τ.im)‖ ≤ B * ‖v.im‖ := by
    have he : (τ.im : ℂ) * (v.im • deriv (highProfile n) τ.im) =
        (v.im : ℂ) * ((τ.im : ℂ) * deriv (highProfile n) τ.im) := by
      simp only [Complex.real_smul]; ring
    rw [he, norm_mul, Complex.norm_real]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hb n τ.im τ.im_pos) (norm_nonneg v.im)
  have hbase : ‖lowProfile n τ.im * directional F v τ‖ ≤ ‖directional F v τ‖ := by
    rw [norm_mul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (norm_lowProfile_le_one n τ.im) (norm_nonneg _)
  have hc : ‖(τ.im : ℂ) * (v.im • deriv (highProfile n) τ.im) * F τ‖ ≤ B * ‖v.im‖ * ‖F τ‖ := by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)
  have hn : ‖directional (truncateC1 n F) v τ‖ ≤ ‖directional F v τ‖ + B * ‖v.im‖ * ‖F τ‖ := by
    rw [hτ]
    exact (norm_sub_le _ _).trans (add_le_add hbase hc)
  refine ⟨hn, ?_⟩
  exact (norm_sub_le _ _).trans (by linarith)

theorem truncateC1_memLp_directional {F : ℂ → ℂ} (hF : ContDiffOn ℝ 1 F upperHalfPlaneSet)
    (hf : MemLp (fun τ : UpperHalfPlane => F τ) 2 modularMeasure) (v : ℂ)
    (hd : MemLp (directional F v) 2 modularMeasure) (n : ℕ) :
    MemLp (directional (truncateC1 n F) v) 2 modularMeasure := by
  obtain ⟨C, hC, hb⟩ := truncateC1_directional_bound hF v
  apply (hd.norm.add (hf.norm.const_mul C)).of_le
    (continuous_C1_directional (contDiffOn_truncateC1 hF n) v).aestronglyMeasurable
  filter_upwards [hb n] with τ hτ
  simpa only [Pi.add_apply, Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (mul_nonneg hC (norm_nonneg _)))] using hτ.1

end GapFamily.Analytic.C1ModularForm
