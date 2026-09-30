import GapFamily.Analytic.Elliptic.C1PeriodizationGraphBasic
import GapFamily.Analytic.Modular.ModularPositivePeriodization

noncomputable section
namespace GapFamily.Analytic.C1Periodization
open Set Filter MeasureTheory UpperHalfPlane ModularGradient
open scoped ContDiff MatrixGroups Topology

lemma norm_seed_le_cutoff {K : Set ℂ} {χ ψ : ℂ → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (hs : tsupport ψ ⊆ K) (hone : EqOn χ 1 K)
    (hb : ∀ z, ‖ψ z‖ ≤ C) (z : ℂ) : ‖ψ z‖ ≤ C * Complex.normSq (χ z) := by
  by_cases hz : z ∈ K
  · simpa only [hone hz, Pi.one_apply, Complex.normSq_one, mul_one] using hb z
  · rw [image_eq_zero_of_notMem_tsupport (fun h => hz (hs h)), norm_zero]
    exact mul_nonneg hC (Complex.normSq_nonneg _)

lemma norm_periodization_le_cutoff {K : Set ℂ} {χ ψ : ℂ → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ upperHalfPlaneSet)
    (hs : tsupport ψ ⊆ K) (hone : EqOn χ 1 K) (hb : ∀ z, ‖ψ z‖ ≤ C)
    (τ : UpperHalfPlane) :
    ‖modularPeriodization ψ τ‖ ≤ C * (modularPeriodization (normSquareSeed χ) τ).re := by
  have hrho := summable_normSquareSeed_orbit hcχ hsχ τ
  have hnorm : Summable (fun γ : SL(2, ℤ) => ‖ψ (γ • τ : UpperHalfPlane)‖) :=
    (hrho.mul_left C).of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun _ => norm_seed_le_cutoff hC hs hone hb _)
  have ht := hnorm.tsum_le_tsum (fun _ => norm_seed_le_cutoff hC hs hone hb _)
    (hrho.mul_left C)
  rw [tsum_mul_left] at ht
  rw [modularPeriodization_coe, norm_mul, modularPeriodization_normSquareSeed_re]
  norm_num only [norm_div, norm_one, Complex.norm_ofNat]
  have hn := norm_tsum_le_tsum_norm hnorm
  nlinarith

lemma frame_comp_le_cutoff {K : Set ℂ} {χ ψ : ℂ → ℂ} {C H : ℝ}
    (hC : 0 ≤ C) (hH : 0 ≤ H) (hψ : ContDiff ℝ 1 ψ)
    (hs : tsupport ψ ⊆ K) (hone : EqOn χ 1 K)
    (hKheight : ∀ z ∈ K, z.im ≤ H) (hb : ∀ z, ‖fderiv ℝ ψ z‖ ≤ C)
    (γ : SL(2, ℤ)) (τ : UpperHalfPlane) (v : ℂ) :
    τ.im * ‖fderiv ℝ (ψ ∘ rawModularAction γ) τ v‖ ≤
      (H * C * ‖v‖) * Complex.normSq (χ (γ • τ : UpperHalfPlane)) := by
  rw [fderiv_comp_rawModularAction γ τ ((hψ.differentiable (by simp)).differentiableAt)]
  by_cases hz : ((γ • τ : UpperHalfPlane) : ℂ) ∈ K
  · have hχ : χ (γ • τ : UpperHalfPlane) = 1 := hone hz
    rw [hχ, Complex.normSq_one, mul_one]
    have hD := (fderiv ℝ ψ (γ • τ : UpperHalfPlane)).le_opNorm
      ((1 / UpperHalfPlane.denom γ τ ^ 2) * v)
    have hscale : τ.im * ‖1 / UpperHalfPlane.denom γ τ ^ 2‖ = (γ • τ).im := by
      rw [ModularGroup.im_smul_eq_div_normSq, Complex.normSq_eq_norm_sq,
        norm_div, norm_one, norm_pow]
      ring
    calc
      _ ≤ τ.im * (‖fderiv ℝ ψ (γ • τ : UpperHalfPlane)‖ *
          ‖(1 / UpperHalfPlane.denom γ τ ^ 2) * v‖) :=
        mul_le_mul_of_nonneg_left hD τ.im_pos.le
      _ ≤ τ.im * (C * ‖(1 / UpperHalfPlane.denom γ τ ^ 2) * v‖) := by gcongr; exact hb _
      _ = (γ • τ).im * C * ‖v‖ := by rw [norm_mul, ← hscale]; ring
      _ ≤ H * C * ‖v‖ := by gcongr; exact hKheight _ hz
  · have hd : fderiv ℝ ψ ((γ • τ : UpperHalfPlane) : ℂ) = 0 :=
      fderiv_of_notMem_tsupport ℝ (fun h => hz (hs h))
    rw [hd, zero_apply, norm_zero, mul_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg hH hC) (norm_nonneg _)) (Complex.normSq_nonneg _)

lemma norm_directional_periodization_le_cutoff {K : Set ℂ} {χ ψ : ℂ → ℂ} {C H : ℝ}
    (hC : 0 ≤ C) (hH : 0 ≤ H) (hψ : ContDiff ℝ 1 ψ)
    (hcψ : HasCompactSupport ψ) (hsψ : tsupport ψ ⊆ upperHalfPlaneSet)
    (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ upperHalfPlaneSet)
    (hs : tsupport ψ ⊆ K) (hone : EqOn χ 1 K)
    (hKheight : ∀ z ∈ K, z.im ≤ H) (hb : ∀ z, ‖fderiv ℝ ψ z‖ ≤ C)
    (τ : UpperHalfPlane) (v : ℂ) :
    ‖directional (modularPeriodization ψ) v τ‖ ≤
      (H * C * ‖v‖) * (modularPeriodization (normSquareSeed χ) τ).re := by
  obtain ⟨S, hS, _⟩ := exists_finset_fderiv_periodization hψ hcψ hsψ τ
  have hrho := summable_normSquareSeed_orbit hcχ hsχ τ
  have hbS := Finset.sum_le_sum (fun γ (_ : γ ∈ S) =>
    frame_comp_le_cutoff hC hH hψ hs hone hKheight hb γ τ v)
  have hsum := hrho.sum_le_tsum S (fun γ _ => Complex.normSq_nonneg _)
  have hnon : 0 ≤ H * C * ‖v‖ := by positivity
  simp only [← Finset.mul_sum] at hbS
  have hb' := hbS.trans (mul_le_mul_of_nonneg_left hsum hnon)
  rw [directional, hS, norm_mul, Complex.norm_of_nonneg τ.im_pos.le, norm_mul,
    modularPeriodization_normSquareSeed_re]
  norm_num only [norm_div, norm_one, Complex.norm_ofNat]
  have hn := norm_sum_le S (fun γ => fderiv ℝ (ψ ∘ rawModularAction γ) (τ : ℂ) v)
  nlinarith [mul_le_mul_of_nonneg_left hn τ.im_pos.le]

end GapFamily.Analytic.C1Periodization
