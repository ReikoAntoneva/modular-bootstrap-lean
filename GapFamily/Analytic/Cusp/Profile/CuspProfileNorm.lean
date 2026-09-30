import GapFamily.Analytic.Cusp.Profile.CuspProfileCore
import GapFamily.Analytic.Cusp.Profile.CuspProfileNormIntegral
import GapFamily.Analytic.Modular.Elliptic.ModularInteriorCompactWeight
import Mathlib.Analysis.Calculus.Deriv.Support

/-!
# Exact mass and energy of genuine compact scalar cusp profiles

The periodized profile belongs to the original smooth automorphic core.
Its actual value and directional representatives identify its Hilbert norms
with the ordinary weighted value and unweighted derivative integrals.
-/

noncomputable section

namespace GapFamily.Analytic

open Set MeasureTheory UpperHalfPlane ModularGradient
open scoped ContDiff

/-- The scalar mass integral converges and is the actual modular Hilbert norm. -/
theorem cuspProfileCore_value_norm_sq (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b)
    (hc : HasCompactSupport b) (hs : tsupport b ⊆ Ioi (1 : ℝ)) :
    IntegrableOn (fun y : ℝ => ‖b y‖ ^ 2 / y ^ 2) (Ioi 1) ∧
      ‖value (cuspProfileCore b hb hc hs)‖ ^ 2 =
        ∫ y : ℝ in Ioi 1, ‖b y‖ ^ 2 / y ^ 2 := by
  let F := cuspProfileCore b hb hc hs
  have hrep : (fun τ : UpperHalfPlane => F.val τ) =ᵐ[modularMeasure]
      (fun τ : UpperHalfPlane => b τ.im) :=
    (value_ae F).symm.trans (cuspProfileCore_value_ae b hb hc hs)
  have hm : MemLp (fun τ : UpperHalfPlane => b τ.im) 2 modularMeasure :=
    (memLp_congr_ae hrep).mp F.property.2.2.1
  have hi := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
  obtain ⟨hw, heq⟩ := cuspProfile_scalar_norm_integral b hb.continuous hs hi
  refine ⟨hw, ?_⟩
  rw [← core_value_integral_norm_sq]
  exact (integral_congr_ae (hrep.mono fun τ hτ => congrArg (fun z : ℂ => ‖z‖ ^ 2) hτ)).trans heq

theorem cuspProfileCore_xComponent_eq_zero (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b)
    (hc : HasCompactSupport b) (hs : tsupport b ⊆ Ioi (1 : ℝ)) :
    xComponent (cuspProfileCore b hb hc hs) = 0 := by
  change component 1 (fun F => F.property.2.2.2.1) (cuspProfileCore b hb hc hs) = 0
  apply Lp.ext
  filter_upwards [component_ae 1 (fun F => F.property.2.2.2.1) (cuspProfileCore b hb hc hs),
    cuspProfileCore_directional_ae b hb hc hs 1,
    Lp.coeFn_zero (E := ℂ) (p := 2) (μ := modularMeasure)] with τ hx hd hz
  rw [hx, hd, hz]
  simp

theorem cuspProfileCore_yComponent_ae (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b)
    (hc : HasCompactSupport b) (hs : tsupport b ⊆ Ioi (1 : ℝ)) :
    yComponent (cuspProfileCore b hb hc hs) =ᵐ[modularMeasure]
      (fun τ : UpperHalfPlane => (τ.im : ℂ) * deriv b τ.im) := by
  have h := (component_ae Complex.I (fun F => F.property.2.2.2.2)
    (cuspProfileCore b hb hc hs)).trans (cuspProfileCore_directional_ae b hb hc hs Complex.I)
  simpa only [yComponent, Complex.I_im, one_smul] using h

/-- The actual closed-frame gradient has exactly the ordinary vertical energy. -/
theorem cuspProfileCore_gradient_norm_sq (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b)
    (hc : HasCompactSupport b) (hs : tsupport b ⊆ Ioi (1 : ℝ)) :
    IntegrableOn (fun y : ℝ => ‖deriv b y‖ ^ 2) (Ioi 1) ∧
      ‖coreGradient (cuspProfileCore b hb hc hs)‖ ^ 2 =
        ∫ y : ℝ in Ioi 1, ‖deriv b y‖ ^ 2 := by
  let F := cuspProfileCore b hb hc hs
  let d : ℝ → ℂ := fun y => (y : ℂ) * deriv b y
  have hd : Continuous d := Complex.continuous_ofReal.mul (hb.continuous_deriv (by simp))
  have hsd : tsupport d ⊆ Ioi (1 : ℝ) :=
    (tsupport_mul_subset_right (f := fun y : ℝ => (y : ℂ)) (g := deriv b)).trans
      (tsupport_deriv_subset.trans hs)
  have hrep : directional F.val Complex.I =ᵐ[modularMeasure]
      (fun τ : UpperHalfPlane => d τ.im) := by
    simpa only [Complex.I_im, one_smul] using
      cuspProfileCore_directional_ae b hb hc hs Complex.I
  have hm : MemLp (fun τ : UpperHalfPlane => d τ.im) 2 modularMeasure :=
    (memLp_congr_ae hrep).mp F.property.2.2.2.2
  have hi := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
  obtain ⟨hw, heq⟩ := cuspProfile_scalar_norm_integral d hd hsd hi
  have hcancel : (fun y : ℝ => ‖d y‖ ^ 2 / y ^ 2)
      =ᵐ[volume.restrict (Ioi (1 : ℝ))] (fun y => ‖deriv b y‖ ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hyne : y ≠ 0 := ne_of_gt (zero_lt_one.trans hy)
    simp only [d, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    field_simp
  refine ⟨hw.congr hcancel, ?_⟩
  rw [coreGradient_norm_sq, cuspProfileCore_xComponent_eq_zero, norm_zero, zero_pow (by decide), zero_add]
  rw [yComponent, ← core_component_integral_norm_sq Complex.I (fun G => G.property.2.2.2.2)]
  exact (integral_congr_ae (hrep.mono fun τ hτ => congrArg (fun z : ℂ => ‖z‖ ^ 2) hτ)).trans
    (heq.trans (integral_congr_ae hcancel))

end GapFamily.Analytic
