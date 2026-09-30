import GapFamily.Analytic.Modular.Geometry.ModularSeamEnergy
import GapFamily.Analytic.Modular.Periodization.ModularPeriodizationAction

/-!
# Pointwise mixed gradient covariance under the actual modular action

All derivatives are real derivatives. The conjugate-linear/linear pairing
uses both real coordinate directions and assumes no holomorphy of either field.
-/

noncomputable section
open scoped ComplexConjugate

namespace GapFamily.Analytic

/-- Two arbitrary real-linear derivatives have a conformally scaled mixed pairing. -/
theorem conj_apply_mul_add_conj_apply_mul_I
    (A B : ℂ →L[ℝ] ℂ) (c : ℂ) :
    conj (A c) * B c + conj (A (c * Complex.I)) * B (c * Complex.I) =
      (‖c‖ ^ 2 : ℝ) • (conj (A 1) * B 1 + conj (A Complex.I) * B Complex.I) := by
  have hL (L : ℂ →L[ℝ] ℂ) (z : ℂ) :
      L z = z.re • L 1 + z.im • L Complex.I := by
    have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
      simpa only [Complex.real_smul, mul_one] using (Complex.re_add_im z).symm
    conv_lhs => rw [hz, map_add, map_smul, map_smul]
  rw [hL A c, hL A (c * Complex.I), hL B c, hL B (c * Complex.I)]
  apply Complex.ext <;>
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.smul_re, Complex.smul_im, smul_eq_mul, Complex.mul_re, Complex.mul_im,
      Complex.conj_re, Complex.conj_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
      zero_sub, add_zero] <;> ring

end GapFamily.Analytic

namespace GapFamily.Analytic.ModularGradient
open Set Filter MeasureTheory UpperHalfPlane
open scoped ContDiff MatrixGroups Topology

/-- The literal fractional-linear action has the same real derivative as its upper-half-plane germ. -/
theorem hasFDerivAt_rawModularAction (γ : SL(2, ℤ)) (τ : UpperHalfPlane) :
    HasFDerivAt (rawModularAction γ)
      ((ContinuousLinearMap.toSpanSingleton ℂ
        (1 / UpperHalfPlane.denom γ τ ^ 2)).restrictScalars ℝ) τ := by
  apply (hasFDerivAt_modularAction γ τ).congr_of_eventuallyEq
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with z hz
  simpa only [UpperHalfPlane.ofComplex_apply_of_im_pos hz] using
    rawModularAction_coe γ (⟨z, hz⟩ : UpperHalfPlane)

/-- The real chain rule for a test field pulled back by the actual raw action. -/
theorem fderiv_comp_rawModularAction (γ : SL(2, ℤ)) (τ : UpperHalfPlane)
    {ψ : ℂ → ℂ} (hψ : DifferentiableAt ℝ ψ (γ • τ : UpperHalfPlane)) (v : ℂ) :
    fderiv ℝ (ψ ∘ rawModularAction γ) τ v =
      fderiv ℝ ψ (γ • τ : UpperHalfPlane)
        ((1 / UpperHalfPlane.denom γ τ ^ 2) * v) := by
  have hψ' : HasFDerivAt ψ (fderiv ℝ ψ (γ • τ : UpperHalfPlane))
      (rawModularAction γ τ) := by
    simpa only [rawModularAction_coe] using hψ.hasFDerivAt
  have hd := congrArg (fun L : ℂ →L[ℝ] ℂ => L v)
    (hψ'.comp (τ : ℂ) (hasFDerivAt_rawModularAction γ τ)).fderiv
  change fderiv ℝ (ψ ∘ rawModularAction γ) τ v =
    fderiv ℝ ψ (γ • τ : UpperHalfPlane)
      (v * (1 / UpperHalfPlane.denom γ τ ^ 2)) at hd
  simpa only [mul_comm] using hd

/-- The complete mixed Euclidean pairing transforms by the genuine squared conformal scale. -/
theorem euclideanMixedGradient_modularAction (F : smoothCore) (γ : SL(2, ℤ))
    (τ : UpperHalfPlane) {ψ : ℂ → ℂ}
    (hψ : DifferentiableAt ℝ ψ (γ • τ : UpperHalfPlane)) :
    conj (fderiv ℝ F.val τ 1) * fderiv ℝ (ψ ∘ rawModularAction γ) τ 1 +
      conj (fderiv ℝ F.val τ Complex.I) * fderiv ℝ (ψ ∘ rawModularAction γ) τ Complex.I =
      ((‖1 / UpperHalfPlane.denom γ τ ^ 2‖ ^ 2 : ℝ) : ℂ) *
        (conj (fderiv ℝ F.val (γ • τ : UpperHalfPlane) 1) *
            fderiv ℝ ψ (γ • τ : UpperHalfPlane) 1 +
          conj (fderiv ℝ F.val (γ • τ : UpperHalfPlane) Complex.I) *
            fderiv ℝ ψ (γ • τ : UpperHalfPlane) Complex.I) := by
  rw [fderiv_core_modularAction F γ τ 1, fderiv_core_modularAction F γ τ Complex.I,
    fderiv_comp_rawModularAction γ τ hψ 1,
    fderiv_comp_rawModularAction γ τ hψ Complex.I, mul_one]
  simpa only [Complex.real_smul] using
    conj_apply_mul_add_conj_apply_mul_I (fderiv ℝ F.val (γ • τ : UpperHalfPlane))
      (fderiv ℝ ψ (γ • τ : UpperHalfPlane)) (1 / UpperHalfPlane.denom γ τ ^ 2)

/-- Hyperbolic frame factors cancel the conformal scale in the actual mixed pairing. -/
theorem directionalMixedGradient_modularAction (F : smoothCore) (γ : SL(2, ℤ))
    (τ : UpperHalfPlane) {ψ : ℂ → ℂ}
    (hψ : DifferentiableAt ℝ ψ (γ • τ : UpperHalfPlane)) :
    conj (directional F.val 1 τ) * directional (ψ ∘ rawModularAction γ) 1 τ +
      conj (directional F.val Complex.I τ) * directional (ψ ∘ rawModularAction γ) Complex.I τ =
      conj (directional F.val 1 (γ • τ)) * directional ψ 1 (γ • τ) +
        conj (directional F.val Complex.I (γ • τ)) * directional ψ Complex.I (γ • τ) := by
  have hscale : ((τ.im : ℂ) ^ 2) * ((‖1 / UpperHalfPlane.denom γ τ ^ 2‖ ^ 2 : ℝ) : ℂ) =
      (((γ • τ : UpperHalfPlane).im : ℂ) ^ 2) := by
    have hr : τ.im ^ 2 * ‖1 / UpperHalfPlane.denom γ τ ^ 2‖ ^ 2 =
        (γ • τ : UpperHalfPlane).im ^ 2 := by
      rw [ModularGroup.im_smul_eq_div_normSq, Complex.normSq_eq_norm_sq,
        norm_div, norm_one, norm_pow]
      ring
    exact_mod_cast hr
  have hmix := euclideanMixedGradient_modularAction F γ τ hψ
  calc
    _ = ((τ.im : ℂ) ^ 2) *
        (conj (fderiv ℝ F.val τ 1) * fderiv ℝ (ψ ∘ rawModularAction γ) τ 1 +
          conj (fderiv ℝ F.val τ Complex.I) *
            fderiv ℝ (ψ ∘ rawModularAction γ) τ Complex.I) := by
      simp only [directional, map_mul, Complex.conj_ofReal]
      ring
    _ = (((γ • τ : UpperHalfPlane).im : ℂ) ^ 2) *
        (conj (fderiv ℝ F.val (γ • τ : UpperHalfPlane) 1) *
            fderiv ℝ ψ (γ • τ : UpperHalfPlane) 1 +
          conj (fderiv ℝ F.val (γ • τ : UpperHalfPlane) Complex.I) *
            fderiv ℝ ψ (γ • τ : UpperHalfPlane) Complex.I) := by
      rw [hmix, ← mul_assoc, hscale]
    _ = _ := by
      simp only [directional, map_mul, Complex.conj_ofReal]
      ring

end GapFamily.Analytic.ModularGradient
