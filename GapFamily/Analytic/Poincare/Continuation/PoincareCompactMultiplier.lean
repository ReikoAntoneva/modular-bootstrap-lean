import GapFamily.Analytic.Poincare.PoincareAnalytic
import Mathlib.MeasureTheory.Function.LocallyIntegrable

noncomputable section
namespace GapFamily.Analytic.PoincareWeak

open MeasureTheory Set Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups UpperHalfPlane

theorem continuous_complexPointSeed_zero (J : ℤ) (s : ℂ) :
    Continuous (complexPointSeed 0 J s) := by
  have hp : Continuous (fun τ : UpperHalfPlane => (τ.im : ℂ) ^ s) := by
    apply continuous_iff_continuousAt.mpr
    intro τ
    exact (Complex.continuousAt_ofReal_cpow_const τ.im s (Or.inr τ.im_pos.ne')).comp
      UpperHalfPlane.continuous_im.continuousAt
  change Continuous (fun τ : UpperHalfPlane => complexPointSeed 0 J s τ)
  simp only [complexPointSeed, mul_zero, zero_mul, zero_add]
  exact hp.mul (Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp (continuous_const.mul UpperHalfPlane.continuous_re)).mul
      continuous_const))

theorem continuous_complexPoincareTerm_zero (J : ℤ) (s : ℂ) (q : CuspCoset) :
    Continuous (fun τ : UpperHalfPlane => complexPoincareTerm 0 J s τ q) := by
  simp only [complexPoincareTerm_out]
  have hg : Continuous (fun τ : UpperHalfPlane => q.out • τ) :=
    continuous_const_smul (toGL (SpecialLinearGroup.map (Int.castRingHom ℝ) q.out))
  exact (continuous_complexPointSeed_zero J s).comp hg

/-- Compact multipliers supported inside the upper half-plane remove the arbitrary
extension of `ofComplex` outside its source. -/
theorem continuous_compact_mul_ofComplex (ψ : ℂ → ℂ) (hψ : Continuous ψ)
    (hsupp : tsupport ψ ⊆ UpperHalfPlane.upperHalfPlaneSet)
    (F : UpperHalfPlane → ℂ) (hF : Continuous F) :
    Continuous (fun z : ℂ => ψ z * F (UpperHalfPlane.ofComplex z)) := by
  apply continuous_of_tsupport
  intro z hz
  have hzψ : z ∈ tsupport ψ := tsupport_mul_subset_left hz
  apply hψ.continuousAt.mul (hF.continuousAt.comp ?_)
  apply UpperHalfPlane.ofComplex.continuousAt
  simpa [UpperHalfPlane.ofComplex] using hsupp hzψ

theorem hasCompactSupport_compact_mul_ofComplex (ψ : ℂ → ℂ) (hc : HasCompactSupport ψ)
    (F : UpperHalfPlane → ℂ) :
    HasCompactSupport (fun z : ℂ => ψ z * F (UpperHalfPlane.ofComplex z)) :=
  hc.mul_right

theorem integrable_compact_mul_ofComplex (ψ : ℂ → ℂ) (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) (hsupp : tsupport ψ ⊆ UpperHalfPlane.upperHalfPlaneSet)
    (F : UpperHalfPlane → ℂ) (hF : Continuous F) :
    Integrable (fun z : ℂ => ψ z * F (UpperHalfPlane.ofComplex z)) :=
  (continuous_compact_mul_ofComplex ψ hψ hsupp F hF).integrable_of_hasCompactSupport
    (hasCompactSupport_compact_mul_ofComplex ψ hc F)

theorem continuous_star_test_complexPoincareTerm (ψ : ℂ → ℂ) (hψ : Continuous ψ)
    (hsupp : tsupport ψ ⊆ UpperHalfPlane.upperHalfPlaneSet)
    (J : ℤ) (s : ℂ) (q : CuspCoset) :
    Continuous (fun z : ℂ => star (ψ z) *
      complexPoincareTerm 0 J s (UpperHalfPlane.ofComplex z) q) :=
  continuous_compact_mul_ofComplex (fun z => star (ψ z)) hψ.star
    ((tsupport_comp_subset (star_zero ℂ) ψ).trans hsupp)
    _ (continuous_complexPoincareTerm_zero J s q)

theorem hasCompactSupport_star_test_complexPoincareTerm
    (ψ : ℂ → ℂ) (hc : HasCompactSupport ψ) (J : ℤ) (s : ℂ) (q : CuspCoset) :
    HasCompactSupport (fun z : ℂ => star (ψ z) *
      complexPoincareTerm 0 J s (UpperHalfPlane.ofComplex z) q) :=
  (hc.comp_left (star_zero ℂ)).mul_right

theorem integrable_star_test_complexPoincareTerm (ψ : ℂ → ℂ) (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) (hsupp : tsupport ψ ⊆ UpperHalfPlane.upperHalfPlaneSet)
    (J : ℤ) (s : ℂ) (q : CuspCoset) :
    Integrable (fun z : ℂ => star (ψ z) *
      complexPoincareTerm 0 J s (UpperHalfPlane.ofComplex z) q) :=
  (continuous_star_test_complexPoincareTerm ψ hψ hsupp J s q).integrable_of_hasCompactSupport
    (hasCompactSupport_star_test_complexPoincareTerm ψ hc J s q)

end GapFamily.Analytic.PoincareWeak
