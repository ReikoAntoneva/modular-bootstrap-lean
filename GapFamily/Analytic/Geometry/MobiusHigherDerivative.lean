import GapFamily.Analytic.Geometry.LaplacianMobiusAction
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

noncomputable section
namespace GapFamily.Analytic.MobiusHigher
open Filter UpperHalfPlane LaplacianCovariance
open scoped MatrixGroups Topology

/-- The actual Möbius derivative agrees locally with its rational denominator formula. -/
theorem deriv_rawRealModularAction_germ (γ : SL(2, ℝ)) (τ : UpperHalfPlane) :
    deriv (rawRealModularAction γ) =ᶠ[𝓝 (τ : ℂ)]
      (fun z : ℂ => 1 / UpperHalfPlane.denom (γ : GL (Fin 2) ℝ) z ^ 2) := by
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with z hz
  exact deriv_rawRealModularAction γ (⟨z, hz⟩ : UpperHalfPlane)

/-- Normalizing the rational higher derivative exposes the first-height factor
and the dimensionless lower-row ratio separately. -/
theorem norm_factorial_quotient (n : ℕ) (c d : ℂ) :
    ‖(-1 : ℂ) ^ n * ((n + 1).factorial : ℂ) * c ^ n / d ^ (n + 2)‖ =
      ((n + 1).factorial : ℝ) * ‖1 / d ^ 2‖ * ‖c / d‖ ^ n := by
  simp only [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
    one_mul, Complex.norm_natCast, div_pow, pow_add]
  ring

end GapFamily.Analytic.MobiusHigher
