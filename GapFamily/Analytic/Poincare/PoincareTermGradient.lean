import GapFamily.Analytic.Poincare.PoincareActionGradient
import GapFamily.Analytic.Poincare.Seed.PoincareSeedGradient

/-!
Actual spatial first derivatives of zero-energy Poincare seeds, with a summable
operator-norm majorant on compact upper-half-plane sets and bounded exponent
strips inside Re(s)>1. No differentiation of an infinite sum is asserted here.
-/

noncomputable section
namespace GapFamily.Analytic.PoincareTermGradient
open Set Filter PoincareActionGradient PoincareSeedGradient
open scoped Topology MatrixGroups

/-- An ambient coordinate function whose restriction is the literal transformed seed. -/
def translatedSeed (J : ℤ) (s : ℂ) (γ : SL(2, ℤ)) : ℂ → ℂ :=
  rawSeed J s ∘ modularAction γ

@[simp] theorem translatedSeed_apply (J : ℤ) (s : ℂ) (γ : SL(2, ℤ))
    (τ : UpperHalfPlane) :
    translatedSeed J s γ τ = complexPointSeed 0 J s (γ • τ) := by
  simp only [translatedSeed, Function.comp_apply, modularAction_apply,
    rawSeed_eq_complexPointSeed]

/-- Differentiability is proved at every actual upper-half-plane point. -/
theorem differentiableAt_translatedSeed (J : ℤ) (s : ℂ) (γ : SL(2, ℤ))
    (τ : UpperHalfPlane) : DifferentiableAt ℝ (translatedSeed J s γ) (τ : ℂ) := by
  have hF : DifferentiableAt ℝ (rawSeed J s) (modularAction γ τ) := by
    simpa only [modularAction_apply] using differentiableAt_rawSeed J s (γ • τ)
  exact hF.comp (τ : ℂ) (ModularGradient.hasFDerivAt_modularAction γ τ).differentiableAt

/-- The literal transformed seed has the claimed hyperbolic-frame bound.
This holds for every complex exponent, with no positivity restriction needed. -/
theorem translatedSeed_frame_bound (J : ℤ) (s : ℂ) (γ : SL(2, ℤ))
    (τ : UpperHalfPlane) (v : ℂ) :
    τ.im * ‖fderiv ℝ (translatedSeed J s γ) (τ : ℂ) v‖ ≤
      (‖s‖ + 2 * Real.pi * |(J : ℝ)| * (γ • τ).im) * (γ • τ).im ^ s.re * ‖v‖ :=
  frame_derivative_comp_le (rawSeed J s) γ τ
    (differentiableAt_rawSeed J s (γ • τ)) _
    (frame_norm_fderiv_rawSeed_le J s (γ • τ)) v

/-- The actual quotient term, extended to ordinary complex coordinates. -/
def term (J : ℤ) (s : ℂ) (q : CuspCoset) : ℂ → ℂ :=
  translatedSeed J s q.out

@[simp] theorem term_apply (J : ℤ) (s : ℂ) (q : CuspCoset) (τ : UpperHalfPlane) :
    term J s q τ = complexPoincareTerm 0 J s τ q := by
  rw [complexPoincareTerm_out]
  exact translatedSeed_apply J s q.out τ

/-- This is the canonical actual term composed with the ambient upper-half-plane map. -/
theorem term_eq_complexPoincareTerm_ofComplex (J : ℤ) (s : ℂ) (q : CuspCoset) :
    term J s q = fun z : ℂ => complexPoincareTerm 0 J s (UpperHalfPlane.ofComplex z) q := by
  funext z
  rw [complexPoincareTerm_out]
  exact rawSeed_eq_complexPointSeed J s (q.out • UpperHalfPlane.ofComplex z)

theorem differentiableAt_term (J : ℤ) (s : ℂ) (q : CuspCoset)
    (τ : UpperHalfPlane) : DifferentiableAt ℝ (term J s q) (τ : ℂ) :=
  differentiableAt_translatedSeed J s q.out τ

/-- A common summable bound for all actual first-derivative operators on a
compact spatial set and a bounded parameter strip strictly inside Re(s)>1. -/
theorem exists_compact_fderiv_majorant (J : ℤ) {a b S : ℝ}
    (ha : 1 < a) (hab : a ≤ b) (hS : 0 ≤ S)
    {K : Set UpperHalfPlane} (hK : IsCompact K) :
    ∃ u : CuspCoset → ℝ, Summable u ∧ (∀ q, 0 ≤ u q) ∧
      ∀ (q : CuspCoset) (s : ℂ) (τ : UpperHalfPlane),
        a ≤ s.re → s.re ≤ b → ‖s‖ ≤ S → τ ∈ K →
        ‖fderiv ℝ (term J s q) (τ : ℂ)‖ ≤ u q := by
  obtain ⟨u, hu, hu0, hub⟩ := exists_seed_frame_majorant J ha hab hS hK
  obtain ⟨A, B, hB, hstrip⟩ := UpperHalfPlane.subset_verticalStrip_of_isCompact hK
  refine ⟨fun q => B⁻¹ * u q, hu.mul_left _,
    fun q => mul_nonneg (inv_nonneg.mpr hB.le) (hu0 q), ?_⟩
  intro q s τ hsa hsb hsS hτ
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (inv_nonneg.mpr hB.le) (hu0 q))
  intro v
  have hframe : τ.im * ‖fderiv ℝ (term J s q) (τ : ℂ) v‖ ≤ u q * ‖v‖ :=
    (translatedSeed_frame_bound J s q.out τ v).trans
      (mul_le_mul_of_nonneg_right (hub q s τ hsa hsb hsS hτ) (norm_nonneg v))
  have hlower : B ≤ τ.im := (hstrip hτ).2
  have hbound : B * ‖fderiv ℝ (term J s q) (τ : ℂ) v‖ ≤ u q * ‖v‖ :=
    (mul_le_mul_of_nonneg_right hlower (norm_nonneg _)).trans hframe
  calc
    _ ≤ (u q * ‖v‖) / B := (le_div_iff₀ hB).mpr (by simpa only [mul_comm] using hbound)
    _ = (B⁻¹ * u q) * ‖v‖ := by ring

/-- In particular, every fixed exponent in Re(s)>1 has a common summable
first-derivative bound on every compact upper-half-plane set. -/
theorem exists_compact_fderiv_majorant_fixed (J : ℤ) {s : ℂ} (hs : 1 < s.re)
    {K : Set UpperHalfPlane} (hK : IsCompact K) :
    ∃ u : CuspCoset → ℝ, Summable u ∧ (∀ q, 0 ≤ u q) ∧
      ∀ (q : CuspCoset) (τ : UpperHalfPlane), τ ∈ K →
        ‖fderiv ℝ (term J s q) (τ : ℂ)‖ ≤ u q := by
  obtain ⟨u, hu, hu0, hb⟩ := exists_compact_fderiv_majorant J hs le_rfl (norm_nonneg s) hK
  exact ⟨u, hu, hu0, fun q τ hτ => hb q s τ le_rfl le_rfl le_rfl hτ⟩

end GapFamily.Analytic.PoincareTermGradient
