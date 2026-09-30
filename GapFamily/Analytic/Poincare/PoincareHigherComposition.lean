import GapFamily.Analytic.Geometry.HeightAwareComposition
import GapFamily.Analytic.Poincare.PoincareHigherAction
import GapFamily.Analytic.Poincare.Seed.PoincareSeedHigher

noncomputable section
namespace GapFamily.Analytic.PoincareHigherComposition
open UpperHalfPlane PoincareActionGradient PoincareSeedGradient
  PoincareTermGradient PoincareTermRegularity PoincareSeedHigher
  HeightAwareComposition
open scoped MatrixGroups

/-- The explicit finite partition coefficient for actual transformed zero-energy seeds. -/
def termDerivativeConstant (n : ℕ) (S : ℝ) (J : ℤ) (M : ℝ) : ℝ :=
  heightCompositionConstant n
    (fun k => seedDerivativeConstant k S J * (1 + M) ^ k)

theorem termDerivativeConstant_nonneg (n : ℕ) {S : ℝ} (hS : 0 ≤ S)
    (J : ℤ) {M : ℝ} (hM : 0 ≤ M) : 0 ≤ termDerivativeConstant n S J M := by
  apply heightCompositionConstant_nonneg
  intro k _hk
  exact mul_nonneg (seedDerivativeConstant_nonneg k hS J) (pow_nonneg (by linarith) k)

/-- The actual translated seed retains a single image-height power at every derivative order.
The negative outer powers cancel the positive inner factors in each genuine partition. -/
theorem norm_iteratedFDeriv_translatedSeed_le (n : ℕ) (J : ℤ) {s : ℂ} {S M : ℝ}
    (hs : ‖s‖ ≤ S) (γ : SL(2, ℤ)) (τ : UpperHalfPlane)
    (hM : (γ • τ : UpperHalfPlane).im ≤ M) :
    ‖iteratedFDeriv ℝ n (translatedSeed J s γ) τ‖ ≤
      termDerivativeConstant n S J M * (γ • τ : UpperHalfPlane).im ^ s.re / τ.im ^ n := by
  let A : ℕ → ℝ := fun k => seedDerivativeConstant k S J * (1 + M) ^ k
  have hS : 0 ≤ S := (norm_nonneg s).trans hs
  have hM0 : 0 ≤ M := (γ • τ : UpperHalfPlane).im_pos.le.trans hM
  have hf : ContDiffAt ℝ n (rawSeed J s) (modularAction γ τ) := by
    simpa only [modularAction_apply] using contDiffAt_rawSeed (n := n) J s (γ • τ)
  have hA (k : ℕ) (_hk : k ≤ n) : 0 ≤ A k :=
    mul_nonneg (seedDerivativeConstant_nonneg k hS J) (pow_nonneg (by linarith) k)
  have houter (k : ℕ) (_hk : k ≤ n) :
      ‖iteratedFDeriv ℝ k (rawSeed J s) (modularAction γ τ)‖ ≤
        A k * (γ • τ : UpperHalfPlane).im ^ (s.re - (k : ℝ)) := by
    simpa only [A, modularAction_apply] using
      norm_iteratedFDeriv_rawSeed_le_of_height_le k J hs (γ • τ) hM
  have hinner (j : ℕ) (hj : 1 ≤ j) (_hjn : j ≤ n) :
      ‖iteratedFDeriv ℝ j (modularAction γ) τ‖ ≤
        (j.factorial : ℝ) * (γ • τ : UpperHalfPlane).im / τ.im ^ j :=
    norm_iteratedFDeriv_modularAction_le γ τ j hj
  exact norm_iteratedFDeriv_comp_height n hf (contDiffAt_modularAction γ τ)
    A (γ • τ : UpperHalfPlane).im τ.im s.re (γ • τ : UpperHalfPlane).im_pos
    τ.im_pos hA houter hinner

/-- The bound is for the existing canonical quotient-term function, with every
nonnegative derivative order and every complex spectral parameter allowed. -/
theorem norm_iteratedFDeriv_term_le (n : ℕ) (J : ℤ) {s : ℂ} {S M : ℝ}
    (hs : ‖s‖ ≤ S) (q : CuspCoset) (τ : UpperHalfPlane)
    (hM : (q.out • τ : UpperHalfPlane).im ≤ M) :
    ‖iteratedFDeriv ℝ n (term J s q) τ‖ ≤
      termDerivativeConstant n S J M * (q.out • τ : UpperHalfPlane).im ^ s.re / τ.im ^ n :=
  norm_iteratedFDeriv_translatedSeed_le n J hs q.out τ hM

end GapFamily.Analytic.PoincareHigherComposition
