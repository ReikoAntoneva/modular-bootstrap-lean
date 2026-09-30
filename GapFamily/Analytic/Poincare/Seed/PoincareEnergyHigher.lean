import GapFamily.Analytic.Poincare.Seed.PoincareEnergySeedHigher
import GapFamily.Analytic.Poincare.PoincareHigherAction
import GapFamily.Analytic.Poincare.PoincareHigherRow
import GapFamily.Analytic.Geometry.HeightAwareComposition

noncomputable section
namespace GapFamily.Analytic.PoincareEnergyHigher
open Set UpperHalfPlane PoincareEnergySeedBasic PoincareActionGradient
  PoincareTermRegularity PoincareHigherComposition PoincareHigherRow
  HeightAwareComposition
open scoped MatrixGroups

/-- The exact finite partition coefficient for actual energy-difference terms. -/
def differenceTermDerivativeConstant (n : ℕ) (S : ℝ) (E : ℂ) (J : ℤ) (M : ℝ) : ℝ :=
  heightCompositionConstant n (fun k => differenceSeedDerivativeConstant k S E J M)

theorem differenceTermDerivativeConstant_nonneg (n : ℕ) {S M : ℝ}
    (hS : 0 ≤ S) (E : ℂ) (J : ℤ) (hM : 0 ≤ M) :
    0 ≤ differenceTermDerivativeConstant n S E J M := by
  apply heightCompositionConstant_nonneg
  intro k _hk
  exact differenceSeedDerivativeConstant_nonneg k hS E J hM

/-- Every actual transformed difference derivative retains the extra orbital-height power. -/
theorem norm_iteratedFDeriv_differenceTerm_le (n : ℕ) (E : ℂ) (J : ℤ)
    {s : ℂ} {S M : ℝ} (hs : ‖s‖ ≤ S) (q : CuspCoset) (τ : UpperHalfPlane)
    (hM : (q.out • τ : UpperHalfPlane).im ≤ M) :
    ‖iteratedFDeriv ℝ n (differenceTerm E J s q) τ‖ ≤
      differenceTermDerivativeConstant n S E J M *
        (q.out • τ : UpperHalfPlane).im ^ (s.re + 1) / τ.im ^ n := by
  let A : ℕ → ℝ := fun k => differenceSeedDerivativeConstant k S E J M
  have hS : 0 ≤ S := (norm_nonneg s).trans hs
  have hM0 : 0 ≤ M := (q.out • τ : UpperHalfPlane).im_pos.le.trans hM
  have hf : ContDiffAt ℝ n (rawDifferenceSeed E J s) (modularAction q.out τ) := by
    simpa only [modularAction_apply] using
      contDiffAt_rawDifferenceSeed (n := n) E J s (q.out • τ)
  have hA (k : ℕ) (_hk : k ≤ n) : 0 ≤ A k :=
    differenceSeedDerivativeConstant_nonneg k hS E J hM0
  have houter (k : ℕ) (_hk : k ≤ n) :
      ‖iteratedFDeriv ℝ k (rawDifferenceSeed E J s) (modularAction q.out τ)‖ ≤
        A k * (q.out • τ : UpperHalfPlane).im ^ (s.re + 1 - (k : ℝ)) := by
    simpa only [A, modularAction_apply] using
      norm_iteratedFDeriv_rawDifferenceSeed_le k E J hs (q.out • τ) hM
  have hinner (j : ℕ) (hj : 1 ≤ j) (_hjn : j ≤ n) :
      ‖iteratedFDeriv ℝ j (modularAction q.out) τ‖ ≤
        (j.factorial : ℝ) * (q.out • τ : UpperHalfPlane).im / τ.im ^ j :=
    norm_iteratedFDeriv_modularAction_le q.out τ j hj
  exact norm_iteratedFDeriv_comp_height n hf (contDiffAt_modularAction q.out τ)
    A (q.out • τ : UpperHalfPlane).im τ.im (s.re + 1) (q.out • τ : UpperHalfPlane).im_pos
    τ.im_pos hA houter hinner

/-- A genuine summable compact majorant for every actual derivative of the
energy-difference term; the extra height permits exactly Re(s)>0. -/
theorem exists_compact_iteratedFDeriv_difference_majorant (n : ℕ) (E : ℂ) (J : ℤ)
    {s : ℂ} (hs : 0 < s.re) {K : Set UpperHalfPlane} (hK : IsCompact K) :
    ∃ u : CuspCoset → ℝ, Summable u ∧ (∀ q, 0 ≤ u q) ∧
      ∀ (q : CuspCoset) (τ : UpperHalfPlane), τ ∈ K →
        ‖iteratedFDeriv ℝ n
          (fun z : ℂ => complexPoincareDifferenceTerm E J s (UpperHalfPlane.ofComplex z) q) τ‖ ≤ u q := by
  obtain ⟨M, hM, u, hu, hu0, hub⟩ :=
    exists_compact_height_power_div_majorant n (show 1 < s.re + 1 by linarith) hK
  let C := differenceTermDerivativeConstant n ‖s‖ E J M
  have hC : 0 ≤ C := differenceTermDerivativeConstant_nonneg n (norm_nonneg s) E J hM.le
  refine ⟨fun q => C * u q, hu.mul_left C,
    fun q => mul_nonneg hC (hu0 q), ?_⟩
  intro q τ hτ
  rw [← differenceTerm_eq_complexPoincareDifferenceTerm_ofComplex]
  calc
    _ ≤ C * (q.out • τ : UpperHalfPlane).im ^ (s.re + 1) / τ.im ^ n :=
      norm_iteratedFDeriv_differenceTerm_le n E J le_rfl q τ (hub q τ hτ).1
    _ = C * ((q.out • τ : UpperHalfPlane).im ^ (s.re + 1) / τ.im ^ n) := by ring
    _ ≤ C * u q := mul_le_mul_of_nonneg_left (hub q τ hτ).2 hC

end GapFamily.Analytic.PoincareEnergyHigher
