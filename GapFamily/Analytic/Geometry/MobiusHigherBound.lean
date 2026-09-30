import GapFamily.Analytic.Geometry.MobiusHigherDerivative
import GapFamily.Analytic.Geometry.MobiusHigherRational
import GapFamily.Analytic.Geometry.MobiusHigherGeometry
import GapFamily.Analytic.Geometry.MobiusHigherRestriction

noncomputable section
namespace GapFamily.Analytic.MobiusHigher
open Filter UpperHalfPlane LaplacianCovariance
open scoped MatrixGroups Topology

/-- The exact complex higher derivative of the actual determinant-one Möbius action. -/
theorem iteratedDeriv_succ_rawRealModularAction (γ : SL(2, ℝ)) (τ : UpperHalfPlane) (n : ℕ) :
    iteratedDeriv (n + 1) (rawRealModularAction γ) τ =
      (-1 : ℂ) ^ n * ((n + 1).factorial : ℂ) * ((γ 1 0 : ℝ) : ℂ) ^ n /
        UpperHalfPlane.denom (γ : GL (Fin 2) ℝ) τ ^ (n + 2) := by
  rw [iteratedDeriv_succ', (deriv_rawRealModularAction_germ γ τ).iteratedDeriv_eq n]
  exact iteratedDeriv_invSq_affine n (γ 1 0 : ℂ) (γ 1 1 : ℂ) τ

/-- The norm of the genuine real multilinear derivative retains the exact
transformed-height factor through the first derivative. -/
theorem norm_iteratedFDeriv_succ_rawRealModularAction_eq
    (γ : SL(2, ℝ)) (τ : UpperHalfPlane) (n : ℕ) :
    ‖iteratedFDeriv ℝ (n + 1) (rawRealModularAction γ) τ‖ =
      ((n + 1).factorial : ℝ) *
        ‖1 / UpperHalfPlane.denom (γ : GL (Fin 2) ℝ) τ ^ 2‖ *
        ‖((γ 1 0 : ℝ) : ℂ) / UpperHalfPlane.denom (γ : GL (Fin 2) ℝ) τ‖ ^ n := by
  rw [norm_iteratedFDeriv_real_eq_iteratedDeriv_of_analyticAt
    (analyticAt_rawRealModularAction γ τ), iteratedDeriv_succ_rawRealModularAction,
    norm_factorial_quotient]

/-- Every positive-order real Fréchet derivative obeys the precise factorial
height estimate needed to compose with negative powers of the image height. -/
theorem norm_iteratedFDeriv_rawRealModularAction_le
    (γ : SL(2, ℝ)) (τ : UpperHalfPlane) (n : ℕ) (hn : 1 ≤ n) :
    ‖iteratedFDeriv ℝ n (rawRealModularAction γ) τ‖ ≤
      (n.factorial : ℝ) * (γ • τ : UpperHalfPlane).im / τ.im ^ n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [norm_iteratedFDeriv_succ_rawRealModularAction_eq]
  simpa only [Nat.add_sub_cancel] using factorial_mobius_factors_le γ τ (m + 1) hn

/-- The actual integer modular action satisfies the same real higher-derivative bound. -/
theorem norm_iteratedFDeriv_rawModularAction_le
    (γ : SL(2, ℤ)) (τ : UpperHalfPlane) (n : ℕ) (hn : 1 ≤ n) :
    ‖iteratedFDeriv ℝ n (rawModularAction γ) τ‖ ≤
      (n.factorial : ℝ) * (γ • τ : UpperHalfPlane).im / τ.im ^ n := by
  exact norm_iteratedFDeriv_rawRealModularAction_le (γ : SL(2, ℝ)) τ n hn

/-- In the affine case, all derivatives of order at least two actually vanish. -/
theorem iteratedFDeriv_rawRealModularAction_eq_zero_of_bottomLeft
    (γ : SL(2, ℝ)) (τ : UpperHalfPlane) (n : ℕ) (hn : 2 ≤ n) (hc : γ 1 0 = 0) :
    iteratedFDeriv ℝ n (rawRealModularAction γ) τ = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  apply norm_eq_zero.mp
  rw [norm_iteratedFDeriv_succ_rawRealModularAction_eq]
  have hm : m ≠ 0 := by omega
  simp [hc, hm]

/-- The affine vanishing statement specializes to the existing integer action. -/
theorem iteratedFDeriv_rawModularAction_eq_zero_of_bottomLeft
    (γ : SL(2, ℤ)) (τ : UpperHalfPlane) (n : ℕ) (hn : 2 ≤ n) (hc : γ 1 0 = 0) :
    iteratedFDeriv ℝ n (rawModularAction γ) τ = 0 := by
  apply iteratedFDeriv_rawRealModularAction_eq_zero_of_bottomLeft
    (γ : SL(2, ℝ)) τ n hn
  simpa using congrArg (fun a : ℤ => (a : ℝ)) hc

end GapFamily.Analytic.MobiusHigher
