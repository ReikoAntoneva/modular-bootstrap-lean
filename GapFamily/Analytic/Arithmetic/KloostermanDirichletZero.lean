import GapFamily.Analytic.Arithmetic.KloostermanDirichlet
import Mathlib.Data.Nat.Totient

/-!
# The all-zero Kloosterman Dirichlet coefficient

At zero input and output frequency every arithmetic phase is one, so the
coefficient is Euler's totient. The resulting identities use genuinely
convergent Dirichlet sums in the half-plane `1 < s.re`.
-/

noncomputable section

namespace GapFamily.Analytic

/-- Every unit contributes one when both arithmetic frequencies vanish. -/
theorem kloostermanSum_zero_zero_eq_totient (k : ℕ) :
    kloostermanSum 0 0 k = (Nat.totient (k + 1) : ℂ) := by
  simp [kloostermanSum, kloostermanPhase, ZMod.card_units_eq_totient]

/-- The zero coefficient agrees with the convention `Nat.totient 0 = 0`. -/
theorem kloostermanCoefficient_zero_zero (c : ℕ) :
    kloostermanCoefficient 0 0 c = (Nat.totient c : ℂ) := by
  cases c with
  | zero => simp
  | succ k => simpa using kloostermanSum_zero_zero_eq_totient k

/-- The all-zero Dirichlet series has exactly the totient coefficients. -/
theorem kloostermanDirichlet_zero_zero_eq_totient_LSeries (s : ℂ) :
    kloostermanDirichlet 0 0 s =
      LSeries (fun c : ℕ => (Nat.totient c : ℂ)) (2 * s) := by
  unfold kloostermanDirichlet
  exact LSeries_congr (fun {_} _ => kloostermanCoefficient_zero_zero _) (2 * s)

/-- Genuine convergence of the totient series with positive-denominator indexing. -/
theorem kloostermanDirichlet_zero_zero_hasSum {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun k : ℕ => (Nat.totient (k + 1) : ℂ) / (k + 1 : ℂ) ^ (2 * s))
      (kloostermanDirichlet 0 0 s) := by
  simpa only [kloostermanSum_zero_zero_eq_totient] using
    kloostermanDirichlet_hasSum 0 0 hs

/-- Absolute convergence of the actual totient series. -/
theorem summable_norm_totientDirichlet {s : ℂ} (hs : 1 < s.re) :
    Summable (fun k : ℕ => ‖(Nat.totient (k + 1) : ℂ) / (k + 1 : ℂ) ^ (2 * s)‖) :=
  (kloostermanDirichlet_zero_zero_hasSum hs).summable.norm

/-- Exact evaluation as a genuinely convergent totient sum. -/
theorem kloostermanDirichlet_zero_zero_eq_tsum {s : ℂ} (hs : 1 < s.re) :
    kloostermanDirichlet 0 0 s =
      ∑' k : ℕ, (Nat.totient (k + 1) : ℂ) / (k + 1 : ℂ) ^ (2 * s) :=
  (kloostermanDirichlet_zero_zero_hasSum hs).tsum_eq.symm

/-- The same convergence with denominator zero included as an explicit zero term. -/
theorem kloostermanDirichlet_zero_zero_totient_hasSum {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun c : ℕ => (Nat.totient c : ℂ) / (c : ℂ) ^ (2 * s))
      (kloostermanDirichlet 0 0 s) := by
  refine (kloostermanDirichlet_summable 0 0 hs).hasSum.congr_fun fun c => ?_
  cases c <;> simp [LSeries.term, kloostermanSum_zero_zero_eq_totient]

end GapFamily.Analytic
