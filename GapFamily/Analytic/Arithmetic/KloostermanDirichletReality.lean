import GapFamily.Analytic.Arithmetic.KloostermanDirichlet
import GapFamily.Analytic.Arithmetic.KloostermanReality

/-! Schwarz reflection of the literal, absolutely convergent Kloosterman
Dirichlet series. -/
noncomputable section
namespace GapFamily.Analytic
open Complex
open scoped ComplexConjugate

private theorem conj_nat_cpow (n : ℕ) (s : ℂ) :
    conj ((n : ℂ) ^ conj s) = (n : ℂ) ^ s := by
  symm
  simpa only [map_natCast] using
    Complex.conj_cpow (n : ℂ) s (by
      simpa only [Complex.natCast_arg] using (Ne.symm Real.pi_ne_zero))

/-- Real finite coefficients and positive real denominators give the exact
reflection identity on the original half-plane. -/
theorem conj_kloostermanDirichlet (m n : ℤ) (s : ℂ) (hs : 1 < s.re) :
    conj (kloostermanDirichlet m n (conj s)) = kloostermanDirichlet m n s := by
  rw [kloostermanDirichlet_eq_tsum m n (by simpa using hs),
    kloostermanDirichlet_eq_tsum m n hs, Complex.conj_tsum]
  apply tsum_congr
  intro k
  rw [map_div₀, conj_kloostermanSum]
  congr 1
  have he : 2 * conj s = conj (2 * s) := by simp [map_ofNat]
  rw [he]
  simpa only [Nat.cast_add, Nat.cast_one] using conj_nat_cpow (k + 1) (2 * s)

/-- In particular, values in the real convergence region are real. -/
@[simp] theorem conj_kloostermanDirichlet_ofReal (m n : ℤ) (s : ℝ) (hs : 1 < s) :
    conj (kloostermanDirichlet m n (s : ℂ)) = kloostermanDirichlet m n (s : ℂ) := by
  simpa only [Complex.conj_ofReal] using conj_kloostermanDirichlet m n (s : ℂ) hs

end GapFamily.Analytic
