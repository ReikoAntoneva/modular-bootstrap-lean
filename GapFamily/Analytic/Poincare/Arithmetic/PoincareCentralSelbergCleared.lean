import GapFamily.Analytic.Poincare.Arithmetic.PoincareCentralQuotient
import GapFamily.Analytic.Arithmetic.SelbergDivisorArithmetic
import GapFamily.Analytic.Arithmetic.SelbergClearedProduct
import GapFamily.Analytic.Arithmetic.KloostermanDirichletSelberg

/-! The actual finite Selberg identity with denominators cleared on the
connected reference-height continuation region. -/
noncomputable section
namespace GapFamily.Analytic.PoincareCentralZeta
open Set CuspFourierCutoff PoincareFourierContinuation
open PoincareCanonical PoincareCentralFactor
open SelbergFiniteBound SelbergClearedProduct

/-- Multiplying by the finite family of actual entire Fourier factors extends
Selberg's proved Dirichlet identity without assuming global factor nonvanishing. -/
theorem centralNumerator_selberg_cleared (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) :
    EqOn
      (fun κ => centralNumerator 1 zero_lt_one m n κ *
        ∏ d ∈ (m.natAbs.gcd n.natAbs).divisors,
          centralFourierFactor 1 (m * n / (d : ℤ) ^ 2) κ)
      (fun κ => centralFourierFactor 1 m κ *
        ∑ d ∈ (m.natAbs.gcd n.natAbs).divisors,
          (d : ℂ) ^ (-2 * κ) *
            centralNumerator 1 zero_lt_one (m * n / (d : ℤ) ^ 2) 1 κ *
              ∏ e ∈ (m.natAbs.gcd n.natAbs).divisors.erase d,
                centralFourierFactor 1 (m * n / (e : ℤ) ^ 2) κ)
      (horizontalFourierDomain 1 zero_lt_one) := by
  classical
  let s := (m.natAbs.gcd n.natAbs).divisors
  have hdf (d : ℕ) (hd : d ∈ s) : AnalyticOnNhd ℂ
      (centralFourierFactor 1 (m * n / (d : ℤ) ^ 2))
      (horizontalFourierDomain 1 zero_lt_one) := by
    intro κ _
    exact centralFourierFactor_analyticAt zero_lt_one
      (normalized_frequency_ne_zero hm hn hd) κ
  have hd0 : AnalyticOnNhd ℂ (centralFourierFactor 1 m)
      (horizontalFourierDomain 1 zero_lt_one) := by
    intro κ _
    exact centralFourierFactor_analyticAt zero_lt_one hm κ
  have hw (d : ℕ) (hd : d ∈ s) : AnalyticOnNhd ℂ
      (fun κ : ℂ => (d : ℂ) ^ (-2 * κ))
      (horizontalFourierDomain 1 zero_lt_one) := by
    intro κ _
    have hdne : (d : ℂ) ≠ 0 := by
      exact_mod_cast (common_frequency_divisor_pos hd).ne'
    exact (((differentiable_const (-2 : ℂ)).mul differentiable_id).const_cpow
      (Or.inl hdne)).analyticAt κ
  have hl : AnalyticOnNhd ℂ
      (fun κ => centralNumerator 1 zero_lt_one m n κ *
        ∏ d ∈ s, centralFourierFactor 1 (m * n / (d : ℤ) ^ 2) κ)
      (horizontalFourierDomain 1 zero_lt_one) :=
    (analyticOnNhd_centralNumerator 1 zero_lt_one m n).mul
      (s.analyticOnNhd_fun_prod hdf)
  have hr : AnalyticOnNhd ℂ
      (fun κ => centralFourierFactor 1 m κ *
        ∑ d ∈ s, (d : ℂ) ^ (-2 * κ) *
          centralNumerator 1 zero_lt_one (m * n / (d : ℤ) ^ 2) 1 κ *
            ∏ e ∈ s.erase d, centralFourierFactor 1 (m * n / (e : ℤ) ^ 2) κ)
      (horizontalFourierDomain 1 zero_lt_one) := by
    apply hd0.mul
    apply s.analyticOnNhd_fun_sum
    intro d hd
    exact ((hw d hd).mul
      (analyticOnNhd_centralNumerator 1 zero_lt_one _ 1)).mul
        ((s.erase d).analyticOnNhd_fun_prod
          (fun e he => hdf e (Finset.mem_of_mem_erase he)))
  apply eqOn_continuationRegion_of_common
    (horizontalContinuation 1 zero_lt_one).radius_pos hl hr
  intro κ hκ
  have hk : (1 / 2 : ℝ) < κ.re := by linarith
  have hs : 1 < (exponent κ).re := by
    norm_num [exponent, Complex.add_re]
    linarith
  have hsel : kloostermanDirichlet m n (exponent κ) =
      ∑ d ∈ s, (d : ℂ) ^ (-2 * κ) *
        kloostermanDirichlet (m * n / (d : ℤ) ^ 2) 1 (exponent κ) := by
    have he : (1 : ℂ) - 2 * exponent κ = -2 * κ := by
      unfold exponent
      ring
    simpa only [he] using kloostermanDirichlet_selberg m n (Or.inl hm) hs
  exact cleared_identity_of_finite_sum s
    (D0 := centralFourierFactor 1 m κ)
    (Z0 := kloostermanDirichlet m n (exponent κ))
    (A0 := centralNumerator 1 zero_lt_one m n κ)
    (D := fun d => centralFourierFactor 1 (m * n / (d : ℤ) ^ 2) κ)
    (Z := fun d => kloostermanDirichlet (m * n / (d : ℤ) ^ 2) 1 (exponent κ))
    (A := fun d => centralNumerator 1 zero_lt_one (m * n / (d : ℤ) ^ 2) 1 κ)
    (c := fun d => (d : ℂ) ^ (-2 * κ))
    (centralNumerator_eq_factor_mul_dirichlet 1 zero_lt_one m n hm hk)
    (fun d hd => centralNumerator_eq_factor_mul_dirichlet 1 zero_lt_one _ 1
      (normalized_frequency_ne_zero hm hn hd) hk) hsel

end GapFamily.Analytic.PoincareCentralZeta
