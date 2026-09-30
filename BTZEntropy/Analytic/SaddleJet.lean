import BTZEntropy.Analytic.SaddleExponential
import BTZEntropy.Analytic.AnalyticJet
import Mathlib.Analysis.Analytic.Order

/-!
# Finite jets of the actual saddle integrand

The bivariate polynomial in the coefficient algorithm is evaluated as an
ordinary polynomial in the complex scale variable. Its finite coefficients
are compared with the analytic saddle integrand at scale zero.
-/

noncomputable section

open Filter
open scoped BigOperators Topology

namespace BTZEntropy

def saddlePolynomialValue (p : Polynomial (Polynomial ℝ)) (z ε : ℂ) : ℂ :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom Complex.ofRealHom z) ε p

theorem analyticAt_saddlePolynomialValue (p : Polynomial (Polynomial ℝ)) (z ε : ℂ) :
    AnalyticAt ℂ (saddlePolynomialValue p z) ε := by
  change AnalyticAt ℂ
    (fun ε => p.eval₂ (Polynomial.eval₂RingHom Complex.ofRealHom z) ε) ε
  simp only [Polynomial.eval₂_eq_sum, Polynomial.sum]
  apply Finset.analyticAt_fun_sum
  intro n hn
  fun_prop

theorem iteratedDeriv_saddlePolynomialValue (p : Polynomial (Polynomial ℝ)) (z : ℂ)
    (n : ℕ) :
    iteratedDeriv n (saddlePolynomialValue p z) 0 =
      (n.factorial : ℂ) * (p.coeff n).eval₂ Complex.ofRealHom z := by
  let H := Polynomial.eval₂RingHom Complex.ofRealHom z
  change iteratedDeriv n (fun ε => p.eval₂ H ε) 0 = (n.factorial : ℂ) * H (p.coeff n)
  simp only [Polynomial.eval₂_eq_sum, Polynomial.sum]
  rw [iteratedDeriv_fun_sum]
  · simp only [iteratedDeriv_const_mul_field, iteratedDeriv_fun_pow_zero]
    rw [Finset.sum_eq_single n]
    · simp
      ring
    · intro m hm hmn
      simp [Ne.symm hmn]
    · intro hn
      simp [Polynomial.notMem_support_iff.mp hn]
  · intro m hm
    fun_prop

def amplitudeTaylorValue (φ : ℝ → ℝ) (x : ℝ) (N : ℕ) (z ε : ℂ) : ℂ :=
  saddlePolynomialValue (amplitudeTaylor φ x N) z ε

theorem amplitudeTaylorValue_eq_sum (φ : ℝ → ℝ) (x : ℝ) (N : ℕ) (z ε : ℂ) :
    amplitudeTaylorValue φ x N z ε =
      ∑ j ∈ Finset.range (N + 1),
        ((iteratedDeriv j (amplitude φ) (saddleBeta x) : ℝ) : ℂ) /
          (j.factorial : ℂ) * z ^ j * ε ^ j := by
  simp [amplitudeTaylorValue, saddlePolynomialValue, amplitudeTaylor,
    Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial]

def rationalSaddlePhase (x : ℝ) (z ε : ℂ) : ℂ :=
  (phaseConstant : ℂ) * z ^ 2 /
    ((saddleBeta x : ℂ) ^ 2 * ((saddleBeta x : ℂ) + ε * z))

theorem analyticAt_rationalSaddlePhase {x : ℝ} (hx : 0 < x) (z : ℂ) :
    AnalyticAt ℂ (rationalSaddlePhase x z) 0 := by
  have hβ : (saddleBeta x : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (saddleBeta_pos hx)
  unfold rationalSaddlePhase
  apply AnalyticAt.div (by fun_prop) (by fun_prop)
  simp [hβ]

theorem rationalSaddlePhase_eq_normalized {x : ℝ} (hx : 0 < x) (ε z : ℂ)
    (hε : ε ≠ 0) (hw : (saddleBeta x : ℂ) + ε * z ≠ 0) :
    rationalSaddlePhase x z ε =
      (complexSaddlePhase x ((saddleBeta x : ℂ) + ε * z) -
        (saddlePhase x (saddleBeta x) : ℂ)) / ε ^ 2 := by
  have hβ : (saddleBeta x : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (saddleBeta_pos hx)
  have hs : (x : ℂ) * (saddleBeta x : ℂ) ^ 2 = (phaseConstant : ℂ) := by
    exact_mod_cast saddleBeta_equation hx
  have hxeq : (x : ℂ) = (phaseConstant : ℂ) / (saddleBeta x : ℂ) ^ 2 :=
    (eq_div_iff (pow_ne_zero _ hβ)).2 hs
  simp only [rationalSaddlePhase, complexSaddlePhase, saddlePhase,
    Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_div]
  rw [hxeq]
  field_simp [hβ, hε, hw]
  ring_nf
  have hw' : z * ε + (saddleBeta x : ℂ) ≠ 0 := by simpa [add_comm, mul_comm] using hw
  field_simp
  ring

def phaseJetRemainder (x : ℝ) (N : ℕ) (z ε : ℂ) : ℂ :=
  (phaseConstant : ℂ) * (-z) ^ (N + 3) /
    ((saddleBeta x : ℂ) ^ (N + 3) * ((saddleBeta x : ℂ) + ε * z))

theorem analyticAt_phaseJetRemainder {x : ℝ} (hx : 0 < x) (N : ℕ) (z : ℂ) :
    AnalyticAt ℂ (phaseJetRemainder x N z) 0 := by
  have hβ : (saddleBeta x : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (saddleBeta_pos hx)
  unfold phaseJetRemainder
  apply AnalyticAt.div (by fun_prop) (by fun_prop)
  simp [hβ]

theorem rationalSaddlePhase_eq_finite {x : ℝ} (hx : 0 < x) (N : ℕ) (ε z : ℂ)
    (hw : (saddleBeta x : ℂ) + ε * z ≠ 0) :
    rationalSaddlePhase x z ε =
      (saddleHessian x : ℂ) / 2 * z ^ 2 + phaseDeviationValue x N ε z +
        ε ^ (N + 1) * phaseJetRemainder x N z ε := by
  have hβ : (saddleBeta x : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (saddleBeta_pos hx)
  by_cases hε : ε = 0
  · subst ε
    simp [rationalSaddlePhase, phaseDeviationValue_eq_sum, saddleHessian,
      Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow]
    field_simp
  · rw [rationalSaddlePhase_eq_normalized hx ε z hε hw,
      complexSaddlePhase_exact_normalized hx ε z hε hw N]
    congr 1
    simp only [reciprocalRemainder, phaseJetRemainder]
    rw [show -(ε * z) = ε * (-z) by ring, mul_pow]
    have hp : ε ^ (N + 3) = ε ^ (N + 1) * ε ^ 2 := by rw [← pow_add]
    simp only [show N + 2 + 1 = N + 3 by omega]
    rw [hp]
    field_simp

theorem eventually_rationalSaddlePhase_eq_finite {x : ℝ} (hx : 0 < x)
    (N : ℕ) (z : ℂ) :
    ∀ᶠ ε in 𝓝 (0 : ℂ), rationalSaddlePhase x z ε =
      (saddleHessian x : ℂ) / 2 * z ^ 2 + phaseDeviationValue x N ε z +
        ε ^ (N + 1) * phaseJetRemainder x N z ε := by
  have hβ : (saddleBeta x : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (saddleBeta_pos hx)
  have hc : ContinuousAt (fun ε : ℂ => (saddleBeta x : ℂ) + ε * z) 0 := by fun_prop
  filter_upwards [hc.eventually_ne (y := (0 : ℂ)) (by simpa using hβ)] with ε hε
  exact rationalSaddlePhase_eq_finite hx N ε z hε

theorem analyticJetEq_rationalSaddlePhase {x : ℝ} (hx : 0 < x) (N : ℕ) (z : ℂ) :
    analyticJetEq N (rationalSaddlePhase x z)
      (fun ε => (saddleHessian x : ℂ) / 2 * z ^ 2 + phaseDeviationValue x N ε z) :=
  ⟨phaseJetRemainder x N z, analyticAt_phaseJetRemainder hx N z,
    eventually_rationalSaddlePhase_eq_finite hx N z⟩

/-- Taylor's theorem for the genuine holomorphic amplitude, transported to the
designated real-axis derivatives rather than an assumed integrand jet. -/
theorem analyticJetEq_amplitudeTaylor {A : ℂ → ℂ} (φ : ℝ → ℝ) (x : ℝ) (N : ℕ)
    (hA : AnalyticAt ℂ A (saddleBeta x))
    (hderiv : ∀ n ≤ N, iteratedDeriv n A (saddleBeta x) =
      ((iteratedDeriv n (amplitude φ) (saddleBeta x) : ℝ) : ℂ)) (z : ℂ) :
    analyticJetEq N (fun ε => A ((saddleBeta x : ℂ) + ε * z))
      (amplitudeTaylorValue φ x N z) := by
  have hf : AnalyticAt ℂ (fun u : ℂ => A ((saddleBeta x : ℂ) + u)) 0 :=
    hA.fun_comp_of_eq (analyticAt_const.add analyticAt_id) (by simp)
  obtain ⟨R, hR, he⟩ := hf.exists_eventuallyEq_sum_add_pow_mul (N + 1)
  refine ⟨fun ε => z ^ (N + 1) * R (ε * z),
    analyticAt_const.mul (hR.fun_comp_of_eq (analyticAt_id.mul analyticAt_const) (by simp)), ?_⟩
  have ht : Tendsto (fun ε : ℂ => ε * z) (𝓝 0) (𝓝 0) := by
    simpa using (continuousAt_id.mul_const z : ContinuousAt (fun ε : ℂ => ε * z) 0).tendsto
  filter_upwards [ht.eventually he] with ε hε
  simp only [iteratedDeriv_comp_const_add, add_zero, smul_eq_mul] at hε
  rw [hε, amplitudeTaylorValue_eq_sum]
  have hsum :
      (∑ i ∈ Finset.range (N + 1),
        ((ε * z) ^ i / (i.factorial : ℂ)) * iteratedDeriv i A (saddleBeta x)) =
      ∑ i ∈ Finset.range (N + 1),
        ((iteratedDeriv i (amplitude φ) (saddleBeta x) : ℝ) : ℂ) /
          (i.factorial : ℂ) * z ^ i * ε ^ i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hderiv i (by simpa using Finset.mem_range.mp hi), mul_pow]
    ring
  rw [hsum, mul_pow]
  ring

theorem analyticJetEq_exp_rationalSaddlePhase {x : ℝ} (hx : 0 < x) (N : ℕ) (z : ℂ) :
    analyticJetEq N (fun ε => Complex.exp (rationalSaddlePhase x z ε))
      (fun ε => Complex.exp ((saddleHessian x : ℂ) / 2 * z ^ 2) *
        phaseExponentialValue x N ε z) := by
  have hd : AnalyticAt ℂ (fun ε => phaseDeviationValue x N ε z) 0 :=
    analyticAt_saddlePolynomialValue (phaseDeviation x N) z 0
  have hd0 : phaseDeviationValue x N 0 z = 0 := by simp [phaseDeviationValue_eq_sum]
  have h₁ := (analyticJetEq_rationalSaddlePhase hx N z).exp (analyticAt_const.add hd)
  have h₂ := (analyticJetEq_exp_comp_sum N hd hd0).const_mul
    (Complex.exp ((saddleHessian x : ℂ) / 2 * z ^ 2))
  have h₃ : analyticJetEq N
      (fun ε => Complex.exp ((saddleHessian x : ℂ) / 2 * z ^ 2 + phaseDeviationValue x N ε z))
      (fun ε => Complex.exp ((saddleHessian x : ℂ) / 2 * z ^ 2) * phaseExponentialValue x N ε z) := by
    simpa only [Complex.exp_add, phaseExponentialValue_eq_sum] using h₂
  exact h₁.trans h₃

/-- The actual rescaled integrand, with the pole at scale zero removed by the
exact saddle equation. -/
def actualSaddleIntegrand (A : ℂ → ℂ) (x : ℝ) (z ε : ℂ) : ℂ :=
  A ((saddleBeta x : ℂ) + ε * z) * Complex.exp (rationalSaddlePhase x z ε)

theorem analyticAt_actualSaddleIntegrand {A : ℂ → ℂ} {x : ℝ} (hx : 0 < x)
    (hA : AnalyticAt ℂ A (saddleBeta x)) (z : ℂ) :
    AnalyticAt ℂ (actualSaddleIntegrand A x z) 0 := by
  exact (hA.fun_comp_of_eq
    (analyticAt_const.add (analyticAt_id.mul analyticAt_const)) (by simp)).mul
      (analyticAt_rationalSaddlePhase hx z).cexp'

theorem analyticJetEq_actualSaddleIntegrand {A : ℂ → ℂ} (φ : ℝ → ℝ) {x : ℝ}
    (hx : 0 < x) (N : ℕ) (hA : AnalyticAt ℂ A (saddleBeta x))
    (hderiv : ∀ n ≤ N, iteratedDeriv n A (saddleBeta x) =
      ((iteratedDeriv n (amplitude φ) (saddleBeta x) : ℝ) : ℂ)) (z : ℂ) :
    analyticJetEq N (actualSaddleIntegrand A x z)
      (fun ε => Complex.exp ((saddleHessian x : ℂ) / 2 * z ^ 2) *
        saddlePolynomialValue (amplitudeTaylor φ x N * phaseExponential x N) z ε) := by
  have hp := (analyticJetEq_amplitudeTaylor φ x N hA hderiv z).mul
    (analyticJetEq_exp_rationalSaddlePhase hx N z)
    (analyticAt_saddlePolynomialValue (amplitudeTaylor φ x N) z 0)
    (analyticAt_rationalSaddlePhase hx z).cexp'
  have he : (fun ε => amplitudeTaylorValue φ x N z ε *
      (Complex.exp ((saddleHessian x : ℂ) / 2 * z ^ 2) * phaseExponentialValue x N ε z)) =
      (fun ε => Complex.exp ((saddleHessian x : ℂ) / 2 * z ^ 2) *
        saddlePolynomialValue (amplitudeTaylor φ x N * phaseExponential x N) z ε) := by
    funext ε
    simp only [amplitudeTaylorValue, saddlePolynomialValue, phaseExponentialValue, map_mul]
    ring
  rw [he] at hp
  exact hp

/-- The coefficient algorithm computes every retained derivative of the actual
holomorphic rescaled integrand. -/
theorem iteratedDeriv_actualSaddleIntegrand {A : ℂ → ℂ} (φ : ℝ → ℝ) {x : ℝ}
    (hx : 0 < x) (N : ℕ) (hA : AnalyticAt ℂ A (saddleBeta x))
    (hderiv : ∀ n ≤ N, iteratedDeriv n A (saddleBeta x) =
      ((iteratedDeriv n (amplitude φ) (saddleBeta x) : ℝ) : ℂ))
    (z : ℂ) {n : ℕ} (hn : n ≤ N) :
    iteratedDeriv n (actualSaddleIntegrand A x z) 0 =
      Complex.exp ((saddleHessian x : ℂ) / 2 * z ^ 2) * (n.factorial : ℂ) *
        ((amplitudeTaylor φ x N * phaseExponential x N).coeff n).eval₂ Complex.ofRealHom z := by
  have he := (analyticJetEq_actualSaddleIntegrand φ hx N hA hderiv z).iteratedDeriv_eq
    (analyticAt_actualSaddleIntegrand hx hA z)
    (analyticAt_const.mul
      (analyticAt_saddlePolynomialValue (amplitudeTaylor φ x N * phaseExponential x N) z 0)) hn
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_saddlePolynomialValue] at he
  simpa only [mul_assoc] using he

theorem iteratedDeriv_actualSaddleIntegrand_imaginary {A : ℂ → ℂ} (φ : ℝ → ℝ) {x : ℝ}
    (hx : 0 < x) (N : ℕ) (hA : AnalyticAt ℂ A (saddleBeta x))
    (hderiv : ∀ n ≤ N, iteratedDeriv n A (saddleBeta x) =
      ((iteratedDeriv n (amplitude φ) (saddleBeta x) : ℝ) : ℂ))
    (t : ℝ) {n : ℕ} (hn : n ≤ N) :
    iteratedDeriv n (actualSaddleIntegrand A x ((t : ℂ) * Complex.I)) 0 =
      (Real.exp (-saddleHessian x * t ^ 2 / 2) : ℂ) * (n.factorial : ℂ) *
        ((amplitudeTaylor φ x N * phaseExponential x N).coeff n).eval₂
          Complex.ofRealHom ((t : ℂ) * Complex.I) := by
  rw [iteratedDeriv_actualSaddleIntegrand φ hx N hA hderiv _ hn]
  have he : (saddleHessian x : ℂ) / 2 * ((t : ℂ) * Complex.I) ^ 2 =
      ((-saddleHessian x * t ^ 2 / 2 : ℝ) : ℂ) := by
    push_cast
    rw [mul_pow, Complex.I_sq]
    ring
  rw [he, ← Complex.ofReal_exp]

end BTZEntropy
