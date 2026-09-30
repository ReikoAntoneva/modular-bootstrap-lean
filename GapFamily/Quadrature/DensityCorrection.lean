import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

/-!
# Polynomial correction of finitely many moments

The actual interval moment Gram map is invertible because the integral of a
nonzero polynomial square is positive. Its inverse supplies a continuous linear
polynomial response to arbitrary changes in finitely many moments, including mass.
-/

noncomputable section

open Set MeasureTheory Polynomial

namespace GapFamily.Quadrature

theorem ofFn_eval {n : ℕ} (v : Fin n → ℝ) (x : ℝ) :
    (Polynomial.ofFn n v).eval x = ∑ i : Fin n, v i * x ^ i.val := by
  rw [Polynomial.ofFn_eq_sum_monomial]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_monomial]

theorem polynomial_sq_integral_pos {a b : ℝ} (hab : a < b)
    (p : ℝ[X]) (hp : p ≠ 0) : 0 < ∫ x in a..b, (p.eval x) ^ 2 := by
  have hex : ∃ x ∈ Icc a b, p.eval x ≠ 0 := by
    by_contra h
    push Not at h
    apply hp
    apply p.eq_zero_of_infinite_isRoot
    apply (Set.Icc_infinite hab).mono
    intro x hx
    exact h x hx
  obtain ⟨x, hx, hpx⟩ := hex
  have h := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    hab (continuous_const.continuousOn : ContinuousOn (fun _ : ℝ => (0 : ℝ)) _)
    (p.continuous.pow 2).continuousOn (fun y _ => sq_nonneg (p.eval y))
    ⟨x, hx, sq_pos_of_ne_zero hpx⟩
  simpa using h

/-- Coefficients are sent to the first `n` moments of their polynomial density. -/
def momentGram (a b : ℝ) (n : ℕ) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun v i := ∫ x in a..b, x ^ i.val * (Polynomial.ofFn n v).eval x
  map_add' u v := by
    ext i
    simp only [map_add, Polynomial.eval_add, Pi.add_apply, mul_add]
    exact intervalIntegral.integral_add
      (((continuous_id.pow i.val).mul (Polynomial.ofFn n u).continuous).intervalIntegrable a b)
      (((continuous_id.pow i.val).mul (Polynomial.ofFn n v).continuous).intervalIntegrable a b)
  map_smul' r v := by
    ext i
    simp only [map_smul, Polynomial.eval_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    ring

theorem momentGram_quadratic (a b : ℝ) {n : ℕ} (v : Fin n → ℝ) :
    (∑ i : Fin n, v i * momentGram a b n v i) =
      ∫ x in a..b, ((Polynomial.ofFn n v).eval x) ^ 2 := by
  change (∑ i : Fin n, v i * ∫ x in a..b,
    x ^ i.val * (Polynomial.ofFn n v).eval x) = _
  simp_rw [← intervalIntegral.integral_const_mul]
  rw [← intervalIntegral.integral_finsetSum]
  · apply intervalIntegral.integral_congr
    intro x _
    dsimp only
    rw [show (∑ i : Fin n, v i * (x ^ i.val * (Polynomial.ofFn n v).eval x)) =
        (∑ i : Fin n, v i * x ^ i.val) * (Polynomial.ofFn n v).eval x by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring]
    rw [← ofFn_eval]
    ring
  · intro i _
    exact (continuous_const.mul ((continuous_id.pow i.val).mul
      (Polynomial.ofFn n v).continuous)).intervalIntegrable a b

theorem momentGram_injective {a b : ℝ} (hab : a < b) (n : ℕ) :
    Function.Injective (momentGram a b n) := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro v hv
  by_contra hne
  have hp : Polynomial.ofFn n v ≠ 0 := by
    intro h
    apply hne
    apply Polynomial.injective_ofFn n
    simpa using h
  have hpos := polynomial_sq_integral_pos hab (Polynomial.ofFn n v) hp
  rw [← momentGram_quadratic] at hpos
  simp [hv] at hpos

/-- Invertibility of the actual polynomial moment Gram map. -/
def momentGramEquiv {a b : ℝ} (hab : a < b) (n : ℕ) :
    (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) :=
  LinearEquiv.ofBijective (momentGram a b n)
    ⟨momentGram_injective hab n, LinearMap.surjective_of_injective (momentGram_injective hab n)⟩

/-- A polynomial density restricted to the physical compact interval. -/
def polynomialDensity (a b : ℝ) (n : ℕ) :
    (Fin n → ℝ) →ₗ[ℝ] C(Icc a b, ℝ) where
  toFun v := ⟨fun x => (Polynomial.ofFn n v).eval x,
    (Polynomial.ofFn n v).continuous.comp continuous_subtype_val⟩
  map_add' u v := by
    ext x
    simp [map_add, Polynomial.eval_add]
  map_smul' r v := by
    ext x
    simp [map_smul, Polynomial.eval_smul]

/-- The continuous polynomial response realizing every prescribed finite moment vector. -/
def densityResponse {a b : ℝ} (hab : a < b) (n : ℕ) :
    (Fin n → ℝ) →L[ℝ] C(Icc a b, ℝ) :=
  LinearMap.toContinuousLinearMap ((polynomialDensity a b n).comp
    (momentGramEquiv hab n).symm.toLinearMap)

theorem densityResponse_apply {a b : ℝ} (hab : a < b) (n : ℕ)
    (w : Fin n → ℝ) (x : Icc a b) :
    densityResponse hab n w x =
      (Polynomial.ofFn n ((momentGramEquiv hab n).symm w)).eval (x : ℝ) := rfl

/-- No moment assumption is made: the actual inverse constructs the response. -/
theorem densityResponse_moment {a b : ℝ} (hab : a < b) (n : ℕ)
    (w : Fin n → ℝ) (i : Fin n) :
    (∫ x in a..b, x ^ i.val *
      (Polynomial.ofFn n ((momentGramEquiv hab n).symm w)).eval x) = w i := by
  have h := (momentGramEquiv hab n).apply_symm_apply w
  exact congrFun h i

/-- A quantitative uniform estimate for the response on the entire interval. -/
theorem norm_densityResponse_apply_le {a b : ℝ} (hab : a < b) (n : ℕ)
    (w : Fin n → ℝ) (x : Icc a b) :
    ‖densityResponse hab n w x‖ ≤ ‖densityResponse hab n‖ * ‖w‖ :=
  (ContinuousMap.norm_coe_le_norm _ x).trans ((densityResponse hab n).le_opNorm w)

/-- Sufficiently small moment changes preserve a strictly positive density. -/
theorem densityResponse_preserves_positive {a b : ℝ} (hab : a < b) (n : ℕ)
    (f : C(Icc a b, ℝ)) {η : ℝ}
    (hf : ∀ x, η ≤ f x) (w : Fin n → ℝ)
    (hw : ‖densityResponse hab n‖ * ‖w‖ < η) :
    ∀ x, 0 < f x + densityResponse hab n w x := by
  intro x
  have hl := norm_densityResponse_apply_le hab n w x
  rw [Real.norm_eq_abs] at hl
  have hlow := (abs_le.mp hl).1
  linarith [hf x]

/-- The first `n` moments, including total mass in coordinate zero. -/
def densityMoments (a b : ℝ) (n : ℕ) (f : ℝ → ℝ) : Fin n → ℝ :=
  fun i => ∫ x in a..b, x ^ i.val * f x

/-- Add the actual polynomial response to correct every prescribed finite moment. -/
def correctedDensity {a b : ℝ} (hab : a < b) (n : ℕ)
    (f : ℝ → ℝ) (target : Fin n → ℝ) (x : ℝ) : ℝ :=
  f x + (Polynomial.ofFn n ((momentGramEquiv hab n).symm
    (target - densityMoments a b n f))).eval x

theorem correctedDensity_moment {a b : ℝ} (hab : a < b) (n : ℕ)
    (f : ℝ → ℝ) (hf : ContinuousOn f (Icc a b)) (target : Fin n → ℝ) :
    densityMoments a b n (correctedDensity hab n f target) = target := by
  ext i
  simp only [densityMoments, correctedDensity, mul_add]
  have h1 : IntervalIntegrable (fun x : ℝ => x ^ i.val * f x) volume a b :=
    ((continuous_id.pow i.val).continuousOn.mul hf).intervalIntegrable_of_Icc hab.le
  have h2 : IntervalIntegrable (fun x : ℝ => x ^ i.val *
      (Polynomial.ofFn n ((momentGramEquiv hab n).symm
        (target - densityMoments a b n f))).eval x) volume a b :=
    ((continuous_id.pow i.val).mul (Polynomial.ofFn n
      ((momentGramEquiv hab n).symm (target - densityMoments a b n f))).continuous).intervalIntegrable a b
  rw [intervalIntegral.integral_add h1 h2]
  rw [densityResponse_moment hab n]
  simp [densityMoments]

theorem correctedDensity_continuousOn {a b : ℝ} (hab : a < b) (n : ℕ)
    (f : ℝ → ℝ) (hf : ContinuousOn f (Icc a b)) (target : Fin n → ℝ) :
    ContinuousOn (correctedDensity hab n f target) (Icc a b) :=
  hf.add (Polynomial.continuous _).continuousOn

/-- Continuity holds jointly in all target moments and the interval variable. -/
theorem correctedDensity_joint_continuous {a b : ℝ} (hab : a < b) (n : ℕ)
    (f : ℝ → ℝ) (hf : ContinuousOn f (Icc a b)) :
    Continuous (fun p : (Fin n → ℝ) × Icc a b => correctedDensity hab n f p.1 p.2) := by
  have hc : Continuous (fun target : Fin n → ℝ =>
      (momentGramEquiv hab n).symm (target - densityMoments a b n f)) :=
    (momentGramEquiv hab n).symm.toLinearMap.continuous_of_finiteDimensional.comp
      (continuous_id.sub continuous_const)
  simp only [correctedDensity, ofFn_eval]
  apply Continuous.add (hf.comp_continuous
    (continuous_subtype_val.comp continuous_snd) (fun _ => Subtype.coe_prop _))
  exact continuous_finsetSum _ (fun i _ =>
    ((continuous_apply i).comp (hc.comp continuous_fst)).mul
      ((continuous_subtype_val.comp continuous_snd).pow i.val))

/-- A small finite-moment change preserves a supplied strict uniform lower bound. -/
theorem correctedDensity_positive_of_close {a b : ℝ} (hab : a < b) (n : ℕ)
    (f : ℝ → ℝ) {η : ℝ} (hf : ∀ x ∈ Icc a b, η ≤ f x)
    (target : Fin n → ℝ)
    (hclose : ‖densityResponse hab n‖ * ‖target - densityMoments a b n f‖ < η) :
    ∀ x ∈ Icc a b, 0 < correctedDensity hab n f target x := by
  intro x hx
  have hnorm := norm_densityResponse_apply_le hab n
    (target - densityMoments a b n f) ⟨x, hx⟩
  rw [densityResponse_apply, Real.norm_eq_abs] at hnorm
  have hlow := (abs_le.mp hnorm).1
  dsimp [correctedDensity]
  linarith [hf x hx]

/-- Every positive continuous density has an actual positive local section of its moments. -/
theorem correctedDensity_positive_near {a b : ℝ} (hab : a < b) (n : ℕ)
    (f : ℝ → ℝ) (hf : ContinuousOn f (Icc a b))
    (hpos : ∀ x ∈ Icc a b, 0 < f x) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ target : Fin n → ℝ,
      ‖target - densityMoments a b n f‖ < δ →
      ∀ x ∈ Icc a b, 0 < correctedDensity hab n f target x := by
  obtain ⟨η, hη, hbound⟩ := isCompact_Icc.exists_forall_le' hf hpos
  refine ⟨η / (‖densityResponse hab n‖ + 1), by positivity, ?_⟩
  intro target hnear
  apply correctedDensity_positive_of_close hab n f hbound target
  have hd : 0 < ‖densityResponse hab n‖ + 1 := by positivity
  have hs := (lt_div_iff₀ hd).mp hnear
  nlinarith [norm_nonneg (target - densityMoments a b n f)]

end GapFamily.Quadrature
