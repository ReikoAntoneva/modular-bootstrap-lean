import BTZEntropy.Analytic.Amplitude
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Order.Compact

/-!
# Regularity of the designated saddle coefficient

The finite Taylor polynomials are lifted to polynomials over continuous real
functions on the positive energy-ratio axis. Evaluation commutes with the
coefficient algorithm, so every designated count coefficient is continuous and
has an actual compact-uniform bound.
-/

noncomputable section

open Polynomial
open scoped Topology ContDiff BigOperators

namespace BTZEntropy

private abbrev PositiveRatio := {x : ℝ // 0 < x}

private abbrev RatioFunction := C(PositiveRatio, ℝ)

private def ratioEval (x : PositiveRatio) : RatioFunction →+* ℝ :=
  (ContinuousMap.evalAlgHom ℝ ℝ x).toRingHom

private theorem continuous_saddleBeta :
    Continuous (fun x : PositiveRatio => saddleBeta x) := by
  unfold saddleBeta saddleRadius
  exact continuous_const.div (Real.continuous_sqrt.comp
    (continuous_const.mul continuous_subtype_val))
    (fun x => ne_of_gt (Real.sqrt_pos.2 (mul_pos (by norm_num) x.property)))

private theorem continuous_amplitudeJet (φ : SmoothKernel) (n : ℕ) :
    Continuous (fun x : PositiveRatio => iteratedDeriv n (amplitude φ) (saddleBeta x)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have hd : ContinuousAt (iteratedDeriv n (amplitude φ)) (saddleBeta x) := by
    rw [iteratedDeriv_eq_equiv_comp]
    exact ((ContinuousMultilinearMap.piFieldEquiv ℝ (Fin n) ℝ).symm.continuous).continuousAt.comp
      ((contDiffAt_amplitude φ (saddleBeta_pos x.property)).continuousAt_iteratedFDeriv
        (by simp))
  exact ContinuousAt.comp (f := fun y : PositiveRatio => saddleBeta y)
    (x := x) hd continuous_saddleBeta.continuousAt

private def amplitudeJet (φ : SmoothKernel) (n : ℕ) : RatioFunction :=
  ⟨fun x => iteratedDeriv n (amplitude φ) (saddleBeta x), continuous_amplitudeJet φ n⟩

private def phaseJet (j : ℕ) : RatioFunction :=
  ⟨fun x => (-1 : ℝ) ^ (j + 3) * phaseConstant / saddleBeta x ^ (j + 4),
    continuous_const.div (continuous_saddleBeta.pow _) (fun x =>
      pow_ne_zero _ (ne_of_gt (saddleBeta_pos x.property)))⟩

private def liftedAmplitude (φ : SmoothKernel) (N : ℕ) : Polynomial (Polynomial RatioFunction) :=
  ∑ j ∈ Finset.range (N + 1),
    monomial j (monomial j (amplitudeJet φ j * ContinuousMap.const _ ((j.factorial : ℝ)⁻¹)))

private def liftedPhase (N : ℕ) : Polynomial (Polynomial RatioFunction) :=
  ∑ j ∈ Finset.range N, monomial (j + 1) (monomial (j + 3) (phaseJet j))

private def liftedExponential (N : ℕ) : Polynomial (Polynomial RatioFunction) :=
  ∑ j ∈ Finset.range (N + 1),
    C (C (ContinuousMap.const _ ((j.factorial : ℝ)⁻¹))) * liftedPhase N ^ j

private theorem map_liftedAmplitude (φ : SmoothKernel) (N : ℕ) (x : PositiveRatio) :
    (liftedAmplitude φ N).map (mapRingHom (ratioEval x)) = amplitudeTaylor φ x N := by
  simp [liftedAmplitude, amplitudeTaylor, Polynomial.map_sum, Polynomial.map_monomial,
    ratioEval, amplitudeJet, div_eq_mul_inv]

private theorem map_liftedPhase (N : ℕ) (x : PositiveRatio) :
    (liftedPhase N).map (mapRingHom (ratioEval x)) = phaseDeviation x N := by
  simp [liftedPhase, phaseDeviation, Polynomial.map_sum, Polynomial.map_monomial,
    ratioEval, phaseJet]

private theorem map_liftedExponential (N : ℕ) (x : PositiveRatio) :
    (liftedExponential N).map (mapRingHom (ratioEval x)) = phaseExponential x N := by
  simp only [liftedExponential, Polynomial.map_sum, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_pow, map_liftedPhase]
  simp [phaseExponential, ratioEval]

private theorem continuous_saddleHessian :
    Continuous (fun x : PositiveRatio => saddleHessian x) := by
  exact continuous_const.div (continuous_saddleBeta.pow 3)
    (fun x => pow_ne_zero _ (ne_of_gt (saddleBeta_pos x.property)))

private theorem saddleHessian_pos {x : ℝ} (hx : 0 < x) : 0 < saddleHessian x := by
  exact div_pos (mul_pos (by norm_num) phaseConstant_pos) (pow_pos (saddleBeta_pos hx) _)

private theorem continuous_gaussianMoment (n : ℕ) :
    Continuous (fun x : PositiveRatio => imaginaryGaussianMoment (saddleHessian x) n) := by
  unfold imaginaryGaussianMoment
  split_ifs
  · exact continuous_const.div
      (continuous_const.mul (continuous_saddleHessian.pow _)) (fun x => by
        apply mul_ne_zero
        · positivity
        · exact pow_ne_zero _ (ne_of_gt (saddleHessian_pos x.property)))
  · exact continuous_const

private theorem continuous_gaussianEvaluation (p : Polynomial RatioFunction) :
    Continuous (fun x : PositiveRatio =>
      gaussianEvaluation (saddleHessian x) (p.map (ratioEval x))) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [Polynomial.map_add, gaussianEvaluation_add]
    exact hp.add hq
  | monomial n a =>
    simp only [Polynomial.map_monomial, gaussianEvaluation_monomial]
    exact a.continuous.mul (continuous_gaussianMoment n)

private theorem continuous_saddleCountCoefficient_positive (φ : SmoothKernel) (m : ℕ) :
    Continuous (fun x : PositiveRatio => saddleCountCoefficient φ x m) := by
  let p := ((liftedAmplitude φ (2 * m) * liftedExponential (2 * m)).coeff (2 * m))
  have hp := continuous_gaussianEvaluation p
  have heq (x : PositiveRatio) : p.map (ratioEval x) =
      (amplitudeTaylor φ x (2 * m) * phaseExponential x (2 * m)).coeff (2 * m) := by
    dsimp [p]
    change (mapRingHom (ratioEval x)) _ = _
    rw [← coeff_map, Polynomial.map_mul, map_liftedAmplitude, map_liftedExponential]
  simp_rw [heq] at hp
  exact hp.div (by simpa using continuous_amplitudeJet φ 0)
    (fun x => amplitude_ne_zero φ (saddleBeta_pos x.property))

/-- Each finite Taylor--Gaussian coefficient is continuous on positive energy ratios. -/
theorem continuousOn_saddleCountCoefficient (φ : SmoothKernel) (m : ℕ) :
    ContinuousOn (fun x => saddleCountCoefficient φ x m) (Set.Ioi 0) := by
  exact continuousOn_iff_continuous_domRestrict.mpr
    (continuous_saddleCountCoefficient_positive φ m)

/-- The designated coefficient is bounded on every positive compact interval. -/
theorem exists_pos_bound_saddleCountCoefficient (φ : SmoothKernel) (m : ℕ)
    {L U : ℝ} (hL : 0 < L) :
    ∃ M > 0, ∀ x ∈ Set.Icc L U, |saddleCountCoefficient φ x m| ≤ M := by
  have hc : ContinuousOn (fun x => saddleCountCoefficient φ x m) (Set.Icc L U) :=
    (continuousOn_saddleCountCoefficient φ m).mono fun _ hx => lt_of_lt_of_le hL hx.1
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max M 1, lt_of_lt_of_le (by norm_num) (le_max_right _ _), fun x hx => ?_⟩
  have hb : |saddleCountCoefficient φ x m| ≤ M := by
    simpa only [Real.norm_eq_abs] using hM x hx
  exact hb.trans (le_max_left _ _)

/-- One bound controls all the finitely many coefficients used by a truncation. -/
theorem exists_pos_bound_saddleCountCoefficient_range (φ : SmoothKernel) (P : ℕ)
    {L U : ℝ} (hL : 0 < L) :
    ∃ M > 0, ∀ n ≤ P, ∀ x ∈ Set.Icc L U, |saddleCountCoefficient φ x n| ≤ M := by
  induction P with
  | zero =>
    obtain ⟨M, hM, hb⟩ := exists_pos_bound_saddleCountCoefficient φ 0 (U := U) hL
    exact ⟨M, hM, fun n hn x hx => by simpa [Nat.eq_zero_of_le_zero hn] using hb x hx⟩
  | succ P ih =>
    obtain ⟨M, hM, hb⟩ := ih
    obtain ⟨N, hN, hc⟩ := exists_pos_bound_saddleCountCoefficient φ (P + 1) (U := U) hL
    refine ⟨max M N, lt_of_lt_of_le hM (le_max_left _ _), fun n hn x hx => ?_⟩
    rcases Nat.eq_or_lt_of_le hn with rfl | hn
    · exact (hc x hx).trans (le_max_right _ _)
    · exact (hb n (Nat.le_of_lt_succ hn) x hx).trans (le_max_left _ _)

end BTZEntropy
