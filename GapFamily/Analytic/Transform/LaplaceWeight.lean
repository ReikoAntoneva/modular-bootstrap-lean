import GapFamily.Analytic.Foundation.ReferenceMeasure
import GapFamily.Analytic.Transform.LaplaceDensity
import GapFamily.Analytic.Transform.LaplaceTest
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# The regularizer and the weighted energy norm

Multiplication by the actual Laplace regularizer converts its finite weighted
measure to the polynomially weighted physical energy norm. The equality is
proved at the extended `L²` seminorm, so it also records finiteness correctly.
-/

namespace GapFamily.Analytic

open MeasureTheory
open scoped ENNReal BigOperators

theorem regularized_polynomial_eq_finite_laplaceTest (p : Polynomial ℂ) (E : ℝ) :
    (laplaceRegularizer E : ℂ) * p.eval (Real.exp (-E) : ℂ) =
      ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k * (laplaceTest k E : ℂ) := by
  rw [Polynomial.eval_eq_sum_range, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [laplaceTest_eq_regularizer_mul_pow]
  unfold laplaceRegularizer
  push_cast
  ring

theorem eLpNorm_mul_eq_withDensity_sq {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {q f : α → ℂ} (hq : Measurable q)
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm (fun x => q x * f x) 2 μ =
      eLpNorm f 2 (μ.withDensity (fun x => ‖q x‖ₑ ^ 2)) := by
  have hqf : AEStronglyMeasurable (fun x => q x * f x) μ :=
    hq.aestronglyMeasurable.mul hf
  have hfw := hf.mono_ac (withDensity_absolutelyContinuous μ (fun x => ‖q x‖ₑ ^ 2))
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hqf,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hfw]
  norm_num only [ENNReal.toReal_ofNat, ENNReal.rpow_natCast]
  rw [lintegral_withDensity_eq_lintegral_mul₀
    ((hq.enorm.pow_const 2).aemeasurable) (hf.enorm.pow_const 2)]
  congr 1
  apply lintegral_congr
  intro x
  simp only [enorm_mul, ENNReal.rpow_two, mul_pow, Pi.mul_apply]

/-- The weighted row norm is `L²((1+E)^4 dω_j)`. -/
noncomputable def energySpaceMeasure (j : ℤ) : Measure ℝ :=
  (referenceMeasure j).withDensity (fun E => ENNReal.ofReal ((1 + E) ^ 4))

theorem energySpaceMeasure_regularized (j : ℤ) :
    (energySpaceMeasure j).withDensity
        (fun E => ‖(laplaceRegularizer E : ℂ)‖ₑ ^ 2) = laplaceReferenceMeasure j := by
  unfold energySpaceMeasure laplaceReferenceMeasure
  have hw : Measurable (fun E : ℝ => ENNReal.ofReal ((1 + E) ^ 4)) := by fun_prop
  have hq : Measurable (fun E => ‖(laplaceRegularizer E : ℂ)‖ₑ ^ 2) := by
    exact ((Complex.continuous_ofReal.comp continuous_laplaceRegularizer).measurable.enorm.pow_const 2)
  rw [← withDensity_mul _ hw hq]
  congr 1
  funext E
  simp only [Pi.mul_apply, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
    ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs, laplaceWeight]
  rw [← ENNReal.ofReal_mul (by positivity), mul_comm]

theorem laplaceRegularizer_norm_identity (j : ℤ) {f : ℝ → ℂ}
    (hf : AEStronglyMeasurable f (energySpaceMeasure j)) :
    eLpNorm (fun E => (laplaceRegularizer E : ℂ) * f E) 2 (energySpaceMeasure j) =
      eLpNorm f 2 (laplaceReferenceMeasure j) := by
  have hq : Measurable (fun E => (laplaceRegularizer E : ℂ)) :=
    (Complex.continuous_ofReal.comp continuous_laplaceRegularizer).measurable
  rw [eLpNorm_mul_eq_withDensity_sq _ hq hf, energySpaceMeasure_regularized]

theorem laplaceRegularizer_energy_ae_pos (j : ℤ) :
    ∀ᵐ E ∂energySpaceMeasure j, 0 < laplaceRegularizer E :=
  (withDensity_absolutelyContinuous _ _).ae_le (laplaceRegularizer_ae_pos j)

theorem laplaceRegularizer_div_norm_identity (j : ℤ) {f : ℝ → ℂ}
    (hf : AEStronglyMeasurable f (energySpaceMeasure j)) :
    eLpNorm (fun E => f E / (laplaceRegularizer E : ℂ)) 2 (laplaceReferenceMeasure j) =
      eLpNorm f 2 (energySpaceMeasure j) := by
  have hq : AEStronglyMeasurable (fun E => f E / (laplaceRegularizer E : ℂ))
      (energySpaceMeasure j) :=
    (hf.aemeasurable.div
      (Complex.continuous_ofReal.comp continuous_laplaceRegularizer).measurable.aemeasurable).aestronglyMeasurable
  rw [← laplaceRegularizer_norm_identity j hq]
  apply eLpNorm_congr_ae
  filter_upwards [laplaceRegularizer_energy_ae_pos j] with E hE
  have hn : (laplaceRegularizer E : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hE
  exact mul_div_cancel₀ (f E) hn

theorem memLp_div_laplaceRegularizer (j : ℤ) {f : ℝ → ℂ}
    (hf : MemLp f 2 (energySpaceMeasure j)) :
    MemLp (fun E => f E / (laplaceRegularizer E : ℂ)) 2 (laplaceReferenceMeasure j) := by
  change eLpNorm _ _ _ < ∞
  rw [laplaceRegularizer_div_norm_identity j hf.aestronglyMeasurable]
  exact hf.eLpNorm_lt_top

/-- The actual regularized finite Laplace tests are dense in the weighted
physical row. The finite-measure reduction and nonvanishing multiplier are
proved, rather than assumed as auxiliary density hypotheses. -/
theorem exists_regularized_laplacePolynomial_eLpNorm_sub_lt (j : ℤ) {f : ℝ → ℂ}
    (hf : MemLp f 2 (energySpaceMeasure j)) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Polynomial ℂ,
      MemLp (fun E => (laplaceRegularizer E : ℂ) * p.eval (Real.exp (-E) : ℂ))
        2 (energySpaceMeasure j) ∧
      eLpNorm (fun E => f E - (laplaceRegularizer E : ℂ) * p.eval (Real.exp (-E) : ℂ))
        2 (energySpaceMeasure j) < ENNReal.ofReal ε := by
  obtain ⟨p, hp, herr⟩ := exists_laplacePolynomial_reference_eLpNorm_sub_lt j
    (memLp_div_laplaceRegularizer j hf) hε
  have hm : Measurable (fun E : ℝ => p.eval (Real.exp (-E) : ℂ)) := by fun_prop
  have hq : Measurable (fun E => (laplaceRegularizer E : ℂ)) :=
    (Complex.continuous_ofReal.comp continuous_laplaceRegularizer).measurable
  refine ⟨p, ?_, ?_⟩
  · change eLpNorm _ _ _ < ∞
    rw [laplaceRegularizer_norm_identity j hm.aestronglyMeasurable]
    exact hp.eLpNorm_lt_top
  · have hdiff : AEStronglyMeasurable
        (fun E => f E / (laplaceRegularizer E : ℂ) - p.eval (Real.exp (-E) : ℂ))
        (energySpaceMeasure j) :=
      (hf.aemeasurable.div hq.aemeasurable).aestronglyMeasurable.sub hm.aestronglyMeasurable
    have heq : (fun E => f E - (laplaceRegularizer E : ℂ) * p.eval (Real.exp (-E) : ℂ)) =ᵐ[
        energySpaceMeasure j] (fun E => (laplaceRegularizer E : ℂ) *
          (f E / (laplaceRegularizer E : ℂ) - p.eval (Real.exp (-E) : ℂ))) := by
      filter_upwards [laplaceRegularizer_energy_ae_pos j] with E hE
      have hn : (laplaceRegularizer E : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hE
      rw [mul_sub, mul_div_cancel₀ _ hn]
    rw [eLpNorm_congr_ae heq, laplaceRegularizer_norm_identity j hdiff]
    exact herr

/-- Every weighted energy-row vector is approximated by a finite sum of actual
adjacent-height Laplace tests, each of which vanishes at the scalar origin. -/
theorem exists_finite_laplaceTest_eLpNorm_sub_lt (j : ℤ) {f : ℝ → ℂ}
    (hf : MemLp f 2 (energySpaceMeasure j)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (c : Fin n → ℂ),
      MemLp (fun E => ∑ k, c k * (laplaceTest k.val E : ℂ)) 2 (energySpaceMeasure j) ∧
      eLpNorm (fun E => f E - ∑ k, c k * (laplaceTest k.val E : ℂ))
        2 (energySpaceMeasure j) < ENNReal.ofReal ε := by
  obtain ⟨p, hp, herr⟩ := exists_regularized_laplacePolynomial_eLpNorm_sub_lt j hf hε
  have heq (E : ℝ) : (laplaceRegularizer E : ℂ) * p.eval (Real.exp (-E) : ℂ) =
      ∑ k : Fin (p.natDegree + 1), p.coeff k.val * (laplaceTest k.val E : ℂ) := by
    rw [regularized_polynomial_eq_finite_laplaceTest]
    exact (Fin.sum_univ_eq_sum_range (fun k => p.coeff k * (laplaceTest k E : ℂ)) _).symm
  refine ⟨p.natDegree + 1, fun k => p.coeff k.val, ?_, ?_⟩
  · simpa only [heq] using hp
  · simpa only [heq] using herr

end GapFamily.Analytic
