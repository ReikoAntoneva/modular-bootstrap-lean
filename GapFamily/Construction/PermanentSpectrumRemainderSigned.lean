import GapFamily.Analytic.Poincare.Poincare
import GapFamily.Analytic.Foundation.SignedMomentIntegral
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-! Signed threshold seed transforms have genuine variation-measure
integrability. Summable thermal variation budgets control their actual
absolute series and the vanishing remainder of its finite prefixes. -/

noncomputable section
namespace GapFamily.Construction

open MeasureTheory Filter
open scoped Topology UpperHalfPlane

/-- The actual scalar signed integral of a threshold point seed. Its ordinary
variation-measure integrability is proved below from the thermal budget. -/
def signedPointSeedHalf (ν : SignedMeasure ℝ) (J : ℤ) (τ : ℍ) : ℂ :=
  ∫ᵛ E, Analytic.pointSeed E J (1 / 2) τ ∂<•ν

theorem norm_pointSeed_half_eq_thermal (E : ℝ) (J : ℤ) (τ : ℍ) :
    ‖Analytic.pointSeed E J (1 / 2) τ‖ =
      Real.sqrt τ.im * Real.exp (-2 * Real.pi * τ.im * E) := by
  rw [Analytic.norm_pointSeed, ← Real.sqrt_eq_rpow]
  congr 2
  ring

/-- The thermal variation integral simultaneously certifies integrability
of the actual signed transform and bounds its complex norm. -/
theorem signedPointSeedHalf_integrable_and_norm_le
    (ν : SignedMeasure ℝ) (J : ℤ) (τ : ℍ)
    (hthermal : Integrable (fun E : ℝ => Real.exp (-2 * Real.pi * τ.im * E))
      ν.variation) :
    ν.Integrable (fun E => Analytic.pointSeed E J (1 / 2) τ) ∧
      ‖signedPointSeedHalf ν J τ‖ ≤ Real.sqrt τ.im *
        ∫ E : ℝ, Real.exp (-2 * Real.pi * τ.im * E) ∂ν.variation := by
  constructor
  · apply (hthermal.const_mul (Real.sqrt τ.im)).mono'
    · apply Continuous.aestronglyMeasurable
      unfold Analytic.pointSeed
      fun_prop
    · exact Eventually.of_forall fun E => (norm_pointSeed_half_eq_thermal E J τ).le
  · have h := VectorMeasure.norm_integral_le_integral_norm
      (B := (ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ)).flip)
      (μ := ν) (f := fun E => Analytic.pointSeed E J (1 / 2) τ)
    simpa only [signedPointSeedHalf, ContinuousLinearMap.opNorm_flip,
      ContinuousLinearMap.opNorm_lsmul, one_mul, norm_pointSeed_half_eq_thermal,
      integral_const_mul] using h

theorem signedIntegrable_pointSeed_half
    (ν : SignedMeasure ℝ) (J : ℤ) (τ : ℍ)
    (hthermal : Integrable (fun E : ℝ => Real.exp (-2 * Real.pi * τ.im * E))
      ν.variation) :
    ν.Integrable (fun E => Analytic.pointSeed E J (1 / 2) τ) :=
  (signedPointSeedHalf_integrable_and_norm_le ν J τ hthermal).1

theorem norm_signedPointSeedHalf_le
    (ν : SignedMeasure ℝ) (J : ℤ) (τ : ℍ)
    (hthermal : Integrable (fun E : ℝ => Real.exp (-2 * Real.pi * τ.im * E))
      ν.variation) :
    ‖signedPointSeedHalf ν J τ‖ ≤ Real.sqrt τ.im *
      ∫ E : ℝ, Real.exp (-2 * Real.pi * τ.im * E) ∂ν.variation :=
  (signedPointSeedHalf_integrable_and_norm_le ν J τ hthermal).2

/-- An arbitrary indexed signed residual family has an absolutely convergent
actual transform series whenever its thermal variation masses are summable.
The index may be a dependent family of finite layer slots. -/
theorem signedPointSeedHalf_norm_summable {κ : Type*}
    (ν : κ → SignedMeasure ℝ) (J : κ → ℤ) (τ : ℍ)
    (hthermal : ∀ i, Integrable (fun E : ℝ => Real.exp (-2 * Real.pi * τ.im * E))
      (ν i).variation)
    (hsum : Summable (fun i => ∫ E : ℝ, Real.exp (-2 * Real.pi * τ.im * E)
      ∂(ν i).variation)) :
    Summable (fun i => ‖signedPointSeedHalf (ν i) (J i) τ‖) := by
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun i => norm_signedPointSeedHalf_le (ν i) (J i) τ (hthermal i))
    (hsum.mul_left (Real.sqrt τ.im))

theorem signedPointSeedHalf_summable {κ : Type*}
    (ν : κ → SignedMeasure ℝ) (J : κ → ℤ) (τ : ℍ)
    (hthermal : ∀ i, Integrable (fun E : ℝ => Real.exp (-2 * Real.pi * τ.im * E))
      (ν i).variation)
    (hsum : Summable (fun i => ∫ E : ℝ, Real.exp (-2 * Real.pi * τ.im * E)
      ∂(ν i).variation)) :
    Summable (fun i => signedPointSeedHalf (ν i) (J i) τ) :=
  (signedPointSeedHalf_norm_summable ν J τ hthermal hsum).of_norm

/-- The genuine signed transform series minus its finite prefix tends to zero. -/
theorem tendsto_signedPointSeedHalf_remainder
    (ν : ℕ → SignedMeasure ℝ) (J : ℕ → ℤ) (τ : ℍ)
    (hthermal : ∀ n, Integrable (fun E : ℝ => Real.exp (-2 * Real.pi * τ.im * E))
      (ν n).variation)
    (hsum : Summable (fun n => ∫ E : ℝ, Real.exp (-2 * Real.pi * τ.im * E)
      ∂(ν n).variation)) :
    Tendsto (fun N => (∑' n, signedPointSeedHalf (ν n) (J n) τ) -
      ∑ n ∈ Finset.range N, signedPointSeedHalf (ν n) (J n) τ) atTop (𝓝 0) := by
  have h := (signedPointSeedHalf_summable ν J τ hthermal hsum).hasSum.tendsto_sum_nat
  simpa only [sub_self] using
    (tendsto_const_nhds (x := ∑' n, signedPointSeedHalf (ν n) (J n) τ)).sub h

/-- The same remainder as a literal shifted infinite tail of actual transforms. -/
theorem tendsto_signedPointSeedHalf_tail
    (ν : ℕ → SignedMeasure ℝ) (J : ℕ → ℤ) (τ : ℍ)
    (hthermal : ∀ n, Integrable (fun E : ℝ => Real.exp (-2 * Real.pi * τ.im * E))
      (ν n).variation)
    (hsum : Summable (fun n => ∫ E : ℝ, Real.exp (-2 * Real.pi * τ.im * E)
      ∂(ν n).variation)) :
    Tendsto (fun N => ∑' n, signedPointSeedHalf (ν (n + N)) (J (n + N)) τ)
      atTop (𝓝 0) := by
  have hs := signedPointSeedHalf_summable ν J τ hthermal hsum
  have heq (N : ℕ) :
      (∑' n, signedPointSeedHalf (ν (n + N)) (J (n + N)) τ) =
        (∑' n, signedPointSeedHalf (ν n) (J n) τ) -
          ∑ n ∈ Finset.range N, signedPointSeedHalf (ν n) (J n) τ := by
    rw [← hs.sum_add_tsum_nat_add N, add_sub_cancel_left]
  simp_rw [heq]
  exact tendsto_signedPointSeedHalf_remainder ν J τ hthermal hsum

end GapFamily.Construction
