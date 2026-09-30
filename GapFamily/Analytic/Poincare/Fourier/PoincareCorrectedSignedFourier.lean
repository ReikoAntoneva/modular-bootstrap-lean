import GapFamily.Analytic.Poincare.Fourier.PoincareSignedFourier
import GapFamily.Analytic.Poincare.Fourier.PoincareCorrectedFourierLaplace

/-!
# Corrected signed seed and its ordinary Fourier coefficient

The scalar rank correction is an actual spatial constant, determined by the
ordinary signed square-root moment. Its Fourier coefficient is identified
with the signed integral of the corrected point coefficient.
-/

noncomputable section

namespace GapFamily.Analytic.PoincareEnergyContinuation

open Set Filter MeasureTheory UpperHalfPlane
open scoped MatrixGroups

/-- Bounded input support makes the square-root moment ordinarily integrable. -/
theorem signedIntegrable_sqrt_of_bounded_above (ν : SignedMeasure ℝ) (B : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, E ≤ B) : ν.Integrable Real.sqrt := by
  let := signedMeasure_isFiniteMeasure_variation ν
  apply (integrable_const (Real.sqrt B)).mono' Real.continuous_sqrt.aestronglyMeasurable
  filter_upwards [hs] with E hE
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg E)] using Real.sqrt_le_sqrt hE

/-- The actual corrected signed row adds its scalar square-root moment as a
spatial constant. -/
def correctedRowSeed (ν : SignedMeasure ℝ) (J : ℤ) (τ : UpperHalfPlane) : ℂ :=
  rowSeedSuperposition ν J τ +
    if J = 0 then ((12 / Real.sqrt 2 : ℝ) : ℂ) *
      (∫ᵛ E : ℝ, (Real.sqrt E : ℂ) ∂<•ν) else 0

/-- The ordinary scalar square-root moment of a finite signed input. -/
def scalarSignedSqrtMoment (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ) : ℝ :=
  if 0 ∈ S then ∫ᵛ E : ℝ, Real.sqrt E ∂<•(ν 0) else 0

/-- The actual finite corrected modular seed. -/
def correctedSeedSuperposition (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ)
    (τ : UpperHalfPlane) : ℂ :=
  ∑ J ∈ S, correctedRowSeed (ν J) J τ

/-- The point rank coefficient has the same fixed multiplier as the signed row. -/
theorem pointSqrtRank_eq_mul (E : ℝ) :
    ((12 * Real.sqrt E / Real.sqrt 2 : ℝ) : ℂ) =
      ((12 / Real.sqrt 2 : ℝ) : ℂ) * (Real.sqrt E : ℂ) := by
  push_cast
  ring

/-- The actual corrected point seed is integrable against every bounded
physical signed input row. -/
theorem signedIntegrable_correctedPointSeed (ν : SignedMeasure ℝ) (J : ℤ) (B : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ B) (τ : UpperHalfPlane) :
    ν.Integrable (fun E : ℝ => correctedPointSeed E J τ) := by
  have hi : ν.Integrable (fun E : ℝ => (Real.sqrt E : ℂ)) :=
    (signedIntegrable_sqrt_of_bounded_above ν B (hs.mono fun _ h => h.2)).ofReal
  simp only [correctedPointSeed, pointSqrtRank_eq_mul]
  apply (rowSeedSuperposition_integrable ν J B hs τ).add
  by_cases hJ : J = 0
  · simpa only [hJ, ite_true] using hi.const_mul ((12 / Real.sqrt 2 : ℝ) : ℂ)
  · simp only [hJ, ite_false]
    exact integrable_zero _ _ _

/-- The corrected row is precisely the ordinary signed integral of the
actual corrected point seeds. -/
theorem correctedRowSeed_eq_signedIntegral (ν : SignedMeasure ℝ) (J : ℤ) (B : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ B) (τ : UpperHalfPlane) :
    correctedRowSeed ν J τ = ∫ᵛ E : ℝ, correctedPointSeed E J τ ∂<•ν := by
  have hi : ν.Integrable (fun E : ℝ => (Real.sqrt E : ℂ)) :=
    (signedIntegrable_sqrt_of_bounded_above ν B (hs.mono fun _ h => h.2)).ofReal
  by_cases hJ : J = 0
  · simp only [correctedRowSeed, correctedPointSeed, hJ, ite_true, pointSqrtRank_eq_mul]
    rw [VectorMeasure.integral_fun_add (rowSeedSuperposition_integrable ν 0 B (by simpa [hJ] using hs) τ)
      (hi.const_mul ((12 / Real.sqrt 2 : ℝ) : ℂ)), signedIntegral_const_mul hi]
    rfl
  · simp only [correctedRowSeed, correctedPointSeed, hJ, ite_false, add_zero,
      rowSeedSuperposition]

/-- The scalar moment correction preserves the actual global modular identity. -/
theorem correctedRowSeed_smul (ν : SignedMeasure ℝ) (J : ℤ)
    (τ : UpperHalfPlane) (g : SL(2, ℤ)) :
    correctedRowSeed ν J (g • τ) = correctedRowSeed ν J τ := by
  simp only [correctedRowSeed, rowSeedSuperposition_smul]

/-- Bounded physical signed inputs give continuous corrected rows. -/
theorem continuous_correctedRowSeed (ν : SignedMeasure ℝ) (J : ℤ) (B : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ B) :
    Continuous (correctedRowSeed ν J) :=
  (continuous_rowSeedSuperposition ν J B hs).add continuous_const

/-- The actual finite corrected seed is modular. -/
theorem correctedSeedSuperposition_smul (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ)
    (τ : UpperHalfPlane) (g : SL(2, ℤ)) :
    correctedSeedSuperposition S ν (g • τ) = correctedSeedSuperposition S ν τ := by
  simp only [correctedSeedSuperposition, correctedRowSeed_smul]

/-- The finite corrected seed is continuous under bounded physical support. -/
theorem continuous_correctedSeedSuperposition (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ)
    (B : ℝ) (hs : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ B) :
    Continuous (correctedSeedSuperposition S ν) :=
  continuous_finsetSum S fun J hJ => continuous_correctedRowSeed (ν J) J B (hs J hJ)

/-- The actual finite corrected seed adds exactly `12 m_g / sqrt 2`, where
`m_g` is its ordinary real scalar square-root moment. -/
theorem correctedSeedSuperposition_eq_add_scalarMoment
    (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ) (B : ℝ)
    (hs : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ B)
    (τ : UpperHalfPlane) :
    correctedSeedSuperposition S ν τ = finiteSeedSuperposition S ν τ +
      ((12 * scalarSignedSqrtMoment S ν / Real.sqrt 2 : ℝ) : ℂ) := by
  classical
  have hi : 0 ∈ S → (ν 0).Integrable Real.sqrt := fun h0 =>
    signedIntegrable_sqrt_of_bounded_above (ν 0) B ((hs 0 h0).mono fun _ h => h.2)
  simp only [correctedSeedSuperposition, correctedRowSeed, Finset.sum_add_distrib,
    finiteSeedSuperposition]
  congr 1
  by_cases h0 : 0 ∈ S
  · simp only [Finset.sum_ite_eq', h0, ite_true, scalarSignedSqrtMoment,
      signedIntegral_complex_ofReal (hi h0)]
    push_cast
    ring
  · simp [Finset.sum_ite_eq', h0, scalarSignedSqrtMoment]

end GapFamily.Analytic.PoincareEnergyContinuation

namespace GapFamily.Analytic.PoincareEnergyFourier

open Set Filter MeasureTheory UpperHalfPlane PoincareEnergyContinuation PoincareFourier

private theorem signedIntegrable_pointFourierRank (ν : SignedMeasure ℝ) (j J : ℤ)
    (B : ℝ) (hs : ∀ᵐ E ∂ν.variation, E ≤ B) :
    ν.Integrable (fun E : ℝ =>
      if j = 0 ∧ J = 0 then ((12 * Real.sqrt E / Real.sqrt 2 : ℝ) : ℂ) else 0) := by
  have hi : ν.Integrable (fun E : ℝ => (Real.sqrt E : ℂ)) :=
    (signedIntegrable_sqrt_of_bounded_above ν B hs).ofReal
  by_cases h : j = 0 ∧ J = 0
  · simpa only [ite_eq_left h, pointSqrtRank_eq_mul, VectorMeasure.Integrable] using
      hi.const_mul ((12 / Real.sqrt 2 : ℝ) : ℂ)
  · simp only [ite_eq_right h]
    exact integrable_zero _ _ _

/-- The actual corrected point Fourier coefficients are signed integrable,
with their scalar rank term controlled by bounded support. -/
theorem signedIntegrable_correctedPointFourierCoefficient
    (y : ℝ) (hy : 0 < y) (ν : SignedMeasure ℝ) (j J : ℤ) (B : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ B) :
    ν.Integrable (fun E : ℝ => correctedPointFourierCoefficient y hy E j J) := by
  simp_rw [correctedPointFourierCoefficient_eq_add_rank]
  exact (signedIntegrable_generalThresholdFourierCoefficient y hy ν j J B hs).add
    (signedIntegrable_pointFourierRank ν j J B (hs.mono fun _ h => h.2))

/-- The corrected row has a genuinely integrable ordinary Fourier integrand. -/
theorem intervalIntegrable_correctedRowSeed_fourier
    (y : ℝ) (hy : 0 < y) (ν : SignedMeasure ℝ) (j J : ℤ) (B : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ B) :
    IntervalIntegrable (fun x => cuspFourierMode (-j) x *
      correctedRowSeed ν J (rowPoint y hy x)) volume 0 1 :=
  ((contDiff_cuspFourierMode (-j)).continuous.mul
    ((continuous_correctedRowSeed ν J B hs).comp (continuous_rowPoint y hy))).intervalIntegrable 0 1

/-- The actual corrected row's ordinary Fourier coefficient commutes with the
signed point-seed integral, including the exact scalar rank coefficient. -/
theorem correctedRowSeed_fourier
    (y : ℝ) (hy : 0 < y) (ν : SignedMeasure ℝ) (j J : ℤ) (B : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ B) :
    (∫ x in (0 : ℝ)..1, cuspFourierMode (-j) x *
      correctedRowSeed ν J (rowPoint y hy x)) =
        ∫ᵛ E : ℝ, correctedPointFourierCoefficient y hy E j J ∂<•ν := by
  have hi : ν.Integrable (fun E : ℝ => (Real.sqrt E : ℂ)) :=
    (signedIntegrable_sqrt_of_bounded_above ν B (hs.mono fun _ h => h.2)).ofReal
  have hc : IntervalIntegrable (fun x : ℝ => cuspFourierMode (-j) x *
      (if J = 0 then ((12 / Real.sqrt 2 : ℝ) : ℂ) *
        (∫ᵛ E : ℝ, (Real.sqrt E : ℂ) ∂<•ν) else 0)) volume 0 1 :=
    ((contDiff_cuspFourierMode (-j)).continuous.mul continuous_const).intervalIntegrable 0 1
  unfold correctedRowSeed
  simp only [mul_add]
  rw [intervalIntegral.integral_add
    (intervalIntegrable_rowSeedSuperposition_fourier y hy ν j J B hs)
    hc,
    intervalIntegral.integral_mul_const, integral_cuspFourierMode_zero_one,
    rowSeedSuperposition_fourier y hy ν j J B hs]
  simp_rw [correctedPointFourierCoefficient_eq_add_rank]
  rw [VectorMeasure.integral_fun_add
    (signedIntegrable_generalThresholdFourierCoefficient y hy ν j J B hs)
    (signedIntegrable_pointFourierRank ν j J B (hs.mono fun _ h => h.2))]
  simp_rw [pointSqrtRank_eq_mul]
  by_cases hj : j = 0
  · by_cases hJ : J = 0
    · simp only [hj, hJ, neg_zero, ite_true, and_self, one_mul]
      rw [signedIntegral_const_mul hi]
    · simp [hJ]
  · simp [hj]

/-- The actual finite corrected seed has an ordinary integrable Fourier integrand. -/
theorem intervalIntegrable_correctedSeedSuperposition_fourier
    (y : ℝ) (hy : 0 < y) (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ) (j : ℤ) (B : ℝ)
    (hs : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ B) :
    IntervalIntegrable (fun x => cuspFourierMode (-j) x *
      correctedSeedSuperposition S ν (rowPoint y hy x)) volume 0 1 :=
  ((contDiff_cuspFourierMode (-j)).continuous.mul
    ((continuous_correctedSeedSuperposition S ν B hs).comp
      (continuous_rowPoint y hy))).intervalIntegrable 0 1

/-- The corrected finite signed seed's ordinary Fourier coefficient is exactly
the finite sum of signed corrected point coefficients. -/
theorem correctedSeedSuperposition_fourier
    (y : ℝ) (hy : 0 < y) (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ) (j : ℤ) (B : ℝ)
    (hs : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ B) :
    (∫ x in (0 : ℝ)..1, cuspFourierMode (-j) x *
      correctedSeedSuperposition S ν (rowPoint y hy x)) =
        ∑ J ∈ S, ∫ᵛ E : ℝ, correctedPointFourierCoefficient y hy E j J ∂<•(ν J) := by
  simp only [correctedSeedSuperposition, Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum
    (fun J hJ => intervalIntegrable_correctedRowSeed_fourier y hy (ν J) j J B (hs J hJ))]
  exact Finset.sum_congr rfl fun J hJ => correctedRowSeed_fourier y hy (ν J) j J B (hs J hJ)

end GapFamily.Analytic.PoincareEnergyFourier
