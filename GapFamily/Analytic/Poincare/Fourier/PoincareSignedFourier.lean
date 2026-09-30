import GapFamily.Analytic.Poincare.Continuation.PoincareCompactSuperposition
import GapFamily.Analytic.Poincare.Fourier.PoincareGeneralFourier

/-!
# Ordinary Fourier coefficients of signed seed superpositions

A bounded physical signed input is integrable in the compact row norm. The
bounded horizontal Fourier functional therefore commutes with its ordinary
signed integral. The finite-spin formula retains the actual global seed.
-/

noncomputable section

namespace GapFamily.Analytic.PoincareEnergyFourier

open Set Filter MeasureTheory UpperHalfPlane
open PoincareCanonical PoincareEnergyContinuation PoincareFourierContinuation PoincareFourier
open DominatedAnalytic

/-- The compact-energy coefficient bound gives genuine signed integrability
for every bounded physical row. -/
theorem signedIntegrable_generalThresholdFourierCoefficient
    (y : ℝ) (hy : 0 < y) (ν : SignedMeasure ℝ) (j J : ℤ) (B : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ B) :
    ν.Integrable (fun E : ℝ => generalThresholdFourierCoefficient y hy E j J) := by
  let := signedMeasure_isFiniteMeasure_variation ν
  obtain ⟨C, hC, hb⟩ := generalThresholdFourierCoefficient_uniform_bound y hy B
  have hc : Continuous (fun E : ℝ => generalThresholdFourierCoefficient y hy E j J) :=
    (continuous_iff_continuousAt.mpr fun E =>
      (analyticAt_generalThresholdFourierCoefficient_energy y hy j J E).continuousAt).comp
        Complex.continuous_ofReal
  apply (integrable_const (C * (1 + (J : ℝ) ^ 2 + B))).mono' hc.aestronglyMeasurable
  filter_upwards [hs] with E hE
  have hE0 : 0 ≤ E := (abs_nonneg (J : ℝ)).trans hE.1
  have hn : ‖(E : ℂ)‖ = E := by simp [Complex.norm_real, abs_of_nonneg hE0]
  have hh := hb E (by simpa only [hn] using hE.2) j J
  rw [hn] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (by linarith [hE.2]) hC.le)

/-- A bounded complex linear functional commutes with the ordinary compact
signed integral, using both integrable Jordan parts. -/
theorem signedIntegral_compact_clm (K : Set ℂ) [CompactSpace K]
    (ν : SignedMeasure ℝ) (L : C(K, ℂ) →L[ℂ] ℂ)
    {F : ℝ → C(K, ℂ)} (hf : ν.Integrable F) :
    L (∫ᵛ E, F E ∂<•ν) = ∫ᵛ E, L (F E) ∂<•ν := by
  have hi : Integrable F
      (ν.toJordanDecomposition.posPart + ν.toJordanDecomposition.negPart) := by
    simpa only [VectorMeasure.Integrable, ← SignedMeasure.totalVariation_eq_variation,
      SignedMeasure.totalVariation] using hf
  have hL : ν.Integrable (fun E => L (F E)) := L.integrable_comp hf
  rw [signedIntegral_eq_jordan hf, signedIntegral_eq_jordan hL, map_sub,
    L.integral_comp_comm hi.left_of_add_measure, L.integral_comp_comm hi.right_of_add_measure]

/-- The actual signed seed has an ordinary integrable horizontal Fourier integrand. -/
theorem intervalIntegrable_rowSeedSuperposition_fourier
    (y : ℝ) (hy : 0 < y) (ν : SignedMeasure ℝ) (j J : ℤ) (B : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ B) :
    IntervalIntegrable (fun x => cuspFourierMode (-j) x *
      rowSeedSuperposition ν J (rowPoint y hy x)) volume 0 1 :=
  ((contDiff_cuspFourierMode (-j)).continuous.mul
    ((continuous_rowSeedSuperposition ν J B hs).comp (continuous_rowPoint y hy))).intervalIntegrable 0 1

/-- The ordinary horizontal Fourier coefficient of the actual row superposition
is exactly the signed integral of its actual point-seed coefficients. -/
theorem rowSeedSuperposition_fourier
    (y : ℝ) (hy : 0 < y) (ν : SignedMeasure ℝ) (j J : ℤ) (B : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ B) :
    (∫ x in (0 : ℝ)..1, cuspFourierMode (-j) x *
      rowSeedSuperposition ν J (rowPoint y hy x)) =
        ∫ᵛ E : ℝ, generalThresholdFourierCoefficient y hy E j J ∂<•ν := by
  let K := horizontalRow y
  let hKH := horizontalRow_subset_upperHalfPlaneSet y hy
  let F := rowContinuationOn K hKH ν J 0
  have he : ∀ (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1),
      F ⟨Complex.mk x y, ⟨x, hx, rfl⟩⟩ = rowSeedSuperposition ν J (rowPoint y hy x) := by
    intro x hx
    exact rowContinuationOn_zero K hKH ν J B hs (rowPoint y hy x) ⟨x, hx, rfl⟩
  rw [← horizontalFourierFunctional_eq_intervalIntegral y j F _ he]
  change horizontalFourierFunctional y j
    (∫ᵛ E : ℝ, continuedSeedOn K hKH E J 0 ∂<•ν) = _
  rw [signedIntegral_compact_clm K ν (horizontalFourierFunctional y j)
    (rowContinuationOn_integrable K hKH ν J B hs (by norm_num))]
  apply VectorMeasure.integral_congr_ae
  exact Eventually.of_forall fun E => continuedEnergyFourierCoefficient_zero y hy E j J

/-- Finite physical signed-spin superpositions have genuinely integrable ordinary
horizontal Fourier integrands. -/
theorem intervalIntegrable_finiteSeedSuperposition_fourier
    (y : ℝ) (hy : 0 < y) (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ) (j : ℤ) (B : ℝ)
    (hs : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ B) :
    IntervalIntegrable (fun x => cuspFourierMode (-j) x *
      finiteSeedSuperposition S ν (rowPoint y hy x)) volume 0 1 :=
  ((contDiff_cuspFourierMode (-j)).continuous.mul
    ((continuous_finiteSeedSuperposition S ν B hs).comp
      (continuous_rowPoint y hy))).intervalIntegrable 0 1

/-- The finite signed-seed Fourier coefficient is the ordinary finite sum of
signed point-seed coefficients; no Fourier-integrability input is assumed. -/
theorem finiteSeedSuperposition_fourier
    (y : ℝ) (hy : 0 < y) (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ) (j : ℤ) (B : ℝ)
    (hs : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ B) :
    (∫ x in (0 : ℝ)..1, cuspFourierMode (-j) x *
      finiteSeedSuperposition S ν (rowPoint y hy x)) =
        ∑ J ∈ S, ∫ᵛ E : ℝ, generalThresholdFourierCoefficient y hy E j J ∂<•(ν J) := by
  simp only [finiteSeedSuperposition, Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum
    (fun J hJ => intervalIntegrable_rowSeedSuperposition_fourier y hy (ν J) j J B (hs J hJ))]
  exact Finset.sum_congr rfl fun J hJ => rowSeedSuperposition_fourier y hy (ν J) j J B (hs J hJ)

end GapFamily.Analytic.PoincareEnergyFourier
