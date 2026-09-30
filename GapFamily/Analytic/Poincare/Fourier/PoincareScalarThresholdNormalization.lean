import GapFamily.Analytic.Poincare.Fourier.PoincareNonzeroScalarAsymptotic
import GapFamily.Analytic.Poincare.Fourier.PoincareComplexEnergyTail

/-!
The scalar cusp normalization of the actual canonical point seed.
Subtracting the direct input term makes the result valid at every complex
energy, including the four negative-energy vacuum inputs. These theorems
identify ordinary Fourier asymptotics; a measure decomposition still requires
the Fourier–Laplace transform of the continuum.
-/

noncomputable section

namespace GapFamily.Analytic.PoincareScalarFourier

open Filter MeasureTheory PoincareEnergyFourier PoincareFourierContinuation
open PoincareEnergyContinuation PoincareFourier
open PoincareFourierRemainder
open scoped Topology

/-- The source coefficient `c_J`: minus one for scalar input and twice the
divisor count for nonzero input spin. -/
def scalarThresholdCoefficient (J : ℤ) : ℂ :=
  if J = 0 then -1 else 2 * (J.natAbs.divisors.card : ℂ)

@[simp] theorem scalarThresholdCoefficient_zero : scalarThresholdCoefficient 0 = -1 := by
  simp [scalarThresholdCoefficient]

@[simp] theorem scalarThresholdCoefficient_one : scalarThresholdCoefficient 1 = 2 := by
  norm_num [scalarThresholdCoefficient]

@[simp] theorem scalarThresholdCoefficient_neg_one : scalarThresholdCoefficient (-1) = 2 := by
  norm_num [scalarThresholdCoefficient]

/-- The exact scalar row separates the direct input, the scalar threshold
coefficient, and both intact ordinary convergent corrections. -/
theorem generalThresholdFourierCoefficient_zero_eq_direct_add_threshold_add_corrections
    (y : ℝ) (hy : 0 < y) (E : ℂ) (J : ℤ) :
    generalThresholdFourierCoefficient y hy E 0 J =
      (if J = 0 then (Real.sqrt y : ℂ) *
        Complex.exp (-2 * (Real.pi : ℂ) * E * (y : ℂ)) else 0) +
      (Real.sqrt y : ℂ) * scalarThresholdCoefficient J +
      fourierRemainder y 0 J (1 / 2 : ℂ) +
      ∑' n : ℕ, kloostermanSum 0 J n *
        ∫ t : ℝ, energyFourierKernel (n + 1 : ℕ) y E 0 J (1 / 2 : ℂ) t := by
  by_cases hJ : J = 0
  · subst J
    have hp : (y : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt y : ℂ) := by
      calc
        (y : ℂ) ^ (1 / 2 : ℂ) = ((y ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
          simpa using (Complex.ofReal_cpow hy.le (1 / 2 : ℝ)).symm
        _ = _ := by rw [← Real.sqrt_eq_rpow]
    rw [generalThresholdFourierCoefficient_eq_base_add_kloosterman,
      thresholdFourierCoefficient_zero_zero, zero_add, energyFourierDirect,
      ite_eq_left rfl, hp, ite_eq_left rfl, scalarThresholdCoefficient_zero]
    simp only [fourierRemainder, fourierRemainderKernel_eq_sub, sub_self,
      integral_zero, mul_zero, tsum_zero, add_zero]
    ring
  · simpa only [ite_eq_right hJ, scalarThresholdCoefficient, zero_add] using
      generalThresholdFourierCoefficient_zero_eq_divisor_add_corrections y hy E J hJ

/-- The normalized actual scalar Fourier coefficient after removing the direct
point input. The auxiliary value at nonpositive height is irrelevant at infinity. -/
def scalarFourierAfterDirect (E : ℂ) (J : ℤ) (y : ℝ) : ℂ :=
  if hy : 0 < y then
    generalThresholdFourierCoefficient y hy E 0 J / (Real.sqrt y : ℂ) -
      if J = 0 then Complex.exp (-2 * (Real.pi : ℂ) * E * (y : ℂ)) else 0
  else 0

/-- The exact normalized error consists of the two convergent denominator
corrections, so no cancellation of divergent series is involved. -/
theorem scalarFourierAfterDirect_sub_threshold_eq (E : ℂ) (J : ℤ)
    {y : ℝ} (hy : 0 < y) :
    scalarFourierAfterDirect E J y - scalarThresholdCoefficient J =
      (fourierRemainder y 0 J (1 / 2 : ℂ) +
        ∑' n : ℕ, kloostermanSum 0 J n *
          ∫ t : ℝ, energyFourierKernel (n + 1 : ℕ) y E 0 J (1 / 2 : ℂ) t) /
        (Real.sqrt y : ℂ) := by
  have hs : (Real.sqrt y : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 hy).ne'
  rw [scalarFourierAfterDirect, dite_eq_left hy,
    generalThresholdFourierCoefficient_zero_eq_direct_add_threshold_add_corrections]
  by_cases hJ : J = 0
  · simp only [ite_eq_left hJ]
    field_simp [hs]
    ring
  · simp only [ite_eq_right hJ]
    field_simp [hs]
    ring

/-- A uniform cusp error bound for all complex energies and both scalar input
cases. Bounded energy and input spin give a common bound for finite seed measures. -/
theorem norm_scalarFourierAfterDirect_sub_threshold_le (E : ℂ) (J : ℤ)
    {y : ℝ} (hy : 1 ≤ y) :
    ‖scalarFourierAfterDirect E J y - scalarThresholdCoefficient J‖ ≤
      (fourierRemainderThresholdConstant * |(J : ℝ)| +
        (2 * Real.pi ^ 2 * ‖E‖ * Real.exp (2 * Real.pi * ‖E‖)) *
          ∑' n : ℕ, 1 / ((n + 1 : ℕ) : ℝ) ^ 2) / y := by
  have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one hy
  rw [scalarFourierAfterDirect_sub_threshold_eq E J hy0, norm_div,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg y)]
  calc
    _ ≤ (‖fourierRemainder y 0 J (1 / 2 : ℂ)‖ +
        ‖∑' n : ℕ, kloostermanSum 0 J n *
          ∫ t : ℝ, energyFourierKernel (n + 1 : ℕ) y E 0 J (1 / 2 : ℂ) t‖) /
          Real.sqrt y :=
      div_le_div_of_nonneg_right (norm_add_le _ _) (Real.sqrt_nonneg y)
    _ ≤ (fourierRemainderThresholdConstant * |(J : ℝ)| / Real.sqrt y +
        ((2 * Real.pi ^ 2 * ‖E‖ * Real.exp (2 * Real.pi * ‖E‖)) / Real.sqrt y) *
          ∑' n : ℕ, 1 / ((n + 1 : ℕ) : ℝ) ^ 2) / Real.sqrt y :=
      div_le_div_of_nonneg_right
        (add_le_add (norm_fourierRemainder_threshold_le hy0 0 J)
          (norm_energyFourier_denominator_sum_half_complex_le hy E 0 J))
        (Real.sqrt_nonneg y)
    _ = _ := by
      rw [div_mul_eq_mul_div, ← add_div, div_div, Real.mul_self_sqrt hy0.le]

/-- The scalar direct input is the only energy-dependent leading cusp term.
The normalized denominator correction remains an intact convergent series. -/
theorem scalarFourierAfterDirect_zero_eq (E : ℂ) {y : ℝ} (hy : 0 < y) :
    scalarFourierAfterDirect E 0 y = -1 +
      (∑' n : ℕ, kloostermanSum 0 0 n *
        ∫ t : ℝ, energyFourierKernel (n + 1 : ℕ) y E 0 0 (1 / 2 : ℂ) t) /
        (Real.sqrt y : ℂ) := by
  have hs : (Real.sqrt y : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 hy).ne'
  have hp : (y : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt y : ℂ) := by
    calc
      (y : ℂ) ^ (1 / 2 : ℂ) = ((y ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
        simpa using (Complex.ofReal_cpow hy.le (1 / 2 : ℝ)).symm
      _ = _ := by rw [← Real.sqrt_eq_rpow]
  rw [scalarFourierAfterDirect, dite_eq_left hy, ite_eq_left rfl,
    generalThresholdFourierCoefficient_eq_base_add_kloosterman,
    thresholdFourierCoefficient_zero_zero, zero_add, energyFourierDirect,
    ite_eq_left rfl, hp, add_div, mul_div_cancel_left₀ _ hs]
  ring

/-- Removing the direct point input extracts exactly `c_J`, for arbitrary
complex energy. In particular, this includes negative-energy vacuum seeds. -/
theorem scalarFourierAfterDirect_tendsto (E : ℂ) (J : ℤ) :
    Tendsto (scalarFourierAfterDirect E J) atTop (𝓝 (scalarThresholdCoefficient J)) := by
  by_cases hJ : J = 0
  · subst J
    have h := (tendsto_const_nhds (x := (-1 : ℂ))).add
      (energyFourier_denominator_sum_div_sqrt_tendsto_zero_complex E 0 0)
    simp only [add_zero] at h
    rw [scalarThresholdCoefficient_zero]
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    exact (scalarFourierAfterDirect_zero_eq E hy).symm
  · have h := ((tendsto_const_nhds (x := 2 * (J.natAbs.divisors.card : ℂ))).add
      (fourierRemainder_div_sqrt_tendsto_zero 0 J)).add
      (energyFourier_denominator_sum_div_sqrt_tendsto_zero_complex E 0 J)
    simp only [add_zero] at h
    rw [scalarThresholdCoefficient, ite_eq_right hJ]
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    have hs : (Real.sqrt y : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 hy).ne'
    rw [scalarFourierAfterDirect, dite_eq_left hy, ite_eq_right hJ, sub_zero,
      generalThresholdFourierCoefficient_zero_eq_divisor_add_corrections y hy E J hJ,
      add_div, add_div, mul_div_cancel_left₀ _ hs]

/-- Ordinary finite point-seed superposition preserves the scalar source
coefficient with its actual complex weights. -/
theorem scalarFourierAfterDirect_finset_tendsto {ι : Type*} (A : Finset ι)
    (weight energy : ι → ℂ) (spin : ι → ℤ) :
    Tendsto (fun y : ℝ => ∑ i ∈ A, weight i * scalarFourierAfterDirect (energy i) (spin i) y)
      atTop (𝓝 (∑ i ∈ A, weight i * scalarThresholdCoefficient (spin i))) := by
  exact tendsto_finsetSum A fun i _ =>
    (scalarFourierAfterDirect_tendsto (energy i) (spin i)).const_mul (weight i)

/-- Every positive-energy input has the expected scalar cusp normalization
for every integer input spin; in particular this covers the physical cone. -/
theorem generalThresholdFourier_div_sqrt_tendsto_scalarThresholdCoefficient
    {E : ℝ} (hE : 0 < E) (J : ℤ) :
    Tendsto (fun y : ℝ => if hy : 0 < y then
      generalThresholdFourierCoefficient y hy (E : ℂ) 0 J / (Real.sqrt y : ℂ)
      else 0) atTop (𝓝 (scalarThresholdCoefficient J)) := by
  by_cases hJ : J = 0
  · subst J
    simpa only [scalarThresholdCoefficient_zero] using
      scalarThresholdFourier_div_sqrt_tendsto_neg_one hE
  · simpa only [scalarThresholdCoefficient, ite_eq_right hJ] using
      nonzeroScalarThresholdFourier_div_sqrt_tendsto_divisor hE.le J hJ

/-- The actual four vacuum inputs, with their scalar direct terms removed. -/
def vacuumScalarFourierAfterDirect (a : ℂ) (y : ℝ) : ℂ :=
  scalarFourierAfterDirect (-a) 0 y - scalarFourierAfterDirect (1 - a) 1 y -
    scalarFourierAfterDirect (1 - a) (-1) y + scalarFourierAfterDirect (2 - a) 0 y

/-- The vacuum profile is the ordinary horizontal average of the actual four
canonical seeds, minus their two scalar direct exponentials. -/
theorem vacuumScalarFourierAfterDirect_eq_intervalIntegral (a : ℂ)
    {y : ℝ} (hy : 0 < y) :
    vacuumScalarFourierAfterDirect a y =
      (∫ x in (0 : ℝ)..1,
        generalThresholdSeed (-a) 0 (rowPoint y hy x) -
          generalThresholdSeed (1 - a) 1 (rowPoint y hy x) -
          generalThresholdSeed (1 - a) (-1) (rowPoint y hy x) +
          generalThresholdSeed (2 - a) 0 (rowPoint y hy x)) /
        (Real.sqrt y : ℂ) -
      Complex.exp (-2 * (Real.pi : ℂ) * (-a) * (y : ℂ)) -
      Complex.exp (-2 * (Real.pi : ℂ) * (2 - a) * (y : ℂ)) := by
  have hi (E : ℂ) (J : ℤ) :
      IntervalIntegrable (fun x => generalThresholdSeed E J (rowPoint y hy x)) volume 0 1 := by
    simpa [cuspFourierMode] using
      intervalIntegrable_generalThresholdFourierIntegrand y hy E 0 J
  rw [intervalIntegral.integral_add
      (((hi (-a) 0).sub (hi (1 - a) 1)).sub (hi (1 - a) (-1))) (hi (2 - a) 0),
    intervalIntegral.integral_sub ((hi (-a) 0).sub (hi (1 - a) 1)) (hi (1 - a) (-1)),
    intervalIntegral.integral_sub (hi (-a) 0) (hi (1 - a) 1)]
  simp only [vacuumScalarFourierAfterDirect, scalarFourierAfterDirect, dite_eq_left hy,
    generalThresholdFourierCoefficient, neg_zero, cuspFourierMode, Int.cast_zero,
    mul_zero]
  norm_num
  ring

/-- The prescribed four vacuum signs give scalar threshold coefficient minus six.
The assertion remains meaningful when the direct vacuum term grows exponentially. -/
theorem vacuumScalarFourierAfterDirect_tendsto (a : ℂ) :
    Tendsto (vacuumScalarFourierAfterDirect a) atTop (𝓝 (-6 : ℂ)) := by
  have h := (((scalarFourierAfterDirect_tendsto (-a) 0).sub
    (scalarFourierAfterDirect_tendsto (1 - a) 1)).sub
    (scalarFourierAfterDirect_tendsto (1 - a) (-1))).add
    (scalarFourierAfterDirect_tendsto (2 - a) 0)
  norm_num only [scalarThresholdCoefficient_zero, scalarThresholdCoefficient_one,
    scalarThresholdCoefficient_neg_one] at h
  exact h

end GapFamily.Analytic.PoincareScalarFourier
