import GapFamily.Construction.MarkerReferenceRhs
import GapFamily.Analytic.Kernel.FullKernelResponse
import GapFamily.Analytic.Kernel.FullKernelScalarColumnMoment

/-!
# Quantitative bounds for the actual marker reference right-hand side

The full vacuum contributes an energy-linear term, and the corrected scalar
marker column contributes a square-root term. Both vanish sufficiently at the
scalar endpoint for ordinary `L¹` and Hilbert estimates.
-/

noncomputable section

open MeasureTheory Real Set
open GapFamily.Analytic

namespace GapFamily.Construction

/-- The explicit coefficient of energy in the low-band full vacuum bound. -/
def markerReferenceEnergyBound (a b : ℝ) : ℝ :=
  2 * centralKernelBound + 64 * π ^ 2 * a * exp (4 * π * sqrt (a * b))

theorem markerReferenceEnergyBound_nonneg (a b : ℝ) (ha : 0 ≤ a) :
    0 ≤ markerReferenceEnergyBound a b := by
  unfold markerReferenceEnergyBound
  have := centralKernelBound_pos
  positivity

/-- The actual central-plus-higher vacuum retains its energy factor throughout
the physical low band, uniformly in all output spins. -/
theorem norm_vacuumFullKernel_lowBand_le (a b e : ℝ) (j : ℤ)
    (ha : 2 ≤ a) (he : |(j : ℝ)| ≤ e) (heb : e ≤ b) :
    ‖vacuumFullKernel a e j‖ ≤ markerReferenceEnergyBound a b * e := by
  have ha0 : 0 ≤ a := by linarith
  have he0 : 0 ≤ e := (abs_nonneg _).trans he
  have hC := centralKernelBound_pos.le
  have hc : ‖vacuumCentralKernel j‖ ≤ 2 * centralKernelBound * e :=
    (norm_vacuumCentralKernel_le centralKernelBound norm_centralKernel_le j).trans
      (mul_le_mul_of_nonneg_left he (by positivity))
  have hh : ‖vacuumHigherKernel a e j‖ ≤
      (64 * π ^ 2 * a * exp (4 * π * sqrt (a * b))) * e := by
    calc
      _ ≤ 64 * π ^ 2 * (a * e) * exp (4 * π * sqrt (a * e)) :=
        norm_vacuumHigherKernel_le a e j ha he
      _ ≤ 64 * π ^ 2 * (a * e) * exp (4 * π * sqrt (a * b)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left
          (sqrt_le_sqrt (mul_le_mul_of_nonneg_left heb ha0)) (by positivity)
      _ = _ := by ring
  rw [vacuumFullKernel_eq_central_add_higher]
  exact (norm_add_le _ _).trans ((add_le_add hc hh).trans_eq (by
    unfold markerReferenceEnergyBound
    ring))

/-- The actual C5 forcing has separate energy and square-root majorants. -/
theorem norm_markerReferenceRhs_le (a b e : ℝ) (j : ℤ)
    (ha : 2 ≤ a) (hb : 0 ≤ b) (he : |(j : ℝ)| ≤ e) (heb : e ≤ b) :
    ‖markerReferenceRhs a b j e‖ ≤ markerReferenceEnergyBound a b * e +
      (correctedKernelBound * sqrt b) * sqrt e := by
  have hc : ‖correctedKernel j 0 e b‖ ≤ correctedKernelBound * (sqrt e * sqrt b) := by
    simpa only [Int.cast_zero, abs_zero, mul_zero, zero_add] using
      norm_correctedKernel_le j 0 e b he (by simpa using hb)
  simp only [markerReferenceRhs, norm_neg]
  exact (norm_add_le _ _).trans ((add_le_add
    (norm_vacuumFullKernel_lowBand_le a b e j ha he heb) hc).trans_eq (by ring))

/-- One global coefficient absorbs both types of endpoint vanishing. -/
def markerReferenceCoefficient : ℝ :=
  2 * centralKernelBound + 64 * π ^ 2 + correctedKernelBound

theorem markerReferenceCoefficient_pos : 0 < markerReferenceCoefficient := by
  unfold markerReferenceCoefficient
  have := centralKernelBound_pos
  have := correctedKernelBound_pos
  positivity

/-- The square-root exponential dependence on the vacuum and marker scales. -/
def markerReferenceEnvelope (a b : ℝ) : ℝ :=
  markerReferenceCoefficient * (1 + a) * exp (4 * π * sqrt (a * b))

theorem markerReferenceEnvelope_nonneg (a b : ℝ) (ha : 0 ≤ a) :
    0 ≤ markerReferenceEnvelope a b := by
  unfold markerReferenceEnvelope
  have := markerReferenceCoefficient_pos
  positivity

private theorem one_le_markerReference_factor (a b : ℝ) (ha : 0 ≤ a) :
    1 ≤ (1 + a) * exp (4 * π * sqrt (a * b)) := by
  have he : 1 ≤ exp (4 * π * sqrt (a * b)) := one_le_exp (by positivity)
  nlinarith [mul_nonneg ha (exp_pos (4 * π * sqrt (a * b))).le]

theorem markerReferenceEnergyBound_le_envelope (a b : ℝ) (ha : 0 ≤ a) :
    markerReferenceEnergyBound a b ≤ markerReferenceEnvelope a b := by
  have hC := centralKernelBound_pos.le
  have hK := correctedKernelBound_pos.le
  have hc : 2 * centralKernelBound ≤
      2 * centralKernelBound * ((1 + a) * exp (4 * π * sqrt (a * b))) :=
    le_mul_of_one_le_right (by positivity) (one_le_markerReference_factor a b ha)
  have hp : 64 * π ^ 2 * a * exp (4 * π * sqrt (a * b)) ≤
      64 * π ^ 2 * (1 + a) * exp (4 * π * sqrt (a * b)) := by
    gcongr
    linarith
  calc
    _ ≤ 2 * centralKernelBound * ((1 + a) * exp (4 * π * sqrt (a * b))) +
        64 * π ^ 2 * (1 + a) * exp (4 * π * sqrt (a * b)) := add_le_add hc hp
    _ = (2 * centralKernelBound + 64 * π ^ 2) * (1 + a) *
        exp (4 * π * sqrt (a * b)) := by ring
    _ ≤ markerReferenceEnvelope a b := by
      unfold markerReferenceEnvelope markerReferenceCoefficient
      apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
      exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hK) (by positivity)

theorem correctedKernelBound_le_markerReferenceEnvelope (a b : ℝ) (ha : 0 ≤ a) :
    correctedKernelBound ≤ markerReferenceEnvelope a b := by
  have hc : correctedKernelBound ≤ markerReferenceCoefficient := by
    unfold markerReferenceCoefficient
    have := centralKernelBound_pos
    nlinarith [sq_nonneg π]
  calc
    _ ≤ markerReferenceCoefficient := hc
    _ ≤ markerReferenceCoefficient * ((1 + a) * exp (4 * π * sqrt (a * b))) :=
      le_mul_of_one_le_right markerReferenceCoefficient_pos.le
        (one_le_markerReference_factor a b ha)
    _ = markerReferenceEnvelope a b := by unfold markerReferenceEnvelope; ring

/-- A single global constant gives the C5 pointwise bound while retaining the
endpoint zeros needed for both ordinary and Hilbert integration. -/
theorem norm_markerReferenceRhs_le_envelope (a b e : ℝ) (j : ℤ)
    (ha : 2 ≤ a) (hb : 0 ≤ b) (he : |(j : ℝ)| ≤ e) (heb : e ≤ b) :
    ‖markerReferenceRhs a b j e‖ ≤
      markerReferenceEnvelope a b * (e + sqrt b * sqrt e) := by
  have ha0 : 0 ≤ a := by linarith
  have he0 : 0 ≤ e := (abs_nonneg _).trans he
  calc
    _ ≤ markerReferenceEnergyBound a b * e +
        (correctedKernelBound * sqrt b) * sqrt e :=
      norm_markerReferenceRhs_le a b e j ha hb he heb
    _ ≤ markerReferenceEnvelope a b * e +
        (markerReferenceEnvelope a b * sqrt b) * sqrt e := by
      gcongr
      · exact markerReferenceEnergyBound_le_envelope a b ha0
      · exact correctedKernelBound_le_markerReferenceEnvelope a b ha0
    _ = _ := by ring

/-- One global constant supplies the parameter-uniform C5 estimate. -/
theorem exists_markerReferenceRhs_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (a b e : ℝ) (j : ℤ),
      2 ≤ a → 1 ≤ b → |(j : ℝ)| ≤ e → e ≤ b →
      ‖markerReferenceRhs a b j e‖ ≤
        C * (1 + a) * exp (4 * π * sqrt (a * b)) * (e + sqrt b * sqrt e) :=
  ⟨markerReferenceCoefficient, markerReferenceCoefficient_pos,
    fun a b e j ha hb he heb => norm_markerReferenceRhs_le_envelope a b e j ha
      (zero_le_one.trans hb) he heb⟩

/-- Each actual Hilbert row is bounded by the ordinary energy moments. -/
theorem norm_markerReferenceRhsRow_le (a b : ℝ) (j : ℤ)
    (ha : 2 ≤ a) (hb : 0 ≤ b) :
    ‖markerReferenceRhsRow a b j ha hb‖ ≤
      (markerReferenceEnergyBound a b + correctedKernelBound) * b := by
  have ha0 : 0 ≤ a := by linarith
  have hD := markerReferenceEnergyBound_nonneg a b ha0
  have hC := correctedKernelBound_pos.le
  calc
    _ ≤ markerReferenceEnergyBound a b * b + (correctedKernelBound * sqrt b) * sqrt b := by
      apply norm_toLp_le_of_energy_sqrt_bound j b hb (markerReferenceRhs a b j)
        (markerReferenceRhs_memLp a b j ha hb) _ _ hD (by positivity)
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with e he
      exact norm_markerReferenceRhs_le a b e j ha hb he.1.le he.2.le
    _ = _ := by rw [mul_assoc correctedKernelBound, mul_self_sqrt hb]; ring

/-- The complete finite Hilbert source carries only the square root of the row count. -/
theorem norm_markerReferenceRhsHilbert_le {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (a b : ℝ) (ha : 2 ≤ a) (hb : 0 ≤ b) :
    ‖markerReferenceRhsHilbert J a b ha hb‖ ≤ sqrt (Fintype.card ι : ℝ) *
      ((markerReferenceEnergyBound a b + correctedKernelBound) * b) := by
  have hD := markerReferenceEnergyBound_nonneg a b (show 0 ≤ a by linarith)
  have hC := correctedKernelBound_pos.le
  have hK : 0 ≤ (markerReferenceEnergyBound a b + correctedKernelBound) * b := by positivity
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [PiLp.norm_sq_eq_of_L2]
  calc
    _ ≤ ∑ _i : ι, ((markerReferenceEnergyBound a b + correctedKernelBound) * b) ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      exact pow_le_pow_left₀ (norm_nonneg _)
        (norm_markerReferenceRhsRow_le a b (J i) ha hb) 2
    _ = (sqrt (Fintype.card ι : ℝ) *
        ((markerReferenceEnergyBound a b + correctedKernelBound) * b)) ^ 2 := by
      rw [mul_pow (sqrt (Fintype.card ι : ℝ)), sq_sqrt (Nat.cast_nonneg _)]
      simp

private theorem markerReference_integral_energy_le (j : ℤ) (b : ℝ) (hb : 0 ≤ b) :
    (∫ e, e ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| b)) ≤ b := by
  by_cases hj : |(j : ℝ)| ≤ b
  · rw [lowBand_integral_energy j hj]
    exact (sqrt_le_left hb).mpr (by nlinarith [sq_nonneg (j : ℝ)])
  · simp [Ioo_eq_empty_of_le (le_of_not_ge hj), hb]

/-- The same source has a quantitative ordinary `L¹` bound on its literal density. -/
theorem integral_norm_markerReferenceRhs_le (a b : ℝ) (j : ℤ)
    (ha : 2 ≤ a) (hb : 0 ≤ b) :
    (∫ e, ‖markerReferenceRhs a b j e‖
      ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| b)) ≤
      markerReferenceEnergyBound a b * b +
        (correctedKernelBound * sqrt b) * (b + 2 * sqrt b) := by
  have hD := markerReferenceEnergyBound_nonneg a b (show 0 ≤ a by linarith)
  have hC := correctedKernelBound_pos.le
  have henergy := (lowBand_energy_integrable j b).const_mul (markerReferenceEnergyBound a b)
  have hsqrt := (lowBand_sqrt_energy_integrable j b).const_mul (correctedKernelBound * sqrt b)
  calc
    _ ≤ ∫ e, markerReferenceEnergyBound a b * e +
        (correctedKernelBound * sqrt b) * sqrt e
          ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| b) := by
      apply integral_mono_ae (markerReferenceRhs_integrable a b j ha hb).norm
        (henergy.add hsqrt)
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with e he
      exact norm_markerReferenceRhs_le a b e j ha hb he.1.le he.2.le
    _ = markerReferenceEnergyBound a b *
        (∫ e, e ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| b)) +
        (correctedKernelBound * sqrt b) *
          (∫ e, sqrt e ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| b)) := by
      rw [integral_add henergy hsqrt, integral_const_mul, integral_const_mul]
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left (markerReference_integral_energy_le j b hb) hD)
      (mul_le_mul_of_nonneg_left (lowBand_integral_sqrt_energy_le j b hb) (by positivity))

theorem norm_markerReferenceRhsL1Row_le (a b : ℝ) (j : ℤ)
    (ha : 2 ≤ a) (hb : 0 ≤ b) :
    ‖markerReferenceRhsL1Row a b j ha hb‖ ≤
      markerReferenceEnergyBound a b * b +
        (correctedKernelBound * sqrt b) * (b + 2 * sqrt b) := by
  rw [L1.norm_eq_integral_norm]
  calc
    _ = ∫ e, ‖markerReferenceRhs a b j e‖
        ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| b) := by
      apply integral_congr_ae
      exact (markerReferenceRhsL1Row_coeFn a b j ha hb).fun_comp (fun z : ℂ => ‖z‖)
    _ ≤ _ := integral_norm_markerReferenceRhs_le a b j ha hb

/-- Ordinary finite-row mass grows at most linearly in the number of rows. -/
theorem norm_markerReferenceRhsL1_le {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (a b : ℝ) (ha : 2 ≤ a) (hb : 0 ≤ b) :
    ‖markerReferenceRhsL1 J a b ha hb‖ ≤ (Fintype.card ι : ℝ) *
      (markerReferenceEnergyBound a b * b +
        (correctedKernelBound * sqrt b) * (b + 2 * sqrt b)) := by
  rw [PiLp.norm_eq_of_L1]
  calc
    _ ≤ ∑ _i : ι, (markerReferenceEnergyBound a b * b +
        (correctedKernelBound * sqrt b) * (b + 2 * sqrt b)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact norm_markerReferenceRhsL1Row_le a b (J i) ha hb
    _ = _ := by simp [mul_add]

end GapFamily.Construction
