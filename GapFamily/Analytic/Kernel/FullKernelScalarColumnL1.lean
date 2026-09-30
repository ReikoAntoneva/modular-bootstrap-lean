import GapFamily.Analytic.Kernel.FullKernelScalarColumn
import GapFamily.Analytic.Kernel.FullKernelScalarColumnL1Bound
import GapFamily.Analytic.Kernel.FullKernelScalarColumnL1Exponent
import GapFamily.Analytic.Foundation.L1DominatedAnalytic

/-! The scalar input column in the ordinary L1 sum of physical rows.
Its analytic realization has the same representatives as the Hilbert column,
so the actual threshold mass is a continuous functional of this column. -/
noncomputable section
namespace GapFamily.Analytic
open MeasureTheory Set Metric Real
open scoped ComplexConjugate

/-- One ordinary integrable physical row of the scalar input column. -/
def correctedScalarColumnL1Row (j : ℤ) (B : ℝ) (hB : 0 ≤ B) (z : ℂ) :
    CorrectedKernelSmoothingRow j B :=
  (correctedKernelHolInput_scalar_memLp_one j B hB z).toLp
    (fun e => correctedKernelHolInput j 0 B e z)

theorem correctedScalarColumnL1Row_coeFn (j : ℤ) (B : ℝ) (hB : 0 ≤ B) (z : ℂ) :
    (correctedScalarColumnL1Row j B hB z : ℝ → ℂ) =ᵐ[
      (referenceMeasure j).restrict (Ioo |(j : ℝ)| B)]
        fun e => correctedKernelHolInput j 0 B e z :=
  (correctedKernelHolInput_scalar_memLp_one j B hB z).coeFn_toLp

/-- Local ordinary integrable majorants give norm holomorphy. -/
theorem differentiable_correctedScalarColumnL1Row (j : ℤ) (B : ℝ) (hB : 0 ≤ B) :
    Differentiable ℂ (correctedScalarColumnL1Row j B hB) := by
  apply DominatedAnalytic.differentiable_L1_of_entire_dominated
    (correctedScalarColumnL1Row_coeFn j B hB)
  · exact Filter.Eventually.of_forall fun e => differentiable_correctedKernelHolInput j 0 B e
  · intro z₀
    refine ⟨scalarColumnMajorant B (‖z₀‖ + 2),
      scalarColumnMajorant_memLp_one j B hB (‖z₀‖ + 2), ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with e he
    intro z hz
    apply norm_correctedKernelHolInput_scalar_le j B (‖z₀‖ + 2) e z hB (by positivity)
      he.1.le he.2.le
    exact norm_le_norm_add_const_of_dist_le (mem_closedBall.mp hz)

/-- The complete scalar column as an ordinary L1 numerator family. -/
def correctedScalarColumnL1 {ι : Type*} [Fintype ι] (J : ι → ℤ) (B : ℝ)
    (hB : 0 ≤ B) (z : ℂ) : CorrectedKernelSmoothingSpace J B :=
  WithLp.toLp 1 (fun i => correctedScalarColumnL1Row (J i) B hB z)

@[simp] theorem correctedScalarColumnL1_apply {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (z : ℂ) (i : ι) :
    correctedScalarColumnL1 J B hB z i = correctedScalarColumnL1Row (J i) B hB z := rfl

theorem differentiable_correctedScalarColumnL1 {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) :
    Differentiable ℂ (correctedScalarColumnL1 J B hB) :=
  (differentiable_piLp _).mpr fun i => differentiable_correctedScalarColumnL1Row (J i) B hB

/-- The L1 and Hilbert constructions represent the identical physical kernel. -/
theorem correctedScalarColumnL1_ae {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (z : ℂ) (i : ι) :
    (correctedScalarColumnL1 J B hB z i : ℝ → ℂ) =ᵐ[
      (referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B)]
        (correctedScalarColumn J B hB z i : ℝ → ℂ) :=
  (correctedScalarColumnL1Row_coeFn (J i) B hB z).trans
    (correctedScalarColumnRow_coeFn (J i) B hB z).symm

/-- Exact agreement with the physical scalar-input column on positive energies. -/
theorem correctedScalarColumnL1_coeFn_ofReal {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (t : ℝ) (ht : 0 ≤ t) (i : ι) :
    (correctedScalarColumnL1 J B hB t i : ℝ → ℂ) =ᵐ[
      (referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B)]
        fun e => correctedKernel (J i) 0 e (B * t ^ 2) :=
  (correctedScalarColumnL1_ae J B hB t i).trans
    (correctedScalarColumn_coeFn_ofReal J B hB t ht i)

@[simp] theorem correctedScalarColumnL1Row_zero (j : ℤ) (B : ℝ) (hB : 0 ≤ B) :
    correctedScalarColumnL1Row j B hB 0 = 0 := by
  apply Lp.ext
  filter_upwards [correctedScalarColumnL1Row_coeFn j B hB 0,
    Lp.coeFn_zero (E := ℂ) (p := 1)
      (μ := (referenceMeasure j).restrict (Ioo |(j : ℝ)| B))] with e he hz
  rw [he, correctedKernelHolInput_scalar_zero, hz]
  rfl

@[simp] theorem correctedScalarColumnL1_zero {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) : correctedScalarColumnL1 J B hB 0 = 0 := by
  apply PiLp.ext
  intro i
  exact correctedScalarColumnL1Row_zero (J i) B hB

/-- Real-axis column representatives are real in the ordinary mass space. -/
theorem correctedScalarColumnL1_real_ae {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (t : ℝ) (i : ι) :
    ∀ᵐ e ∂(referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B),
      conj (correctedScalarColumnL1 J B hB t i e) =
        correctedScalarColumnL1 J B hB t i e := by
  filter_upwards [correctedScalarColumnL1_ae J B hB t i,
    (lowBandIsReal_iff_ae J B _).mp (correctedScalarColumn_real J B hB t) i] with e he hreal
  simpa only [he] using hreal

/-- Direct ordinary-mass control on one fixed square-root disk. -/
theorem norm_correctedScalarColumnL1_le {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (R : ℝ) (hR : 0 ≤ R)
    (z : ℂ) (hz : ‖z‖ ≤ R) :
    ‖correctedScalarColumnL1 J B hB z‖ ≤ (Fintype.card ι : ℝ) *
      (higherKernelCompactBound 0 B (B * R ^ 2) * B +
        12 * sqrt B * R * (B + 2 * sqrt B)) := by
  rw [PiLp.norm_eq_of_L1]
  calc
    _ ≤ ∑ _i : ι, (higherKernelCompactBound 0 B (B * R ^ 2) * B +
        12 * sqrt B * R * (B + 2 * sqrt B)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact norm_correctedKernelHolInput_scalar_toL1_le (J i) B R hB hR z hz
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- Uniform ordinary mass bound with one exponent for each fixed disk. -/
theorem norm_correctedScalarColumnL1_le_exp {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (hJ : Function.Injective J) (B : ℝ) (hB : 1 ≤ B)
    (hband : ∀ i, |(J i : ℝ)| < B) (R : ℝ) (hR : 0 ≤ R)
    (z : ℂ) (hz : ‖z‖ ≤ R) :
    ‖correctedScalarColumnL1 J B (by linarith) z‖ ≤
      exp (scalarColumnL1DiskCardExponent R * B) := by
  calc
    _ ≤ (Fintype.card ι : ℝ) * scalarColumnL1DiskBound B R :=
      norm_correctedScalarColumnL1_le J B (by linarith) R hR z hz
    _ ≤ (5 * B) * scalarColumnL1DiskBound B R :=
      mul_le_mul_of_nonneg_right (physicalLowBand_card_le J hJ hB hband)
        (scalarColumnL1DiskBound_nonneg B R (by linarith) hR)
    _ ≤ _ := scalarColumnL1DiskBound_mul_five_band_le_exp B R hB hR

end GapFamily.Analytic
