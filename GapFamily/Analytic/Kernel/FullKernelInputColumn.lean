import GapFamily.Analytic.Kernel.FullKernelInputColumnBound
import GapFamily.Analytic.Kernel.FullKernelConjugation
import GapFamily.Analytic.Kernel.FullKernelSmoothingOperator
import GapFamily.Analytic.Foundation.L2DominatedAnalytic
import GapFamily.Analytic.Foundation.L1DominatedAnalytic
import Mathlib.Analysis.Calculus.FDeriv.WithLp

/-! Actual arbitrary-spin input columns in the physical Hilbert and ordinary
L1 spaces. The input scale is one, independently of the output cutoff. -/
noncomputable section
namespace GapFamily.Analytic
open MeasureTheory Set Metric Real
open scoped ComplexConjugate

/-- One physical Hilbert row of the input column at energy `|jin| + z²`. -/
def correctedInputColumnRow (j jin : ℤ) (B : ℝ) (hB : 0 ≤ B) (z : ℂ) : LowBandRow j B :=
  (correctedKernelHolInput_unit_memLp j jin B hB z).toLp
    (fun e => correctedKernelHolInput j jin 1 e z)

theorem correctedInputColumnRow_coeFn (j jin : ℤ) (B : ℝ) (hB : 0 ≤ B) (z : ℂ) :
    (correctedInputColumnRow j jin B hB z : ℝ → ℂ) =ᵐ[
      (referenceMeasure j).restrict (Ioo |(j : ℝ)| B)]
        fun e => correctedKernelHolInput j jin 1 e z :=
  (correctedKernelHolInput_unit_memLp j jin B hB z).coeFn_toLp

/-- The column is entire in every physical row, including the scalar row. -/
theorem differentiable_correctedInputColumnRow (j jin : ℤ) (B : ℝ) (hB : 0 ≤ B) :
    Differentiable ℂ (correctedInputColumnRow j jin B hB) := by
  apply DominatedAnalytic.differentiable_L2_of_entire_dominated
    (correctedInputColumnRow_coeFn j jin B hB)
  · exact Filter.Eventually.of_forall fun e => differentiable_correctedKernelHolInput j jin 1 e
  · intro z₀
    refine ⟨inputColumnMajorant jin B (‖z₀‖ + 2),
      inputColumnMajorant_memLp j jin B hB (‖z₀‖ + 2), ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with e he
    intro z hz
    apply norm_correctedKernelHolInput_unit_le j jin B (‖z₀‖ + 2) e z (by positivity)
      he.1.le he.2.le
    exact norm_le_norm_add_const_of_dist_le (mem_closedBall.mp hz)

/-- The actual input column as a physical Hilbert vector. -/
def correctedInputColumn {ι : Type*} [Fintype ι] (J : ι → ℤ) (B : ℝ)
    (hB : 0 ≤ B) (jin : ℤ) (z : ℂ) : LowBandHilbert J B :=
  WithLp.toLp 2 (fun i => correctedInputColumnRow (J i) jin B hB z)

@[simp] theorem correctedInputColumn_apply {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (jin : ℤ) (z : ℂ) (i : ι) :
    correctedInputColumn J B hB jin z i = correctedInputColumnRow (J i) jin B hB z := rfl

theorem differentiable_correctedInputColumn {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (jin : ℤ) :
    Differentiable ℂ (correctedInputColumn J B hB jin) :=
  (differentiable_piLp _).mpr fun i => differentiable_correctedInputColumnRow (J i) jin B hB

private theorem inputColumn_hilbert_norm_le_sum {ι : Type*} [Fintype ι] {V : ι → Type*}
    [∀ i, SeminormedAddCommGroup (V i)] (f : PiLp 2 V) : ‖f‖ ≤ ∑ i, ‖f i‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2]
  exact Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => norm_nonneg _)

/-- Compact-disk control retaining the full transposed energy coefficient. -/
theorem norm_correctedInputColumn_le {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (jin : ℤ) (R : ℝ) (hR : 0 ≤ R)
    (z : ℂ) (hz : ‖z‖ ≤ R) :
    ‖correctedInputColumn J B hB jin z‖ ≤ (Fintype.card ι : ℝ) *
      (fullKernelCompactBound jin B (|(jin : ℝ)| + R ^ 2) * B + 12 * R * sqrt B) := by
  calc
    _ ≤ ∑ i, ‖correctedInputColumnRow (J i) jin B hB z‖ := inputColumn_hilbert_norm_le_sum _
    _ ≤ ∑ _i : ι, (fullKernelCompactBound jin B (|(jin : ℝ)| + R ^ 2) * B +
        12 * R * sqrt B) := by
      apply Finset.sum_le_sum
      intro i hi
      exact norm_correctedKernelHolInput_unit_toLp_le (J i) jin B R hB hR z hz
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- Physical agreement at each nonnegative real square-root input. -/
theorem correctedInputColumn_coeFn_ofReal {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (jin : ℤ) (t : ℝ) (ht : 0 ≤ t) (i : ι) :
    (correctedInputColumn J B hB jin t i : ℝ → ℂ) =ᵐ[
      (referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B)]
        fun e => correctedKernel (J i) jin e (|(jin : ℝ)| + t ^ 2) := by
  filter_upwards [correctedInputColumnRow_coeFn (J i) jin B hB (t : ℂ)] with e he
  rw [correctedInputColumn_apply, he,
    correctedKernelHolInput_ofReal (J i) jin 1 e t (by norm_num) ht]
  simp only [one_mul]

/-- Schwarz reflection for the actual input square-root extension. -/
theorem conj_correctedKernelHolInput (j jin : ℤ) (b e : ℝ) (z : ℂ) :
    conj (correctedKernelHolInput j jin b e z) =
      correctedKernelHolInput j jin b e (conj z) := by
  simp only [correctedKernelHolInput, map_add, map_mul, map_pow,
    conj_fullKernelHol, Complex.conj_ofReal]
  split_ifs <;> simp [map_ofNat]

/-- Reality holds on the entire real coordinate axis. -/
theorem correctedInputColumn_real {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (jin : ℤ) (t : ℝ) :
    LowBandIsReal J B (correctedInputColumn J B hB jin t) := by
  rw [lowBandIsReal_iff_ae]
  intro i
  filter_upwards [correctedInputColumnRow_coeFn (J i) jin B hB (t : ℂ)] with e he
  change conj (correctedInputColumnRow (J i) jin B hB t e) =
    correctedInputColumnRow (J i) jin B hB t e
  rw [he, conj_correctedKernelHolInput, Complex.conj_ofReal]

/-- One ordinary integrable row of the same actual input column. -/
def correctedInputColumnL1Row (j jin : ℤ) (B : ℝ) (hB : 0 ≤ B) (z : ℂ) :
    CorrectedKernelSmoothingRow j B :=
  (correctedKernelHolInput_unit_memLp_one j jin B hB z).toLp
    (fun e => correctedKernelHolInput j jin 1 e z)

theorem correctedInputColumnL1Row_coeFn (j jin : ℤ) (B : ℝ) (hB : 0 ≤ B) (z : ℂ) :
    (correctedInputColumnL1Row j jin B hB z : ℝ → ℂ) =ᵐ[
      (referenceMeasure j).restrict (Ioo |(j : ℝ)| B)]
        fun e => correctedKernelHolInput j jin 1 e z :=
  (correctedKernelHolInput_unit_memLp_one j jin B hB z).coeFn_toLp

theorem differentiable_correctedInputColumnL1Row (j jin : ℤ) (B : ℝ) (hB : 0 ≤ B) :
    Differentiable ℂ (correctedInputColumnL1Row j jin B hB) := by
  apply DominatedAnalytic.differentiable_L1_of_entire_dominated
    (correctedInputColumnL1Row_coeFn j jin B hB)
  · exact Filter.Eventually.of_forall fun e => differentiable_correctedKernelHolInput j jin 1 e
  · intro z₀
    refine ⟨inputColumnMajorant jin B (‖z₀‖ + 2),
      inputColumnMajorant_memLp_one j jin B hB (‖z₀‖ + 2), ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with e he
    intro z hz
    apply norm_correctedKernelHolInput_unit_le j jin B (‖z₀‖ + 2) e z (by positivity)
      he.1.le he.2.le
    exact norm_le_norm_add_const_of_dist_le (mem_closedBall.mp hz)

/-- The actual input column in the ordinary L1 sum of physical rows. -/
def correctedInputColumnL1 {ι : Type*} [Fintype ι] (J : ι → ℤ) (B : ℝ)
    (hB : 0 ≤ B) (jin : ℤ) (z : ℂ) : CorrectedKernelSmoothingSpace J B :=
  WithLp.toLp 1 (fun i => correctedInputColumnL1Row (J i) jin B hB z)

@[simp] theorem correctedInputColumnL1_apply {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (jin : ℤ) (z : ℂ) (i : ι) :
    correctedInputColumnL1 J B hB jin z i = correctedInputColumnL1Row (J i) jin B hB z := rfl

theorem differentiable_correctedInputColumnL1 {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (jin : ℤ) :
    Differentiable ℂ (correctedInputColumnL1 J B hB jin) :=
  (differentiable_piLp _).mpr fun i => differentiable_correctedInputColumnL1Row (J i) jin B hB

/-- Both constructions use the identical physical kernel representative. -/
theorem correctedInputColumnL1_ae {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (jin : ℤ) (z : ℂ) (i : ι) :
    (correctedInputColumnL1 J B hB jin z i : ℝ → ℂ) =ᵐ[
      (referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B)]
        (correctedInputColumn J B hB jin z i : ℝ → ℂ) :=
  (correctedInputColumnL1Row_coeFn (J i) jin B hB z).trans
    (correctedInputColumnRow_coeFn (J i) jin B hB z).symm

/-- Every Hilbert column representative has genuine ordinary mass. -/
theorem correctedInputColumn_integrable {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (jin : ℤ) (z : ℂ) (i : ι) :
    Integrable (correctedInputColumn J B hB jin z i)
      ((referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B)) :=
  (L1.integrable_coeFn (correctedInputColumnL1 J B hB jin z i)).congr
    (correctedInputColumnL1_ae J B hB jin z i)

theorem correctedInputColumnL1_coeFn_ofReal {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (jin : ℤ) (t : ℝ) (ht : 0 ≤ t) (i : ι) :
    (correctedInputColumnL1 J B hB jin t i : ℝ → ℂ) =ᵐ[
      (referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B)]
        fun e => correctedKernel (J i) jin e (|(jin : ℝ)| + t ^ 2) :=
  (correctedInputColumnL1_ae J B hB jin t i).trans
    (correctedInputColumn_coeFn_ofReal J B hB jin t ht i)

theorem correctedInputColumnL1_real_ae {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (jin : ℤ) (t : ℝ) (i : ι) :
    ∀ᵐ e ∂(referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B),
      conj (correctedInputColumnL1 J B hB jin t i e) =
        correctedInputColumnL1 J B hB jin t i e := by
  filter_upwards [correctedInputColumnL1_ae J B hB jin t i,
    (lowBandIsReal_iff_ae J B _).mp (correctedInputColumn_real J B hB jin t) i] with e he hreal
  simpa only [he] using hreal

/-- The full compact coefficient also controls ordinary mass, with no finite
reference-mass assumption on the scalar row. -/
theorem norm_correctedInputColumnL1_le {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (jin : ℤ) (R : ℝ) (hR : 0 ≤ R)
    (z : ℂ) (hz : ‖z‖ ≤ R) :
    ‖correctedInputColumnL1 J B hB jin z‖ ≤ (Fintype.card ι : ℝ) *
      (fullKernelCompactBound jin B (|(jin : ℝ)| + R ^ 2) * B +
        12 * R * (B + 2 * sqrt B)) := by
  rw [PiLp.norm_eq_of_L1]
  calc
    _ ≤ ∑ _i : ι, (fullKernelCompactBound jin B (|(jin : ℝ)| + R ^ 2) * B +
        12 * R * (B + 2 * sqrt B)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact norm_correctedKernelHolInput_unit_toL1_le (J i) jin B R hB hR z hz
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end GapFamily.Analytic
