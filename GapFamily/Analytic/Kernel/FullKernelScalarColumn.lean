import GapFamily.Analytic.Kernel.FullKernelScalarColumnBound
import GapFamily.Analytic.Kernel.FullKernelResponseBound
import GapFamily.Analytic.Kernel.FullKernelCoercivity
import GapFamily.Analytic.Kernel.FullKernelConjugation
import GapFamily.Analytic.Foundation.L2DominatedAnalytic
import Mathlib.Analysis.Calculus.FDeriv.WithLp

/-! The actual scalar input column as an entire physical Hilbert vector.
Its inverse column uses the existing bounded inverse of the same low-band
operator, with no abstract replacement of the physical kernel. -/
noncomputable section
namespace GapFamily.Analytic
open MeasureTheory Set Metric Real
open scoped ComplexConjugate

/-- One actual physical row of the holomorphic scalar input column. -/
def correctedScalarColumnRow (j : ℤ) (B : ℝ) (hB : 0 ≤ B) (z : ℂ) : LowBandRow j B :=
  (correctedKernelHolInput_scalar_memLp j B hB z).toLp
    (fun e => correctedKernelHolInput j 0 B e z)

theorem correctedScalarColumnRow_coeFn (j : ℤ) (B : ℝ) (hB : 0 ≤ B) (z : ℂ) :
    (correctedScalarColumnRow j B hB z : ℝ → ℂ) =ᵐ[
      (referenceMeasure j).restrict (Ioo |(j : ℝ)| B)]
        fun e => correctedKernelHolInput j 0 B e z :=
  (correctedKernelHolInput_scalar_memLp j B hB z).coeFn_toLp

/-- The scalar input column is an entire L2 vector, including at zero. -/
theorem differentiable_correctedScalarColumnRow (j : ℤ) (B : ℝ) (hB : 0 ≤ B) :
    Differentiable ℂ (correctedScalarColumnRow j B hB) := by
  apply DominatedAnalytic.differentiable_L2_of_entire_dominated
    (correctedScalarColumnRow_coeFn j B hB)
  · exact Filter.Eventually.of_forall fun e => differentiable_correctedKernelHolInput j 0 B e
  · intro z₀
    refine ⟨scalarColumnMajorant B (‖z₀‖ + 2),
      scalarColumnMajorant_memLp j B hB (‖z₀‖ + 2), ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with e he
    intro z hz
    apply norm_correctedKernelHolInput_scalar_le j B (‖z₀‖ + 2) e z hB (by positivity)
      he.1.le he.2.le
    exact norm_le_norm_add_const_of_dist_le (mem_closedBall.mp hz)

/-- The complete finite physical column `r_B^hol(z)`. -/
def correctedScalarColumn {ι : Type*} [Fintype ι] (J : ι → ℤ) (B : ℝ)
    (hB : 0 ≤ B) (z : ℂ) : LowBandHilbert J B :=
  WithLp.toLp 2 (fun i => correctedScalarColumnRow (J i) B hB z)

@[simp] theorem correctedScalarColumn_apply {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (z : ℂ) (i : ι) :
    correctedScalarColumn J B hB z i = correctedScalarColumnRow (J i) B hB z := rfl

/-- The actual input column is entire in the square-root coordinate in the
full Hilbert norm, not only after testing its scalar coordinates. -/
theorem differentiable_correctedScalarColumn {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) :
    Differentiable ℂ (correctedScalarColumn J B hB) :=
  (differentiable_piLp _).mpr fun i => differentiable_correctedScalarColumnRow (J i) B hB

private theorem piLp_norm_le_sum_norm {ι : Type*} [Fintype ι] {V : ι → Type*}
    [∀ i, SeminormedAddCommGroup (V i)] (f : PiLp 2 V) : ‖f‖ ≤ ∑ i, ‖f i‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2]
  exact Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => norm_nonneg _)

/-- Explicit compact-disk control of the column's Hilbert norm. -/
theorem norm_correctedScalarColumn_le {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (R : ℝ) (hR : 0 ≤ R)
    (z : ℂ) (hz : ‖z‖ ≤ R) :
    ‖correctedScalarColumn J B hB z‖ ≤
      (Fintype.card ι : ℝ) * (higherKernelCompactBound 0 B (B * R ^ 2) * B + 12 * B * R) := by
  calc
    _ ≤ ∑ i, ‖correctedScalarColumnRow (J i) B hB z‖ := piLp_norm_le_sum_norm _
    _ ≤ ∑ _i : ι, (higherKernelCompactBound 0 B (B * R ^ 2) * B + 12 * B * R) := by
      apply Finset.sum_le_sum
      intro i hi
      exact norm_correctedKernelHolInput_scalar_toLp_le (J i) B R hB hR z hz
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The scalar column has one fixed-disk exponential bound, uniform in the
physical band and its injective finite spin family. -/
theorem norm_correctedScalarColumn_le_exp {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (hJ : Function.Injective J) (B : ℝ) (hB : 1 ≤ B)
    (hband : ∀ i, |(J i : ℝ)| < B) (R : ℝ) (hR : 0 ≤ R)
    (z : ℂ) (hz : ‖z‖ ≤ R) :
    ‖correctedScalarColumn J B (by linarith) z‖ ≤
      exp (correctedResponseDiskExponent R * B) := by
  have hc := fullKernelScaledCardBound_le_exp J hJ B R hB hR hband 0
    (by simpa using (show 0 ≤ B by linarith))
  simp only [Int.cast_zero, abs_zero, zero_add, fullKernelCompactBound, mul_zero] at hc
  exact (norm_correctedScalarColumn_le J B (by linarith) R hR z hz).trans hc

/-- On nonnegative real square-root coordinates this is exactly the physical
corrected scalar-input column at energy `B t²`. -/
theorem correctedScalarColumn_coeFn_ofReal {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (t : ℝ) (ht : 0 ≤ t) (i : ι) :
    (correctedScalarColumn J B hB t i : ℝ → ℂ) =ᵐ[
      (referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B)]
        fun e => correctedKernel (J i) 0 e (B * t ^ 2) := by
  filter_upwards [correctedScalarColumnRow_coeFn (J i) B hB (t : ℂ)] with e he
  rw [correctedScalarColumn_apply, he, correctedKernelHolInput_ofReal (J i) 0 B e t hB ht]
  simp

/-- The actual inverse column `U_B(z)` in the physical Hilbert band. -/
def correctedScalarInverseColumn {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (z : ℂ) : LowBandHilbert J B :=
  correctedLowBandInverse J B (correctedScalarColumn J B hB z)

/-- Applying the fixed bounded inverse preserves norm holomorphy. -/
theorem differentiable_correctedScalarInverseColumn {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) :
    Differentiable ℂ (correctedScalarInverseColumn J B hB) :=
  (correctedLowBandInverse J B).differentiable.comp
    (differentiable_correctedScalarColumn J B hB)

/-- Quantitative inverse-column control retains the actual inverse norm. -/
theorem norm_correctedScalarInverseColumn_le {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (hJ : Function.Injective J) (B : ℝ) (hB : 1 ≤ B)
    (hband : ∀ i, |(J i : ℝ)| < B) (R : ℝ) (hR : 0 ≤ R)
    (z : ℂ) (hz : ‖z‖ ≤ R) :
    ‖correctedScalarInverseColumn J B (by linarith) z‖ ≤
      ‖correctedLowBandInverse J B‖ * exp (correctedResponseDiskExponent R * B) :=
  ((correctedLowBandInverse J B).le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (norm_correctedScalarColumn_le_exp J hJ B hB hband R hR z hz)
      (norm_nonneg _))

@[simp] theorem correctedScalarColumnRow_zero (j : ℤ) (B : ℝ) (hB : 0 ≤ B) :
    correctedScalarColumnRow j B hB 0 = 0 := by
  apply Lp.ext
  filter_upwards [correctedScalarColumnRow_coeFn j B hB 0,
    Lp.coeFn_zero (E := ℂ) (p := 2)
      (μ := (referenceMeasure j).restrict (Ioo |(j : ℝ)| B))] with e he hz
  rw [he, correctedKernelHolInput_scalar_zero, hz]
  rfl

@[simp] theorem correctedScalarColumn_zero {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) : correctedScalarColumn J B hB 0 = 0 := by
  apply PiLp.ext
  intro i
  exact correctedScalarColumnRow_zero (J i) B hB

@[simp] theorem correctedScalarInverseColumn_zero {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) : correctedScalarInverseColumn J B hB 0 = 0 := by
  simp [correctedScalarInverseColumn]

/-- Schwarz reflection of the scalar input extension. -/
theorem conj_correctedKernelHolInput_scalar (j : ℤ) (B e : ℝ) (z : ℂ) :
    conj (correctedKernelHolInput j 0 B e z) =
      correctedKernelHolInput j 0 B e (conj z) := by
  simp only [correctedKernelHolInput, Int.cast_zero, abs_zero, Complex.ofReal_zero,
    zero_add, map_add, map_mul, map_pow, conj_fullKernelHol, Complex.conj_ofReal]
  split_ifs <;> simp [map_ofNat]

/-- Real square-root coordinates give real physical Hilbert columns. -/
theorem correctedScalarColumn_real {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (t : ℝ) :
    LowBandIsReal J B (correctedScalarColumn J B hB t) := by
  rw [lowBandIsReal_iff_ae]
  intro i
  filter_upwards [correctedScalarColumnRow_coeFn (J i) B hB (t : ℂ)] with e he
  change conj (correctedScalarColumnRow (J i) B hB t e) =
    correctedScalarColumnRow (J i) B hB t e
  rw [he, conj_correctedKernelHolInput_scalar, Complex.conj_ofReal]

/-- The actual inverse scalar column stays real on the real axis. -/
theorem correctedScalarInverseColumn_real {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B)
    (hunit : IsUnit (correctedLowBandIdentityPlus J B)) (t : ℝ) :
    LowBandIsReal J B (correctedScalarInverseColumn J B hB t) :=
  LowBandIsReal.correctedLowBandInverse J B hunit (correctedScalarColumn_real J B hB t)

/-- The scalar inverse column solves the actual low-band equation. -/
theorem correctedLowBandIdentityPlus_scalarInverseColumn_of_positive
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (hJ : Function.Injective J)
    (B : ℝ) (hB : 1 ≤ B) (hband : ∀ i, |(J i : ℝ)| < B)
    (hP : (correctedLowBandIdentityPlus J (4 * B)).IsPositive) (z : ℂ) :
    correctedLowBandIdentityPlus J B (correctedScalarInverseColumn J B (by linarith) z) =
      correctedScalarColumn J B (by linarith) z :=
  correctedLowBandIdentityPlus_inverse_of_positive J hJ B hB hband hP _

end GapFamily.Analytic
