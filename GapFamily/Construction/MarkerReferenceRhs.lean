import GapFamily.Analytic.Foundation.FullVacuumIntegrability
import GapFamily.Analytic.Foundation.FullVacuumReality
import GapFamily.Analytic.Kernel.FullKernelScalarColumnL1

/-!
# The actual marker reference source

The negative sum of the full vacuum and scalar marker response is an ordinary
integrable density on each physical low band. Its Hilbert and ordinary mass
representations have the same actual real function as representative.
-/

noncomputable section

open MeasureTheory Set
open scoped ComplexConjugate

namespace GapFamily.Construction

open Analytic

/-- The actual low-band source whose inverse cancels the vacuum and marker response. -/
def markerReferenceRhs (a b : ℝ) (j : ℤ) (e : ℝ) : ℂ :=
  -(vacuumFullKernel a e j + correctedKernel j 0 e b)

@[simp] theorem conj_markerReferenceRhs (a b : ℝ) (j : ℤ) (e : ℝ) :
    conj (markerReferenceRhs a b j e) = markerReferenceRhs a b j e := by
  simp [markerReferenceRhs]

@[simp] theorem markerReferenceRhs_im (a b : ℝ) (j : ℤ) (e : ℝ) :
    (markerReferenceRhs a b j e).im = 0 :=
  Complex.conj_eq_iff_im.mp (conj_markerReferenceRhs a b j e)

@[simp] theorem markerReferenceRhs_ofReal_re (a b : ℝ) (j : ℤ) (e : ℝ) :
    ((markerReferenceRhs a b j e).re : ℂ) = markerReferenceRhs a b j e := by
  apply Complex.ext
  · rfl
  · simp

private theorem scalarColumn_at_one (j : ℤ) (b : ℝ) (hb : 0 ≤ b) :
    (fun e : ℝ => correctedKernelHolInput j 0 b e (1 : ℂ)) =
      (fun e : ℝ => correctedKernel j 0 e b) := by
  funext e
  simpa only [Complex.ofReal_one, Int.cast_zero, abs_zero, one_pow, mul_one, zero_add] using
    correctedKernelHolInput_ofReal j 0 b e 1 hb zero_le_one

/-- Ordinary absolute integrability includes the infinite-mass scalar reference row. -/
theorem markerReferenceRhs_integrable (a b : ℝ) (j : ℤ) (ha : 2 ≤ a) (hb : 0 ≤ b) :
    Integrable (markerReferenceRhs a b j)
      ((referenceMeasure j).restrict (Ioo |(j : ℝ)| b)) := by
  have hc := correctedKernelHolInput_scalar_integrable j b hb (1 : ℂ)
  rw [scalarColumn_at_one j b hb] at hc
  exact ((vacuumFullKernel_lowBand_integrable a b j ha).add hc).neg

/-- The same actual source has genuine Hilbert membership. -/
theorem markerReferenceRhs_memLp (a b : ℝ) (j : ℤ) (ha : 2 ≤ a) (hb : 0 ≤ b) :
    MemLp (markerReferenceRhs a b j) 2
      ((referenceMeasure j).restrict (Ioo |(j : ℝ)| b)) := by
  have hc := correctedKernelHolInput_scalar_memLp j b hb (1 : ℂ)
  rw [scalarColumn_at_one j b hb] at hc
  exact ((vacuumFullKernel_lowBand_memLp a b j ha).add hc).neg

/-- One actual Hilbert row of the marker reference source. -/
def markerReferenceRhsRow (a b : ℝ) (j : ℤ) (ha : 2 ≤ a) (hb : 0 ≤ b) : LowBandRow j b :=
  (markerReferenceRhs_memLp a b j ha hb).toLp (markerReferenceRhs a b j)

theorem markerReferenceRhsRow_coeFn (a b : ℝ) (j : ℤ) (ha : 2 ≤ a) (hb : 0 ≤ b) :
    (markerReferenceRhsRow a b j ha hb : ℝ → ℂ) =ᵐ[
      (referenceMeasure j).restrict (Ioo |(j : ℝ)| b)] markerReferenceRhs a b j :=
  (markerReferenceRhs_memLp a b j ha hb).coeFn_toLp

/-- The finite Hilbert vector consists of the actual vacuum-plus-marker rows. -/
def markerReferenceRhsHilbert {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (a b : ℝ) (ha : 2 ≤ a) (hb : 0 ≤ b) : LowBandHilbert J b :=
  WithLp.toLp 2 (fun i => markerReferenceRhsRow a b (J i) ha hb)

@[simp] theorem markerReferenceRhsHilbert_apply {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (a b : ℝ) (ha : 2 ≤ a) (hb : 0 ≤ b) (i : ι) :
    markerReferenceRhsHilbert J a b ha hb i = markerReferenceRhsRow a b (J i) ha hb := rfl

theorem markerReferenceRhsHilbert_coeFn {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (a b : ℝ) (ha : 2 ≤ a) (hb : 0 ≤ b) (i : ι) :
    (markerReferenceRhsHilbert J a b ha hb i : ℝ → ℂ) =ᵐ[
      (referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| b)] markerReferenceRhs a b (J i) :=
  markerReferenceRhsRow_coeFn a b (J i) ha hb

/-- The Hilbert representative remains ordinarily integrable, by its actual source identity. -/
theorem markerReferenceRhsHilbert_integrable {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (a b : ℝ) (ha : 2 ≤ a) (hb : 0 ≤ b) (i : ι) :
    Integrable (markerReferenceRhsHilbert J a b ha hb i)
      ((referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| b)) :=
  (markerReferenceRhs_integrable a b (J i) ha hb).congr
    (markerReferenceRhsHilbert_coeFn J a b ha hb i).symm

/-- The actual source lies in the real subspace of the physical Hilbert band. -/
theorem markerReferenceRhsHilbert_real {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (a b : ℝ) (ha : 2 ≤ a) (hb : 0 ≤ b) :
    LowBandIsReal J b (markerReferenceRhsHilbert J a b ha hb) := by
  rw [lowBandIsReal_iff_ae]
  intro i
  filter_upwards [markerReferenceRhsHilbert_coeFn J a b ha hb i] with e he
  rw [he, conj_markerReferenceRhs]

/-- One ordinary integrable row of the same marker reference source. -/
def markerReferenceRhsL1Row (a b : ℝ) (j : ℤ) (ha : 2 ≤ a) (hb : 0 ≤ b) :
    CorrectedKernelSmoothingRow j b :=
  (markerReferenceRhs_integrable a b j ha hb).toL1 (markerReferenceRhs a b j)

theorem markerReferenceRhsL1Row_coeFn (a b : ℝ) (j : ℤ) (ha : 2 ≤ a) (hb : 0 ≤ b) :
    (markerReferenceRhsL1Row a b j ha hb : ℝ → ℂ) =ᵐ[
      (referenceMeasure j).restrict (Ioo |(j : ℝ)| b)] markerReferenceRhs a b j :=
  (markerReferenceRhs_integrable a b j ha hb).coeFn_toL1

/-- The same source as an ordinary L1 numerator family. -/
def markerReferenceRhsL1 {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (a b : ℝ) (ha : 2 ≤ a) (hb : 0 ≤ b) : CorrectedKernelSmoothingSpace J b :=
  WithLp.toLp 1 (fun i => markerReferenceRhsL1Row a b (J i) ha hb)

@[simp] theorem markerReferenceRhsL1_apply {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (a b : ℝ) (ha : 2 ≤ a) (hb : 0 ≤ b) (i : ι) :
    markerReferenceRhsL1 J a b ha hb i = markerReferenceRhsL1Row a b (J i) ha hb := rfl

theorem markerReferenceRhsL1_coeFn {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (a b : ℝ) (ha : 2 ≤ a) (hb : 0 ≤ b) (i : ι) :
    (markerReferenceRhsL1 J a b ha hb i : ℝ → ℂ) =ᵐ[
      (referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| b)] markerReferenceRhs a b (J i) :=
  markerReferenceRhsL1Row_coeFn a b (J i) ha hb

/-- Hilbert and ordinary mass representations have identical physical representatives. -/
theorem markerReferenceRhsL1_ae {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (a b : ℝ) (ha : 2 ≤ a) (hb : 0 ≤ b) (i : ι) :
    (markerReferenceRhsL1 J a b ha hb i : ℝ → ℂ) =ᵐ[
      (referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| b)]
        (markerReferenceRhsHilbert J a b ha hb i : ℝ → ℂ) :=
  (markerReferenceRhsL1_coeFn J a b ha hb i).trans
    (markerReferenceRhsHilbert_coeFn J a b ha hb i).symm

/-- Reality holds also for the ordinary L1 representative. -/
theorem markerReferenceRhsL1_real_ae {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (a b : ℝ) (ha : 2 ≤ a) (hb : 0 ≤ b) (i : ι) :
    ∀ᵐ e ∂(referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| b),
      conj (markerReferenceRhsL1 J a b ha hb i e) = markerReferenceRhsL1 J a b ha hb i e := by
  filter_upwards [markerReferenceRhsL1_coeFn J a b ha hb i] with e he
  rw [he, conj_markerReferenceRhs]

end GapFamily.Construction
