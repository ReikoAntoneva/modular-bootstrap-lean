import GapFamily.Analytic.Kernel.FullKernelOperator
import GapFamily.Analytic.Kernel.LowBandConjugation
import GapFamily.Analytic.Kernel.KernelFormConjugation
import GapFamily.Analytic.Foundation.InverseConjugation

/-! The actual corrected low-band operator and its invertible identity-plus
operator respect the real subspace of the physical Hilbert band. -/
noncomputable section
namespace GapFamily.Analytic
open MeasureTheory
open scoped ComplexConjugate

variable {ι : Type*} [Fintype ι]

/-- A physical Hilbert input is real when it is fixed by conjugation. -/
def LowBandIsReal (J : ι → ℤ) (B : ℝ) (f : LowBandHilbert J B) : Prop :=
  lowBandConj J B f = f

/-- Reality of a Hilbert input means reality of its representative in every
physical row, almost everywhere for the actual restricted reference measure. -/
theorem lowBandIsReal_iff_ae (J : ι → ℤ) (B : ℝ) (f : LowBandHilbert J B) :
    LowBandIsReal J B f ↔ ∀ i,
      ∀ᵐ E ∂(referenceMeasure (J i)).restrict (Set.Ioo |(J i : ℝ)| B),
        conj (f i E) = f i E := by
  constructor
  · intro hf i
    have hr : star (f i) = f i := by
      simpa only [lowBandConj_apply] using congrArg (fun g : LowBandHilbert J B => g i) hf
    have ha := Lp.coeFn_star (f i)
    rw [hr] at ha
    exact ha.symm
  · intro hf
    apply PiLp.ext
    intro i
    change star (f i) = f i
    exact Lp.ext ((Lp.coeFn_star (f i)).trans (hf i))

/-- Equivalent representative-level reality in terms of the imaginary part. -/
theorem lowBandIsReal_iff_im_zero_ae (J : ι → ℤ) (B : ℝ) (f : LowBandHilbert J B) :
    LowBandIsReal J B f ↔ ∀ i,
      ∀ᵐ E ∂(referenceMeasure (J i)).restrict (Set.Ioo |(J i : ℝ)| B),
        (f i E).im = 0 := by
  simp only [lowBandIsReal_iff_ae, Complex.conj_eq_iff_im]

/-- Reality of the actual kernel makes its Riesz integral operator commute
with conjugation on the physical Hilbert band. -/
theorem lowBandConj_correctedLowBandOperator (J : ι → ℤ) (B : ℝ)
    (f : LowBandHilbert J B) :
    lowBandConj J B (correctedLowBandOperator J B f) =
      correctedLowBandOperator J B (lowBandConj J B f) := by
  apply ext_inner_left ℂ
  intro g
  rw [inner_lowBandConj_right]
  simp only [inner_correctedLowBandOperator, map_sum, lowBandConj_apply]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro l hl
  have hp := lowBandKernelPairing_conj_left (J i) (J l) B
    (fun p => correctedKernel (J i) (J l) p.1 p.2)
    (fun p => conj_correctedKernel (J i) (J l) p.1 p.2) (g i) (f l)
  simpa only [starRingEnd_self_apply] using congrArg conj hp

/-- Conjugation also commutes with the actual identity-plus correction. -/
theorem lowBandConj_correctedLowBandIdentityPlus (J : ι → ℤ) (B : ℝ)
    (f : LowBandHilbert J B) :
    lowBandConj J B (correctedLowBandIdentityPlus J B f) =
      correctedLowBandIdentityPlus J B (lowBandConj J B f) := by
  rw [correctedLowBandIdentityPlus_apply, lowBandConj_add,
    lowBandConj_correctedLowBandOperator, correctedLowBandIdentityPlus_apply]

/-- The actual inverse commutes with conjugation whenever the actual operator
is invertible. Positivity is not needed for this compatibility statement. -/
theorem lowBandConj_correctedLowBandInverse (J : ι → ℤ) (B : ℝ)
    (hunit : IsUnit (correctedLowBandIdentityPlus J B)) (f : LowBandHilbert J B) :
    lowBandConj J B (Ring.inverse (correctedLowBandIdentityPlus J B) f) =
      Ring.inverse (correctedLowBandIdentityPlus J B) (lowBandConj J B f) :=
  InverseConjugation.commutes_inverse_of_isUnit (correctedLowBandIdentityPlus J B)
    (lowBandConj J B) (lowBandConj_correctedLowBandIdentityPlus J B) hunit f

/-- Real Hilbert inputs have real actual corrected responses. -/
theorem LowBandIsReal.correctedLowBandOperator (J : ι → ℤ) (B : ℝ)
    {f : LowBandHilbert J B} (hf : LowBandIsReal J B f) :
    LowBandIsReal J B (correctedLowBandOperator J B f) := by
  unfold LowBandIsReal at *
  rw [lowBandConj_correctedLowBandOperator, hf]

/-- The identity-plus operator preserves the real physical Hilbert subspace. -/
theorem LowBandIsReal.correctedLowBandIdentityPlus (J : ι → ℤ) (B : ℝ)
    {f : LowBandHilbert J B} (hf : LowBandIsReal J B f) :
    LowBandIsReal J B (correctedLowBandIdentityPlus J B f) := by
  unfold LowBandIsReal at *
  rw [lowBandConj_correctedLowBandIdentityPlus, hf]

/-- Inverting the actual identity-plus operator preserves real data. -/
theorem LowBandIsReal.correctedLowBandInverse (J : ι → ℤ) (B : ℝ)
    (hunit : IsUnit (GapFamily.Analytic.correctedLowBandIdentityPlus J B))
    {f : LowBandHilbert J B} (hf : LowBandIsReal J B f) :
    LowBandIsReal J B (Ring.inverse (GapFamily.Analytic.correctedLowBandIdentityPlus J B) f) := by
  unfold LowBandIsReal at *
  rw [lowBandConj_correctedLowBandInverse J B hunit, hf]

/-- Representative-level formulation: almost-everywhere real input gives
almost-everywhere real inverse output in every physical row. -/
theorem correctedLowBandInverse_real_ae (J : ι → ℤ) (B : ℝ)
    (hunit : IsUnit (correctedLowBandIdentityPlus J B))
    (f : LowBandHilbert J B)
    (hf : ∀ i, ∀ᵐ E ∂(referenceMeasure (J i)).restrict (Set.Ioo |(J i : ℝ)| B),
      conj (f i E) = f i E) :
    ∀ i, ∀ᵐ E ∂(referenceMeasure (J i)).restrict (Set.Ioo |(J i : ℝ)| B),
      conj ((Ring.inverse (correctedLowBandIdentityPlus J B) f) i E) =
        (Ring.inverse (correctedLowBandIdentityPlus J B) f) i E :=
  (lowBandIsReal_iff_ae J B _).mp
    (LowBandIsReal.correctedLowBandInverse J B hunit ((lowBandIsReal_iff_ae J B f).mpr hf))

end GapFamily.Analytic
