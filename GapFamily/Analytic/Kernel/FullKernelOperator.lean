import GapFamily.Analytic.Kernel.FullKernel
import GapFamily.Analytic.Kernel.FullKernelReality
import GapFamily.Analytic.Kernel.LowBandOperator

/-!
# The full corrected low-band operator

This instantiates the integral-form construction with the actual canonical
central coefficient, higher kernel and scalar rank-one correction. All kernel
pairings are ordinary integrable product-measure integrals. Positivity is not
an input to this bounded-operator construction and is not asserted here.
-/

noncomputable section

namespace GapFamily.Analytic

open MeasureTheory Real

/-- A single bound chosen from the proved full-kernel estimate. -/
def correctedKernelBound : ℝ := exists_correctedKernel_physical_bound.choose

theorem correctedKernelBound_pos : 0 < correctedKernelBound :=
  exists_correctedKernel_physical_bound.choose_spec.1

theorem norm_correctedKernel_le (j J : ℤ) (e E : ℝ)
    (he : |(j : ℝ)| ≤ e) (hE : |(J : ℝ)| ≤ E) :
    ‖correctedKernel j J e E‖ ≤
      correctedKernelBound * (|(j : ℝ)| * |(J : ℝ)| + sqrt e * sqrt E) :=
  exists_correctedKernel_physical_bound.choose_spec.2 j J e E he hE

theorem correctedKernel_aestronglyMeasurable (j J : ℤ) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => correctedKernel j J p.1 p.2)
      ((referenceMeasure j).prod (referenceMeasure J)) :=
  (continuous_correctedKernel j J).aestronglyMeasurable

theorem correctedKernel_ae_weak_bound (j J : ℤ) :
    ∀ᵐ p ∂(referenceMeasure j).prod (referenceMeasure J),
      ‖correctedKernel j J p.1 p.2‖ ≤
        correctedKernelBound * (|(j : ℝ)| * |(J : ℝ)| + sqrt p.1 * sqrt p.2) := by
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (referenceMeasure_ae_above_edge j),
    Measure.quasiMeasurePreserving_snd.ae (referenceMeasure_ae_above_edge J)] with p he hE
  exact norm_correctedKernel_le j J p.1 p.2 he.le hE.le

/-- The actual corrected kernel gives an ordinary integrable pairing on every band. -/
theorem correctedKernel_lowBand_integrable (j J : ℤ) (B : ℝ)
    (f : LowBandRow j B) (g : LowBandRow J B) :
    Integrable (weakKernelIntegrand (fun p => correctedKernel j J p.1 p.2) f g)
      (((referenceMeasure j).restrict (Set.Ioo |(j : ℝ)| B)).prod
        ((referenceMeasure J).restrict (Set.Ioo |(J : ℝ)| B))) :=
  lowBandKernel_integrable correctedKernelBound_pos.le
    (correctedKernel_aestronglyMeasurable j J) (correctedKernel_ae_weak_bound j J)
    (Lp.memLp f) (Lp.memLp g)

/-- The full actual `R_B`, acting on a finite Hilbert sum of physical rows. -/
def correctedLowBandOperator {ι : Type*} [Fintype ι] (J : ι → ℤ) (B : ℝ) :
    LowBandHilbert J B →L[ℂ] LowBandHilbert J B :=
  lowBandKernelOperator J B (fun i l p => correctedKernel (J i) (J l) p.1 p.2)
    correctedKernelBound_pos.le
    (fun i l => correctedKernel_aestronglyMeasurable (J i) (J l))
    (fun i l => correctedKernel_ae_weak_bound (J i) (J l))

theorem inner_correctedLowBandOperator {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (f g : LowBandHilbert J B) :
    inner ℂ f (correctedLowBandOperator J B g) =
      ∑ i, ∑ l, lowBandKernelPairing (J i) (J l) B
        (fun p => correctedKernel (J i) (J l) p.1 p.2) (f i) (g l) :=
  inner_lowBandKernelOperator J B _ correctedKernelBound_pos.le _ _ f g

theorem norm_correctedLowBandOperator_le {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) :
    ‖correctedLowBandOperator J B‖ ≤ lowBandOperatorBound J B correctedKernelBound :=
  norm_lowBandKernelOperator_le J B _ correctedKernelBound_pos.le _ _

/-- The actual full operator is self-adjoint; no kernel symmetry is supplied
as a hypothesis. -/
theorem isSelfAdjoint_correctedLowBandOperator {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) : IsSelfAdjoint (correctedLowBandOperator J B) := by
  apply isSelfAdjoint_lowBandKernelOperator
  intro i l
  exact Filter.Eventually.of_forall fun p =>
    correctedKernel_hermitian (J i) (J l) p.1 p.2

/-- The operator `P_B = I + R_B` used by the repair construction. -/
def correctedLowBandIdentityPlus {ι : Type*} [Fintype ι] (J : ι → ℤ) (B : ℝ) :
    LowBandHilbert J B →L[ℂ] LowBandHilbert J B :=
  ContinuousLinearMap.id ℂ _ + correctedLowBandOperator J B

theorem correctedLowBandIdentityPlus_apply {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (f : LowBandHilbert J B) :
    correctedLowBandIdentityPlus J B f = f + correctedLowBandOperator J B f := rfl

end GapFamily.Analytic
