import GapFamily.Analytic.Kernel.FullKernelThermal
import GapFamily.Analytic.Foundation.SignedMomentIntegral
import Mathlib.MeasureTheory.Integral.Prod

/-! Uniform physical and thermal bounds for ordinary compact signed input rows. -/

noncomputable section

namespace GapFamily.Analytic

open Set MeasureTheory
open scoped Real

/-- The full physical kernel is uniformly bounded by the product of its two energies. -/
theorem exists_fullKernelHol_physical_mul_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (j J : ℤ) (e E : ℝ),
      |(j : ℝ)| ≤ e → |(J : ℝ)| ≤ E → ‖fullKernelHol j J e E‖ ≤ C * (e * E) := by
  obtain ⟨C, hC, hbound⟩ := exists_centralKernel_bound
  refine ⟨C + 32 * π ^ 2, by positivity, ?_⟩
  intro j J e E he hE
  have he0 : 0 ≤ e := (abs_nonneg _).trans he
  have hE0 : 0 ≤ E := (abs_nonneg _).trans hE
  calc
    _ ≤ ‖centralKernel j J‖ + ‖higherKernel j J e E‖ := norm_add_le _ _
    _ ≤ C * (|(j : ℝ)| * |(J : ℝ)|) + 32 * π ^ 2 * (e * E) :=
      add_le_add (hbound j J) (norm_higherKernel_physical_le_mul j J e E he hE)
    _ ≤ C * (e * E) + 32 * π ^ 2 * (e * E) := by gcongr
    _ = _ := by ring

/-- One fixed constant for every physical row, column, and energy pair. -/
def fullKernelPhysicalMulBound : ℝ := Classical.choose exists_fullKernelHol_physical_mul_bound

theorem fullKernelPhysicalMulBound_pos : 0 < fullKernelPhysicalMulBound :=
  (Classical.choose_spec exists_fullKernelHol_physical_mul_bound).1

theorem norm_fullKernelHol_physical_le_mul (j J : ℤ) (e E : ℝ)
    (he : |(j : ℝ)| ≤ e) (hE : |(J : ℝ)| ≤ E) :
    ‖fullKernelHol j J e E‖ ≤ fullKernelPhysicalMulBound * (e * E) :=
  (Classical.choose_spec exists_fullKernelHol_physical_mul_bound).2 j J e E he hE

/-- Compact physical input has one thermal envelope independent of its input energy and spin. -/
theorem norm_thermal_fullKernelHol_on_band_le (j J : ℤ) (e E B t : ℝ)
    (he : |(j : ℝ)| ≤ e) (hE : |(J : ℝ)| ≤ E) (hEB : E ≤ B) :
    ‖Complex.exp (-(t : ℂ) * (e : ℂ)) * fullKernelHol j J e E‖ ≤
      (fullKernelPhysicalMulBound * B) * (e * Real.exp (-t * e)) := by
  have he0 : 0 ≤ e := (abs_nonneg _).trans he
  have hC := fullKernelPhysicalMulBound_pos
  rw [norm_mul, norm_exp_thermal]
  calc
    _ ≤ Real.exp (-t * e) * (fullKernelPhysicalMulBound * (e * E)) :=
      mul_le_mul_of_nonneg_left (norm_fullKernelHol_physical_le_mul j J e E he hE)
        (Real.exp_pos _).le
    _ ≤ Real.exp (-t * e) * (fullKernelPhysicalMulBound * (e * B)) := by gcongr
    _ = _ := by ring

/-- Ordinary product integrability supplies the signed-row Fourier--Laplace Fubini hypothesis. -/
theorem integrable_thermal_fullKernelHol_compactInput_prod (ν : SignedMeasure ℝ)
    (j J : ℤ) (B : ℝ) (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ B)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun p : ℝ × ℝ => Complex.exp (-(t : ℂ) * (p.2 : ℂ)) *
      fullKernelHol j J p.2 p.1) (ν.variation.prod (referenceMeasure j)) := by
  let := signedMeasure_isFiniteMeasure_variation ν
  have hbase := (integrable_const (fullKernelPhysicalMulBound * B)
    (μ := ν.variation)).mul_prod (integrable_energy_exp_referenceMeasure j ht)
  have hpair : Continuous (fun p : ℝ × ℝ => ((p.2 : ℂ), (p.1 : ℂ))) :=
    (Complex.continuous_ofReal.comp continuous_snd).prodMk
      (Complex.continuous_ofReal.comp continuous_fst)
  have hc : Continuous (fun p : ℝ × ℝ => fullKernelHol j J p.2 p.1) := by
    simpa only [Function.comp_def] using (continuous_fullKernelHol j J).comp hpair
  apply hbase.mono'
  · exact ((Complex.continuous_exp.comp
      (continuous_const.mul (Complex.continuous_ofReal.comp continuous_snd))).mul hc).aestronglyMeasurable
  · filter_upwards [Measure.quasiMeasurePreserving_fst.ae hs,
      Measure.quasiMeasurePreserving_snd.ae (referenceMeasure_ae_above_edge j)] with p hE he
    exact norm_thermal_fullKernelHol_on_band_le j J p.2 p.1 B t he.le hE.1 hE.2

/-- Product absolute mass is bounded by input variation mass times the ordinary reference moment. -/
theorem integral_norm_thermal_fullKernelHol_compactInput_prod_le (ν : SignedMeasure ℝ)
    (j J : ℤ) (B : ℝ) (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ B)
    {t : ℝ} (ht : 0 < t) :
    (∫ p : ℝ × ℝ, ‖Complex.exp (-(t : ℂ) * (p.2 : ℂ)) * fullKernelHol j J p.2 p.1‖
      ∂ν.variation.prod (referenceMeasure j)) ≤
        (ν.variation.real univ * (fullKernelPhysicalMulBound * B)) *
          ∫ e, e * Real.exp (-t * e) ∂referenceMeasure j := by
  let := signedMeasure_isFiniteMeasure_variation ν
  calc
    _ ≤ ∫ p : ℝ × ℝ, (fullKernelPhysicalMulBound * B) * (p.2 * Real.exp (-t * p.2))
        ∂ν.variation.prod (referenceMeasure j) := by
      apply integral_mono_ae (integrable_thermal_fullKernelHol_compactInput_prod ν j J B hs ht).norm
        ((integrable_const (fullKernelPhysicalMulBound * B)
          (μ := ν.variation)).mul_prod (integrable_energy_exp_referenceMeasure j ht))
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae hs,
        Measure.quasiMeasurePreserving_snd.ae (referenceMeasure_ae_above_edge j)] with p hE he
      exact norm_thermal_fullKernelHol_on_band_le j J p.2 p.1 B t he.le hE.1 hE.2
    _ = (∫ _ : ℝ, fullKernelPhysicalMulBound * B ∂ν.variation) *
        ∫ e, e * Real.exp (-t * e) ∂referenceMeasure j :=
      integral_prod_mul (fun _ : ℝ => fullKernelPhysicalMulBound * B)
        (fun e : ℝ => e * Real.exp (-t * e))
    _ = _ := by simp only [integral_const, smul_eq_mul]

/-- Ordinary product absolute masses remain summable over the complete integer output spin set. -/
theorem summable_integral_norm_thermal_fullKernelHol_compactInput_prod (ν : SignedMeasure ℝ)
    (J : ℤ) (B : ℝ) (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ B)
    {t : ℝ} (ht : 0 < t) :
    Summable (fun j : ℤ => ∫ p : ℝ × ℝ,
      ‖Complex.exp (-(t : ℂ) * (p.2 : ℂ)) * fullKernelHol j J p.2 p.1‖
        ∂ν.variation.prod (referenceMeasure j)) := by
  apply ((summable_integral_energy_exp_referenceMeasure ht).mul_left
    (ν.variation.real univ * (fullKernelPhysicalMulBound * B))).of_nonneg_of_le
  · exact fun j => integral_nonneg fun _ => norm_nonneg _
  · exact fun j => integral_norm_thermal_fullKernelHol_compactInput_prod_le ν j J B hs ht

open Real

/-- The full holomorphic response of one genuine signed input measure. -/
def fullKernelSignedRowResponse (ν : SignedMeasure ℝ) (J j : ℤ) (e : ℝ) : ℂ :=
  ∫ᵛ E, fullKernelHol j J e E ∂<•ν

/-- Compact physical input support gives ordinary input integrability. -/
theorem fullKernelSignedRowResponse_integrable (ν : SignedMeasure ℝ) (J j : ℤ)
    (B : ℝ) (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ B) (e : ℝ) :
    ν.Integrable (fun E => fullKernelHol j J e E) := by
  let := signedMeasure_isFiniteMeasure_variation ν
  have hp : Continuous (fun E : ℝ => ((e : ℂ), (E : ℂ))) :=
    continuous_const.prodMk Complex.continuous_ofReal
  have hc := (continuous_fullKernelHol j J).comp hp
  have hi := hc.integrableOn_Icc (μ := ν.variation) (a := |(J : ℝ)|) (b := B)
  have hr : ν.variation.restrict (Icc |(J : ℝ)| B) = ν.variation :=
    Measure.restrict_eq_self_of_ae_mem hs
  rw [IntegrableOn, hr] at hi
  exact hi

/-- Jordan decomposition supplies ordinary measurable parameter integrals. -/
theorem fullKernelSignedRowResponse_stronglyMeasurable (ν : SignedMeasure ℝ)
    (J j : ℤ) (B : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ B) :
    StronglyMeasurable (fullKernelSignedRowResponse ν J j) := by
  have heq : fullKernelSignedRowResponse ν J j = fun e : ℝ =>
      (∫ E, fullKernelHol j J e E ∂ν.toJordanDecomposition.posPart) -
        ∫ E, fullKernelHol j J e E ∂ν.toJordanDecomposition.negPart := by
    funext e
    exact signedIntegral_eq_jordan (fullKernelSignedRowResponse_integrable ν J j B hs e)
  rw [heq]
  have hp : Continuous (fun p : ℝ × ℝ => ((p.1 : ℂ), (p.2 : ℂ))) :=
      ((Complex.continuous_ofReal.comp continuous_fst).prodMk
        (Complex.continuous_ofReal.comp continuous_snd))
  have hc : Continuous (fun p : ℝ × ℝ => fullKernelHol j J p.1 p.2) := by
    simpa only [Function.comp_def] using (continuous_fullKernelHol j J).comp hp
  exact hc.stronglyMeasurable.integral_prod_right'.sub
    hc.stronglyMeasurable.integral_prod_right'

/-- A uniform physical kernel bound controls the actual signed response. -/
theorem norm_fullKernelSignedRowResponse_le_of_bound (ν : SignedMeasure ℝ)
    (J j : ℤ) (B C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ (j J : ℤ) (e E : ℝ), |(j : ℝ)| ≤ e → |(J : ℝ)| ≤ E →
      ‖fullKernelHol j J e E‖ ≤ C * (e * E))
    (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ B)
    (e : ℝ) (he : |(j : ℝ)| ≤ e) :
    ‖fullKernelSignedRowResponse ν J j e‖ ≤
      ν.variation.real univ * C * (e * B) := by
  let := signedMeasure_isFiniteMeasure_variation ν
  have he0 := (abs_nonneg (j : ℝ)).trans he
  have hbound : ∀ᵐ E : ℝ ∂ν.variation, ‖fullKernelHol j J e E‖ ≤ C * (e * B) := by
    filter_upwards [hs] with E hE
    exact (hb j J e E he hE.1).trans (by gcongr; exact hE.2)
  have h := VectorMeasure.norm_integral_le_of_norm_le_const
    (B := (ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ)).flip) hbound
  simpa only [fullKernelSignedRowResponse, ContinuousLinearMap.opNorm_flip,
    ContinuousLinearMap.opNorm_lsmul, mul_one, one_mul, mul_comm, mul_left_comm,
    mul_assoc] using h

/-- Thermal domination retains the scalar-channel energy factor. -/
theorem norm_thermal_fullKernelSignedRowResponse_le_of_bound (ν : SignedMeasure ℝ)
    (J j : ℤ) (B C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ (j J : ℤ) (e E : ℝ), |(j : ℝ)| ≤ e → |(J : ℝ)| ≤ E →
      ‖fullKernelHol j J e E‖ ≤ C * (e * E))
    (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ B)
    (e t : ℝ) (he : |(j : ℝ)| ≤ e) :
    ‖Complex.exp (-(t : ℂ) * (e : ℂ)) * fullKernelSignedRowResponse ν J j e‖ ≤
      (ν.variation.real univ * C * B) * (e * exp (-t * e)) := by
  rw [norm_mul, norm_exp_thermal]
  calc
    _ ≤ exp (-t * e) * (ν.variation.real univ * C * (e * B)) :=
      mul_le_mul_of_nonneg_left
        (norm_fullKernelSignedRowResponse_le_of_bound ν J j B C hC hb hs e he)
        (exp_pos _).le
    _ = _ := by ring

/-- Compact signed physical input has a genuine ordinary thermal output. -/
theorem integrable_thermal_fullKernelSignedRowResponse_of_bound (ν : SignedMeasure ℝ)
    (J j : ℤ) (B C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ (j J : ℤ) (e E : ℝ), |(j : ℝ)| ≤ e → |(J : ℝ)| ≤ E →
      ‖fullKernelHol j J e E‖ ≤ C * (e * E))
    (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ B)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun e : ℝ =>
      Complex.exp (-(t : ℂ) * (e : ℂ)) * fullKernelSignedRowResponse ν J j e)
      (referenceMeasure j) := by
  apply ((integrable_energy_exp_referenceMeasure j ht).const_mul
    (ν.variation.real univ * C * B)).mono'
  · exact ((Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal)).stronglyMeasurable.mul
        (fullKernelSignedRowResponse_stronglyMeasurable ν J j B hs)).aestronglyMeasurable
  · filter_upwards [referenceMeasure_ae_above_edge j] with e he
    exact norm_thermal_fullKernelSignedRowResponse_le_of_bound ν J j B C hC hb hs e t he.le

/-- Full absolute thermal output is summable over every integer spin. -/
theorem summable_integral_norm_thermal_fullKernelSignedRowResponse_of_bound
    (ν : SignedMeasure ℝ) (J : ℤ) (B C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ (j J : ℤ) (e E : ℝ), |(j : ℝ)| ≤ e → |(J : ℝ)| ≤ E →
      ‖fullKernelHol j J e E‖ ≤ C * (e * E))
    (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ B)
    {t : ℝ} (ht : 0 < t) :
    Summable (fun j : ℤ => ∫ e : ℝ,
      ‖Complex.exp (-(t : ℂ) * (e : ℂ)) * fullKernelSignedRowResponse ν J j e‖
        ∂referenceMeasure j) := by
  apply ((summable_integral_energy_exp_referenceMeasure ht).mul_left
    (ν.variation.real univ * C * B)).of_nonneg_of_le
  · exact fun j => integral_nonneg fun _ => norm_nonneg _
  · intro j
    calc
      _ ≤ ∫ e, (ν.variation.real univ * C * B) * (e * exp (-t * e))
          ∂referenceMeasure j := by
        apply integral_mono_ae
          (integrable_thermal_fullKernelSignedRowResponse_of_bound ν J j B C hC hb hs ht).norm
          ((integrable_energy_exp_referenceMeasure j ht).const_mul _)
        filter_upwards [referenceMeasure_ae_above_edge j] with e he
        exact norm_thermal_fullKernelSignedRowResponse_le_of_bound ν J j B C hC hb hs e t he.le
      _ = _ := integral_const_mul _ _

/-- The proved physical constant controls the actual signed input response. -/
theorem norm_fullKernelSignedRowResponse_le (ν : SignedMeasure ℝ) (J j : ℤ)
    (B : ℝ) (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ B)
    (e : ℝ) (he : |(j : ℝ)| ≤ e) :
    ‖fullKernelSignedRowResponse ν J j e‖ ≤
      ν.variation.real univ * fullKernelPhysicalMulBound * (e * B) :=
  norm_fullKernelSignedRowResponse_le_of_bound ν J j B fullKernelPhysicalMulBound
    fullKernelPhysicalMulBound_pos.le norm_fullKernelHol_physical_le_mul hs e he

/-- Every compact physical signed row has an actual ordinary thermal output. -/
theorem integrable_thermal_fullKernelSignedRowResponse (ν : SignedMeasure ℝ) (J j : ℤ)
    (B : ℝ) (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ B)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun e : ℝ => Complex.exp (-(t : ℂ) * (e : ℂ)) *
      fullKernelSignedRowResponse ν J j e) (referenceMeasure j) :=
  integrable_thermal_fullKernelSignedRowResponse_of_bound ν J j B fullKernelPhysicalMulBound
    fullKernelPhysicalMulBound_pos.le norm_fullKernelHol_physical_le_mul hs ht

/-- The actual signed-row thermal output is absolutely summable over every integer spin. -/
theorem summable_integral_norm_thermal_fullKernelSignedRowResponse (ν : SignedMeasure ℝ)
    (J : ℤ) (B : ℝ) (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ B)
    {t : ℝ} (ht : 0 < t) :
    Summable (fun j : ℤ => ∫ e : ℝ,
      ‖Complex.exp (-(t : ℂ) * (e : ℂ)) * fullKernelSignedRowResponse ν J j e‖
        ∂referenceMeasure j) :=
  summable_integral_norm_thermal_fullKernelSignedRowResponse_of_bound ν J B
    fullKernelPhysicalMulBound fullKernelPhysicalMulBound_pos.le
    norm_fullKernelHol_physical_le_mul hs ht

end GapFamily.Analytic
