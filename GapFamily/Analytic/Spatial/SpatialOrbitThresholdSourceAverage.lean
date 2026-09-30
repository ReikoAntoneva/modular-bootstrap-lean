import GapFamily.Analytic.Spatial.SpatialOrbitThresholdContinuity
import GapFamily.Analytic.Spatial.SpatialOrbitSourceIntegral
import GapFamily.Analytic.Spatial.SpatialOrbitMeanZeroSchur
import GapFamily.Analytic.Modular.Elliptic.ModularUpperCoreEvaluation

/-! Ordinary Bochner averages of the actual weighted threshold point source,
their compact observation, and their physical integral-operator identity. -/
noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open Set Filter MeasureTheory UpperHalfPlane ModularGradient CuspSchurLocal Dirichlet
open UpperWeightedCoherence
open scoped Topology

/-- Ordinary weighted-source superposition in the actual modular Hilbert space. -/
def spatialOrbitThresholdSourceAverage (s : ℂ) (f : ModularHilbert) : ModularHilbert :=
  ∫ w, f w • spatialOrbitThresholdInput s w ∂modularMeasure

theorem spatialOrbitThresholdSourceAverage_eq (s : ℂ) (f : ModularHilbert) :
    spatialOrbitThresholdSourceAverage s f = s ^ 2 •
      ∫ w, f w • spatialOrbitWeightedSource (1 / 4) (by norm_num) (by norm_num)
        (s + 1) w ∂modularMeasure := by
  rw [spatialOrbitThresholdSourceAverage, ← integral_smul]
  apply integral_congr_ae
  exact Eventually.of_forall fun w => by
    simp only [spatialOrbitThresholdInput, smul_smul, mul_comm (f w)]

theorem integrable_spatialOrbitThresholdInput_smul (s : ℂ) (f : ModularHilbert)
    (hi : Integrable (fun w => f w •
      spatialOrbitWeightedSource (1 / 4) (by norm_num) (by norm_num) (s + 1) w)
        modularMeasure) :
    Integrable (fun w => f w • spatialOrbitThresholdInput s w) modularMeasure := by
  convert hi.smul (s ^ 2) using 1
  funext w
  simp only [spatialOrbitThresholdInput, Pi.smul_apply, smul_smul, mul_comm (f w)]

theorem integrable_spatialOrbitThresholdInput_smul_of_compact_support
    (s : ℂ) (hs : 0 < s.re) (f : ModularHilbert)
    (S : Set UpperHalfPlane) (hS : IsCompact S)
    (hf : ∀ᵐ w ∂modularMeasure, w ∉ S → f w = 0) :
    Integrable (fun w => f w • spatialOrbitThresholdInput s w) modularMeasure := by
  apply integrable_spatialOrbitThresholdInput_smul
  apply integrable_smul_spatialOrbitWeightedSource_of_compact_support
    (1 / 4) (by norm_num) (by norm_num) (s + 1) _ f S hS hf
  simp only [Complex.add_re, Complex.one_re]
  linarith

/-- The weighted average has exactly the literal shifted integral-operator
source after removing the cusp weight. -/
theorem cuspWeightedInput_spatialOrbitThresholdSourceAverage
    (s : ℝ) (hs : 0 < s) (f : ModularHilbert)
    (hi : Integrable (fun w => f w •
      spatialOrbitWeightedSource (1 / 4) (by norm_num) (by norm_num)
        ((s + 1 : ℝ) : ℂ) w) modularMeasure) :
    cuspWeightedInput (1 / 4) (by norm_num)
      (spatialOrbitThresholdSourceAverage (s : ℂ) f) =
        (s : ℂ) ^ 2 • spatialOrbitIntegralOperator (s + 1) (by linarith) f := by
  rw [spatialOrbitThresholdSourceAverage_eq, map_smul]
  congr 1
  simpa only [Complex.ofReal_add, Complex.ofReal_one] using
    cuspWeightedInput_integral_spatialOrbitWeightedSource (1 / 4) (by norm_num)
      (by norm_num) (s + 1) (by linarith) f hi

/-- The fixed compact evaluator applied to one actual point source. -/
def spatialOrbitCompactResponse {K : Set ℂ} [CompactSpace K]
    (D : Evaluation (1 / 4) (by norm_num) K) (s : ℂ) (w : UpperHalfPlane) : C(K, ℂ) :=
  D.family (s - 1 / 2) (spatialOrbitThresholdInput s w)

theorem continuous_spatialOrbitCompactResponse_source {K : Set ℂ} [CompactSpace K]
    (D : Evaluation (1 / 4) (by norm_num) K) (s : ℂ) (hs : 0 < s.re) :
    Continuous (spatialOrbitCompactResponse D s) :=
  (D.family (s - 1 / 2)).continuous.comp
    (continuous_spatialOrbitThresholdInput_source s hs)

theorem continuous_spatialOrbitCorrectedResponse {K : Set ℂ} [CompactSpace K]
    (D : Evaluation (1 / 4) (by norm_num) K) (s : ℂ) (hs : 0 < s.re) :
    Continuous (fun p : K × UpperHalfPlane =>
      spatialOrbitCorrectedEvaluation (spatialOrbitCompactResponse D) s p.2 p.1) := by
  have hF : Continuous (fun w =>
      spatialOrbitCorrectedEvaluation (spatialOrbitCompactResponse D) s w) :=
    (continuous_spatialOrbitCompactResponse_source D s hs).sub continuous_const
  exact (hF.comp continuous_snd).eval continuous_fst

theorem integrable_smul_spatialOrbitCorrectedResponse {K : Set ℂ} [CompactSpace K]
    (D : Evaluation (1 / 4) (by norm_num) K) (s : ℂ) (f : ModularHilbert)
    (hi : Integrable (fun w => f w • spatialOrbitThresholdInput s w) modularMeasure) :
    Integrable (fun w => f w • spatialOrbitCorrectedEvaluation
      (spatialOrbitCompactResponse D) s w) modularMeasure := by
  have hR : Integrable (fun w => f w • spatialOrbitCompactResponse D s w) modularMeasure := by
    simpa only [map_smul, spatialOrbitCompactResponse] using
      (D.family (s - 1 / 2)).integrable_comp hi
  apply (hR.sub ((integrable_modularHilbert f).smul_const
    ((3 / (s - 1) : ℂ) • (1 : C(K, ℂ))))).congr
  filter_upwards with w
  simp only [spatialOrbitCorrectedEvaluation, smul_sub, Pi.sub_apply]

/-- Compact observation commutes with ordinary source superposition. -/
theorem spatialOrbitCompactResponse_average {K : Set ℂ} [CompactSpace K]
    (D : Evaluation (1 / 4) (by norm_num) K) (s : ℂ) (f : ModularHilbert)
    (hi : Integrable (fun w => f w • spatialOrbitThresholdInput s w) modularMeasure) :
    D.family (s - 1 / 2) (spatialOrbitThresholdSourceAverage s f) =
      ∫ w, f w • spatialOrbitCompactResponse D s w ∂modularMeasure := by
  rw [spatialOrbitThresholdSourceAverage,
    ← (D.family (s - 1 / 2)).integral_comp_comm hi]
  simp only [map_smul, spatialOrbitCompactResponse]

/-- Every point of the compact observation has the corresponding ordinary
scalar integral, including boundary and thin observation sets. -/
theorem spatialOrbitCompactResponse_average_apply {K : Set ℂ} [CompactSpace K]
    (D : Evaluation (1 / 4) (by norm_num) K) (s : ℂ) (f : ModularHilbert)
    (hi : Integrable (fun w => f w • spatialOrbitThresholdInput s w) modularMeasure)
    (z : K) :
    D.family (s - 1 / 2) (spatialOrbitThresholdSourceAverage s f) z =
      ∫ w, f w * spatialOrbitCompactResponse D s w z ∂modularMeasure := by
  let T : ModularHilbert →L[ℂ] ℂ :=
    (ContinuousMap.evalCLM ℂ z).comp (D.family (s - 1 / 2))
  have he := (T.integral_comp_comm hi).symm
  simpa only [T, spatialOrbitThresholdSourceAverage, spatialOrbitCompactResponse,
    ContinuousLinearMap.comp_apply, ContinuousMap.evalCLM_apply,
    map_smul, smul_eq_mul] using he

/-- The physical average is the compact continuous representative of the actual
resolvent applied to `s² A_(s+1) f`. The sole integrability premise is ordinary
Bochner integrability of the literal weighted source family. -/
theorem spatialOrbitCompactResponse_average_physical {K : Set ℂ} [CompactSpace K]
    (D : Evaluation (1 / 4) (by norm_num) K)
    (s : ℝ) (hs : 1 / 2 < s) (hn : ‖(s : ℂ) - 1 / 2‖ < D.radius)
    (f : ModularHilbert)
    (hi : Integrable (fun w => f w •
      spatialOrbitWeightedSource (1 / 4) (by norm_num) (by norm_num)
        ((s + 1 : ℝ) : ℂ) w) modularMeasure) :
    ∃ hu : CuspSchur.actualSchurResolvent ((s : ℂ) * (1 - (s : ℂ)))
        ((s : ℂ) ^ 2 • spatialOrbitIntegralOperator (s + 1) (by linarith) f)
          ∈ laplacian.domain,
      (∫ w, f w • spatialOrbitCompactResponse D (s : ℂ) w ∂modularMeasure) =
        laplacianUpperCompactRestriction D.cutoff D.cutoff_smooth D.cutoff_compact
          D.cutoff_support D.region D.open_region D.one_region K D.compact_subset
          (gradientLift laplacian
            ⟨CuspSchur.actualSchurResolvent ((s : ℂ) * (1 - (s : ℂ)))
              ((s : ℂ) ^ 2 • spatialOrbitIntegralOperator (s + 1) (by linarith) f), hu⟩) := by
  have hs0 : 0 < s := by linarith
  have hi' := integrable_spatialOrbitThresholdInput_smul (s : ℂ) f
    (by simpa only [Complex.ofReal_add, Complex.ofReal_one] using hi)
  have hκ : 0 < ((s : ℂ) - 1 / 2).re := by
    norm_num [Complex.sub_re]
    linarith
  obtain ⟨hu, hvalue⟩ := D.physical ((s : ℂ) - 1 / 2) hn hκ
    (spatialOrbitThresholdSourceAverage (s : ℂ) f)
  have hparameter : parameter ((s : ℂ) - 1 / 2) = (s : ℂ) * (1 - (s : ℂ)) := by
    dsimp [parameter]
    ring
  have hsource := cuspWeightedInput_spatialOrbitThresholdSourceAverage s hs0 f hi
  have hres : CuspSchur.actualSchurResolvent (parameter ((s : ℂ) - 1 / 2))
      (cuspWeightedInput (1 / 4) (by norm_num) (spatialOrbitThresholdSourceAverage (s : ℂ) f)) =
      CuspSchur.actualSchurResolvent ((s : ℂ) * (1 - (s : ℂ)))
        ((s : ℂ) ^ 2 • spatialOrbitIntegralOperator (s + 1) (by linarith) f) := by
    rw [hparameter, hsource]
  refine ⟨hres ▸ hu, ?_⟩
  exact (spatialOrbitCompactResponse_average D (s : ℂ) f hi').symm.trans
    (hvalue.trans (congrArg
      (fun u : laplacian.domain => laplacianUpperCompactRestriction D.cutoff D.cutoff_smooth
        D.cutoff_compact D.cutoff_support D.region D.open_region D.one_region K D.compact_subset
          (gradientLift laplacian u)) (Subtype.ext hres)))

/-- All constructed compact responses have the canonical threshold row. -/
theorem spatialOrbitCompactResponse_half_apply {K : Set ℂ} [CompactSpace K]
    (D : Evaluation (1 / 4) (by norm_num) K) (z w : UpperHalfPlane)
    (hz : (z : ℂ) ∈ K) :
    spatialOrbitCompactResponse D (1 / 2) w ⟨(z : ℂ), hz⟩ = spatialThresholdKernel z w := by
  simpa only [spatialOrbitCompactResponse, sub_self, spatialThresholdKernel] using
    (weightedThresholdValue_eq_evaluation (by norm_num : (0 : ℝ) < 1 / 4)
      D (spatialOrbitThresholdInput (1 / 2) w) z hz).symm

/-- The actual threshold kernel average is the threshold compact observation of
the same ordinary weighted-source integral. -/
theorem spatialThresholdKernel_integral_eq {K : Set ℂ} [CompactSpace K]
    (D : Evaluation (1 / 4) (by norm_num) K) (f : ModularHilbert)
    (hi : Integrable (fun w => f w • spatialOrbitThresholdInput (1 / 2) w) modularMeasure)
    (z : UpperHalfPlane) (hz : (z : ℂ) ∈ K) :
    (∫ w, f w * spatialThresholdKernel z w ∂modularMeasure) =
      D.family 0 (spatialOrbitThresholdSourceAverage (1 / 2) f) ⟨(z : ℂ), hz⟩ := by
  simpa only [sub_self, spatialOrbitCompactResponse_half_apply D z _ hz] using
    (spatialOrbitCompactResponse_average_apply D (1 / 2) f hi ⟨(z : ℂ), hz⟩).symm

/-- The graph observation fixed by the actual compact evaluation data. -/
def spatialOrbitCompactGraphRestriction {K : Set ℂ} [CompactSpace K]
    (D : Evaluation (1 / 4) (by norm_num) K) : LaplacianGraphDomain →L[ℂ] C(K, ℂ) :=
  laplacianUpperCompactRestriction D.cutoff D.cutoff_smooth D.cutoff_compact
    D.cutoff_support D.region D.open_region D.one_region K D.compact_subset

theorem spatialOrbitCompactGraphRestriction_constant {K : Set ℂ} [CompactSpace K]
    (D : Evaluation (1 / 4) (by norm_num) K) :
    spatialOrbitCompactGraphRestriction D
      (gradientLift laplacian ⟨modularConstant, modularConstant_mem_laplacian_domain⟩) = 1 := by
  apply ContinuousMap.ext
  intro z
  exact laplacianUpperCompactEvaluation_core D.cutoff D.cutoff_smooth D.cutoff_compact
    D.cutoff_support D.region D.open_region D.one_region K D.compact_subset z
    (constantCore 1) modularConstant_mem_laplacian_domain

theorem spatialOrbitCompactGraphRestriction_constantProjection {K : Set ℂ} [CompactSpace K]
    (D : Evaluation (1 / 4) (by norm_num) K) (f : ModularHilbert) :
    spatialOrbitCompactGraphRestriction D
      (gradientLift laplacian
        ⟨modularConstantProjection f, constantProjection_mem_laplacian_domain f⟩) =
      modularAverage f • (1 : C(K, ℂ)) := by
  have he : gradientLift laplacian
      ⟨modularConstantProjection f, constantProjection_mem_laplacian_domain f⟩ =
      modularAverage f • gradientLift laplacian
        ⟨modularConstant, modularConstant_mem_laplacian_domain⟩ := by
    apply gradientEmbedding_injective laplacian
    simp only [map_smul, gradientEmbedding_lift]
    exact modularConstantProjection_apply f
  rw [he, map_smul, spatialOrbitCompactGraphRestriction_constant]

/-- Exact modular volume turns the spectral constant projection into the
literal kernel correction, with the same ordinary source integral. -/
theorem spatialOrbit_constantCorrection_average (s : ℝ) (hne : s ≠ 1)
    (f : ModularHilbert) :
    (((Real.pi / (s - 1) : ℝ) : ℂ)) * modularAverage f =
      (3 / ((s : ℂ) - 1)) * (∫ w, f w ∂modularMeasure) := by
  have hden : (s : ℂ) - 1 ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hne
  rw [modularAverage_apply, modularMeasure_real_univ]
  push_cast
  field_simp [hden, Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]

/-- The corrected compact kernel average is the continuous graph representative
of the actual positive mean-zero continuation operator before threshold. -/
theorem spatialOrbitCorrectedResponse_average_physical {K : Set ℂ} [CompactSpace K]
    (D : Evaluation (1 / 4) (by norm_num) K)
    (s : ℝ) (hs : 1 / 2 < s) (hne : s ≠ 1)
    (hn : ‖(s : ℂ) - 1 / 2‖ < D.radius) (f : ModularHilbert)
    (hi : Integrable (fun w => f w •
      spatialOrbitWeightedSource (1 / 4) (by norm_num) (by norm_num)
        ((s + 1 : ℝ) : ℂ) w) modularMeasure) :
    (∫ w, f w • spatialOrbitCorrectedEvaluation
        (spatialOrbitCompactResponse D) (s : ℂ) w ∂modularMeasure) =
      spatialOrbitCompactGraphRestriction D
        (gradientLift laplacian
          ⟨spatialOrbitMeanZeroContinuation s hs f,
            spatialOrbitMeanZeroContinuation_mem_laplacian_domain s hs f⟩) := by
  obtain ⟨hu, hvalue⟩ := spatialOrbitCompactResponse_average_physical D s hs hn f hi
  let q := CuspSchur.actualSchurResolvent ((s : ℂ) * (1 - (s : ℂ)))
    ((s : ℂ) ^ 2 • spatialOrbitIntegralOperator (s + 1) (by linarith) f)
  let c : ℂ := ((Real.pi / (s - 1) : ℝ) : ℂ)
  let a : ℂ := 3 / ((s : ℂ) - 1)
  have hT : spatialOrbitMeanZeroContinuation s hs f = q - c • modularConstantProjection f := by
    have he := congrArg (fun A : ModularHilbert →L[ℂ] ModularHilbert => A f)
      (spatialOrbitMeanZeroContinuation_eq_actualSchur_sub_constant s hs hne)
    change spatialOrbitMeanZeroContinuation s hs f =
      (s : ℂ) ^ 2 • CuspSchur.actualSchurResolvent ((s * (1 - s) : ℝ) : ℂ)
        (spatialOrbitIntegralOperator (s + 1) (by linarith) f) -
      c • modularConstantProjection f at he
    simpa only [q, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one, map_smul] using he
  have hgraph : gradientLift laplacian
      ⟨spatialOrbitMeanZeroContinuation s hs f,
        spatialOrbitMeanZeroContinuation_mem_laplacian_domain s hs f⟩ =
      gradientLift laplacian ⟨q, hu⟩ -
        c • gradientLift laplacian
          ⟨modularConstantProjection f, constantProjection_mem_laplacian_domain f⟩ := by
    apply gradientEmbedding_injective laplacian
    simp only [map_sub, map_smul, gradientEmbedding_lift]
    exact hT
  have hi' := integrable_spatialOrbitThresholdInput_smul (s : ℂ) f
    (by simpa only [Complex.ofReal_add, Complex.ofReal_one] using hi)
  have hiR : Integrable (fun w => f w • spatialOrbitCompactResponse D (s : ℂ) w)
      modularMeasure := by
    simpa only [map_smul, spatialOrbitCompactResponse] using
      (D.family ((s : ℂ) - 1 / 2)).integrable_comp hi'
  have hiC := (integrable_modularHilbert f).smul_const (a • (1 : C(K, ℂ)))
  rw [hgraph, map_sub, map_smul, spatialOrbitCompactGraphRestriction_constantProjection,
    smul_smul, spatialOrbit_constantCorrection_average s hne f]
  change _ = spatialOrbitCompactGraphRestriction D (gradientLift laplacian ⟨q, hu⟩) -
    (a * (∫ w, f w ∂modularMeasure)) • (1 : C(K, ℂ))
  change (∫ w, f w • spatialOrbitCompactResponse D (s : ℂ) w ∂modularMeasure) =
    spatialOrbitCompactGraphRestriction D (gradientLift laplacian ⟨q, hu⟩) at hvalue
  rw [← hvalue]
  calc
    _ = (∫ w, f w • spatialOrbitCompactResponse D (s : ℂ) w ∂modularMeasure) -
        ∫ w, f w • (a • (1 : C(K, ℂ))) ∂modularMeasure := by
      simp only [spatialOrbitCorrectedEvaluation, smul_sub]
      exact integral_sub hiR hiC
    _ = _ := by
      rw [integral_smul_const, smul_smul, mul_comm (∫ w, f w ∂modularMeasure) a]

/-- For compactly supported Hilbert inputs the source integrability premise is
already proved, so the corrected average identity has no residual hypothesis. -/
theorem spatialOrbitCorrectedResponse_average_physical_of_compact_support
    {K : Set ℂ} [CompactSpace K] (D : Evaluation (1 / 4) (by norm_num) K)
    (s : ℝ) (hs : 1 / 2 < s) (hne : s ≠ 1)
    (hn : ‖(s : ℂ) - 1 / 2‖ < D.radius) (f : ModularHilbert)
    (S : Set UpperHalfPlane) (hS : IsCompact S)
    (hf : ∀ᵐ w ∂modularMeasure, w ∉ S → f w = 0) :
    (∫ w, f w • spatialOrbitCorrectedEvaluation
        (spatialOrbitCompactResponse D) (s : ℂ) w ∂modularMeasure) =
      spatialOrbitCompactGraphRestriction D
        (gradientLift laplacian
          ⟨spatialOrbitMeanZeroContinuation s hs f,
            spatialOrbitMeanZeroContinuation_mem_laplacian_domain s hs f⟩) :=
  spatialOrbitCorrectedResponse_average_physical D s hs hne hn f
    (integrable_smul_spatialOrbitWeightedSource_of_compact_support
      (1 / 4) (by norm_num) (by norm_num) ((s + 1 : ℝ) : ℂ) (by norm_num; linarith)
      f S hS hf)

/-- Pointwise ordinary integral form of the corrected operator identity. -/
theorem spatialOrbitCorrectedResponse_average_apply_of_compact_support
    {K : Set ℂ} [CompactSpace K] (D : Evaluation (1 / 4) (by norm_num) K)
    (s : ℝ) (hs : 1 / 2 < s) (hne : s ≠ 1)
    (hn : ‖(s : ℂ) - 1 / 2‖ < D.radius) (f : ModularHilbert)
    (S : Set UpperHalfPlane) (hS : IsCompact S)
    (hf : ∀ᵐ w ∂modularMeasure, w ∉ S → f w = 0) (z : K) :
    (∫ w, f w * spatialOrbitCorrectedEvaluation
        (spatialOrbitCompactResponse D) (s : ℂ) w z ∂modularMeasure) =
      spatialOrbitCompactGraphRestriction D
        (gradientLift laplacian
          ⟨spatialOrbitMeanZeroContinuation s hs f,
            spatialOrbitMeanZeroContinuation_mem_laplacian_domain s hs f⟩) z := by
  have hi := integrable_smul_spatialOrbitCorrectedResponse D (s : ℂ) f
    (integrable_spatialOrbitThresholdInput_smul_of_compact_support (s : ℂ)
      (by norm_num; linarith) f S hS hf)
  have he := (ContinuousMap.evalCLM ℂ z).integral_comp_comm hi
  have hvalue := congrArg (fun F : C(K, ℂ) => F z)
    (spatialOrbitCorrectedResponse_average_physical_of_compact_support D s hs hne hn f S hS hf)
  calc
    _ = (∫ w, f w • spatialOrbitCorrectedEvaluation
        (spatialOrbitCompactResponse D) (s : ℂ) w ∂modularMeasure) z := by
      simpa only [map_smul, ContinuousMap.evalCLM_apply, smul_eq_mul] using he
    _ = _ := hvalue

end GapFamily.Analytic.SpatialPoint
