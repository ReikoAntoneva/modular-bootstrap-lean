import GapFamily.Analytic.Spatial.SpatialOrbitThresholdEvaluation
import GapFamily.Analytic.Spatial.SpatialOrbitWeightedNormBound
import GapFamily.Analytic.Foundation.AnalyticDominatedIntegral

/-!
# Analytic Fourier and height tests of the actual weighted source

Horizontal integration is performed in the actual weighted modular Hilbert
space. A compact horizontal row and a smaller real exponent give a uniform
norm bound on a complex parameter disk, so ordinary dominated Bochner
integration preserves analyticity in `Re s > 0`.
-/

noncomputable section

namespace GapFamily.Analytic.SpatialPoint

open Set Filter MeasureTheory Metric
open scoped Topology

/-- The ordinary horizontal Fourier test of the actual shifted weighted source. -/
def spatialSourceFourierInput (s : ℂ) (J : ℤ) (l : ℕ) : ModularHilbert :=
  ∫ x : ℝ in 0..1,
    horizontalPhase J x • spatialOrbitThresholdInput s (laplacePoint l x)

/-- A normalized horizontal source test at one positive Laplace height. -/
def spatialSourceNormalizedFourierInput (s : ℂ) (J : ℤ) (l : ℕ) : ModularHilbert :=
  (laplaceHeight l : ℂ) ^ (-s) • spatialSourceFourierInput s J l

/-- The input-side adjacent normalized height difference. -/
def spatialSourceFourierHeightInput (s : ℂ) (J : ℤ) (l : ℕ) : ModularHilbert :=
  spatialSourceNormalizedFourierInput s J l - spatialSourceNormalizedFourierInput s J (l + 1)

private theorem continuous_horizontalPhase (J : ℤ) : Continuous (horizontalPhase J) := by
  unfold horizontalPhase
  fun_prop

private theorem norm_horizontalPhase (J : ℤ) (x : ℝ) : ‖horizontalPhase J x‖ = 1 := by
  simp [horizontalPhase, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

theorem continuous_spatialSourceFourierIntegrand (s : ℂ) (hs : 0 < s.re) (J : ℤ) (l : ℕ) :
    Continuous (fun x : ℝ =>
      horizontalPhase J x • spatialOrbitThresholdInput s (laplacePoint l x)) :=
  (continuous_horizontalPhase J).smul
    ((continuous_spatialOrbitThresholdInput_source s hs).comp (continuous_laplacePoint l))

/-- These completed-space source integrals are ordinary Bochner integrals. -/
theorem intervalIntegrable_spatialSourceFourierIntegrand
    (s : ℂ) (hs : 0 < s.re) (J : ℤ) (l : ℕ) :
    IntervalIntegrable (fun x : ℝ =>
      horizontalPhase J x • spatialOrbitThresholdInput s (laplacePoint l x)) volume 0 1 :=
  (continuous_spatialSourceFourierIntegrand s hs J l).intervalIntegrable _ _

/-- Ordinary horizontal integration preserves analyticity of the actual
shifted source throughout `Re s > 0`. -/
theorem analyticAt_spatialSourceFourierInput (J : ℤ) (l : ℕ) {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ (fun t => spatialSourceFourierInput t J l) s := by
  let r : ℝ := s.re / 2
  let σ : ℝ := 1 + s.re / 2
  have hr : 0 < r := half_pos hs
  have hσ : 1 < σ := by dsimp [σ]; linarith
  have hstrip {t : ℂ} (ht : t ∈ ball s r) : σ ≤ (t + 1).re := by
    have hn : ‖t - s‖ < r := by simpa only [mem_ball, dist_eq_norm] using ht
    have hre := Complex.abs_re_le_norm (t - s)
    have hlo := neg_abs_le (t - s).re
    simp only [Complex.sub_re] at hre hlo
    simp only [Complex.add_re, Complex.one_re]
    dsimp [σ, r] at *
    linarith
  have hpositive {t : ℂ} (ht : t ∈ ball s r) : 0 < t.re := by
    have ht' := hstrip ht
    simp only [Complex.add_re, Complex.one_re] at ht'
    linarith
  obtain ⟨C, hC, hbound⟩ := exists_spatialOrbitWeightedSource_laplacePoint_bound
    (1 / 4) (by norm_num) (by norm_num) σ hσ l
  have hnorm {t : ℂ} (ht : t ∈ ball s r) : ‖t‖ ≤ ‖s‖ + r := by
    have hn : ‖t - s‖ < r := by simpa only [mem_ball, dist_eq_norm] using ht
    calc
      ‖t‖ ≤ ‖t - s‖ + ‖s‖ := by simpa using norm_add_le (t - s) s
      _ ≤ r + ‖s‖ := add_le_add hn.le le_rfl
      _ = ‖s‖ + r := add_comm _ _
  simp only [spatialSourceFourierInput,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  apply DominatedAnalytic.analyticAt_integral_of_dominated
    (bound := fun _ : ℝ => (‖s‖ + r) ^ 2 * C) hr
  · intro t ht
    exact (continuous_spatialSourceFourierIntegrand t (hpositive ht) J l).aestronglyMeasurable
  · exact Eventually.of_forall fun x t ht => by
      convert!
        (analyticAt_spatialOrbitThresholdInput (laplacePoint l x) (hpositive ht)).const_smul
          (c := horizontalPhase J x) using 1
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    intro t ht
    simp only [spatialOrbitThresholdInput, norm_smul, norm_pow, norm_horizontalPhase, one_mul]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg t) (hnorm ht) 2)
      (hbound x ⟨hx.1.le, hx.2⟩ (t + 1) (hstrip ht)) (norm_nonneg _) (by positivity)
  · exact integrable_const _

theorem analyticAt_spatialSourceNormalizedFourierInput (J : ℤ) (l : ℕ)
    {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ (fun t => spatialSourceNormalizedFourierInput t J l) s := by
  have hn : (laplaceHeight l : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (laplaceHeight_pos l).ne'
  exact ((differentiable_id.neg.const_cpow (Or.inl hn)).analyticAt s).smul
    (analyticAt_spatialSourceFourierInput J l hs)

/-- Both normalized heights remain in one analytic completed-space family. -/
theorem analyticAt_spatialSourceFourierHeightInput (J : ℤ) (l : ℕ)
    {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ (fun t => spatialSourceFourierHeightInput t J l) s :=
  (analyticAt_spatialSourceNormalizedFourierInput J l hs).sub
    (analyticAt_spatialSourceNormalizedFourierInput J (l + 1) hs)

theorem analyticOnNhd_spatialSourceFourierHeightInput (J : ℤ) (l : ℕ) :
    AnalyticOnNhd ℂ (fun s => spatialSourceFourierHeightInput s J l) {s : ℂ | 0 < s.re} :=
  fun _ hs => analyticAt_spatialSourceFourierHeightInput J l hs

/-- Any actual bounded observation commutes with the ordinary source integral. -/
theorem map_spatialSourceFourierInput {B : Type*} [NormedAddCommGroup B]
    [NormedSpace ℝ B] [NormedSpace ℂ B] [CompleteSpace B]
    (L : ModularHilbert →L[ℂ] B) (s : ℂ) (hs : 0 < s.re) (J : ℤ) (l : ℕ) :
    L (spatialSourceFourierInput s J l) =
      ∫ x : ℝ in 0..1,
        horizontalPhase J x • L (spatialOrbitThresholdInput s (laplacePoint l x)) := by
  rw [spatialSourceFourierInput, ← L.intervalIntegral_comp_comm
    (intervalIntegrable_spatialSourceFourierIntegrand s hs J l)]
  simp only [map_smul]

theorem map_spatialSourceFourierHeightInput {B : Type*} [NormedAddCommGroup B]
    [NormedSpace ℝ B] [NormedSpace ℂ B] [CompleteSpace B]
    (L : ModularHilbert →L[ℂ] B) (s : ℂ) (hs : 0 < s.re) (J : ℤ) (l : ℕ) :
    L (spatialSourceFourierHeightInput s J l) =
      (laplaceHeight l : ℂ) ^ (-s) •
        (∫ x : ℝ in 0..1,
          horizontalPhase J x • L (spatialOrbitThresholdInput s (laplacePoint l x))) -
      (laplaceHeight (l + 1) : ℂ) ^ (-s) •
        (∫ x : ℝ in 0..1,
          horizontalPhase J x • L (spatialOrbitThresholdInput s (laplacePoint (l + 1) x))) := by
  rw [spatialSourceFourierHeightInput, map_sub, spatialSourceNormalizedFourierInput,
    spatialSourceNormalizedFourierInput, map_smul, map_smul,
    map_spatialSourceFourierInput L s hs, map_spatialSourceFourierInput L s hs]

/-- Point evaluation of any actual compact observation gives the literal
scalar Fourier/height test of the observed spatial source. -/
theorem eval_map_spatialSourceFourierHeightInput {K : Type*} [TopologicalSpace K]
    [CompactSpace K] (L : ModularHilbert →L[ℂ] C(K, ℂ)) (z : K)
    (s : ℂ) (hs : 0 < s.re) (J : ℤ) (l : ℕ) :
    L (spatialSourceFourierHeightInput s J l) z =
      (laplaceHeight l : ℂ) ^ (-s) *
        (∫ x : ℝ in 0..1,
          horizontalPhase J x * L (spatialOrbitThresholdInput s (laplacePoint l x)) z) -
      (laplaceHeight (l + 1) : ℂ) ^ (-s) *
        (∫ x : ℝ in 0..1,
          horizontalPhase J x * L (spatialOrbitThresholdInput s (laplacePoint (l + 1) x)) z) := by
  simpa only [ContinuousLinearMap.comp_apply, ContinuousMap.evalCLM_apply, smul_eq_mul] using
    map_spatialSourceFourierHeightInput ((ContinuousMap.evalCLM ℂ z).comp L) s hs J l

private theorem laplaceHeight_cpow_neg_half (l : ℕ) :
    (laplaceHeight l : ℂ) ^ (-(1 / 2 : ℂ)) = laplaceHeightWeight l := by
  rw [Complex.cpow_neg]
  unfold laplaceHeightWeight
  congr 1
  simpa only [Real.sqrt_eq_rpow, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_ofNat] using
      (Complex.ofReal_cpow (laplaceHeight_pos l).le (1 / 2)).symm

/-- The source family specializes to the literal normalized input Fourier
and height test of the canonical threshold kernel. -/
theorem weightedThresholdValue_spatialSourceFourierHeightInput
    (z : UpperHalfPlane) (J : ℤ) (l : ℕ) :
    UpperWeightedCoherence.weightedThresholdValue (1 / 4) (by norm_num)
      (spatialSourceFourierHeightInput (1 / 2) J l) z =
      laplaceHeightWeight l *
        (∫ x : ℝ in 0..1, horizontalPhase J x * spatialThresholdKernel z (laplacePoint l x)) -
      laplaceHeightWeight (l + 1) *
        (∫ x : ℝ in 0..1,
          horizontalPhase J x * spatialThresholdKernel z (laplacePoint (l + 1) x)) := by
  simpa only [UpperWeightedCoherence.weightedThresholdEvaluation,
    ContinuousLinearMap.comp_apply, ContinuousMap.evalCLM_apply,
    laplaceHeight_cpow_neg_half, smul_eq_mul, spatialThresholdKernel,
    UpperWeightedCoherence.weightedThresholdValue] using
      map_spatialSourceFourierHeightInput
        (UpperWeightedCoherence.weightedThresholdEvaluation (1 / 4) (by norm_num) z)
        (1 / 2) (by norm_num) J l

end GapFamily.Analytic.SpatialPoint
