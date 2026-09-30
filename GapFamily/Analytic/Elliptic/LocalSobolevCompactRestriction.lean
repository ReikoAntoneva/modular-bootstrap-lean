import GapFamily.Analytic.Elliptic.LocalSobolevCompactMollifier
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# The actual restricted L² mollifier error

The target measure is the literal Lebesgue measure pulled back to a compact
subtype. Ordinary restricted integrals and L² norms are identified exactly.
-/

noncomputable section

namespace GapFamily.Analytic.LocalSobolev

open Set MeasureTheory ContinuousLinearMap
open scoped ContDiff Convolution

/-- Literal Lebesgue measure on a subset, with no normalization. -/
def restrictedVolume (K : Set ℂ) : Measure K :=
  volume.comap (Subtype.val : K → ℂ)

instance restrictedVolume_finite (K : Set ℂ) [CompactSpace K] :
    IsFiniteMeasure (restrictedVolume K) where
  measure_univ_lt_top := by
    have hK : IsCompact K := isCompact_iff_compactSpace.mpr inferInstance
    rw [restrictedVolume, (MeasurableEmbedding.subtype_coe hK.measurableSet).comap_apply]
    simpa using (hK.measure_lt_top (μ := volume))

/-- A continuous function restricted to the actual compact target. -/
def restrictedContinuous (K : Set ℂ) (f : ℂ → ℂ) (hf : Continuous f) : C(K, ℂ) :=
  ⟨fun z => f z, hf.comp continuous_subtype_val⟩

/-- Its actual class in L² of the compact target with unnormalized Lebesgue measure. -/
def restrictedLp (K : Set ℂ) [CompactSpace K] (f : ℂ → ℂ) (hf : Continuous f) :
    Lp ℂ 2 (restrictedVolume K) :=
  ContinuousMap.toLp 2 (restrictedVolume K) ℂ (restrictedContinuous K f hf)

theorem restrictedLp_ae (K : Set ℂ) [CompactSpace K] (f : ℂ → ℂ) (hf : Continuous f) :
    restrictedLp K f hf =ᵐ[restrictedVolume K] fun z : K => f z :=
  ContinuousMap.coeFn_toLp _ _

theorem restrictedLp_norm_sq (K : Set ℂ) [CompactSpace K] (f : ℂ → ℂ)
    (hf : Continuous f) :
    ‖restrictedLp K f hf‖ ^ 2 = ∫ z in K, ‖f z‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  calc
    _ = ∫ z : K, ‖f z‖ ^ 2 ∂restrictedVolume K := by
      apply integral_congr_ae
      filter_upwards [restrictedLp_ae K f hf] with z hz
      simp only [hz, real_inner_self_eq_norm_sq]
    _ = _ := by
      simpa only [restrictedVolume] using integral_subtype_comap (μ := volume)
        (isCompact_iff_compactSpace.mpr (inferInstance : CompactSpace K)).measurableSet
        (fun z : ℂ => ‖f z‖ ^ 2)

theorem restrictedLp_sub (K : Set ℂ) [CompactSpace K] (f g : ℂ → ℂ)
    (hf : Continuous f) (hg : Continuous g) :
    restrictedLp K f hf - restrictedLp K g hg =
      restrictedLp K (fun z => f z - g z) (hf.sub hg) := by
  exact (ContinuousMap.toLp 2 (restrictedVolume K) ℂ).map_sub
    (restrictedContinuous K f hf) (restrictedContinuous K g hg) |>.symm

theorem continuous_mollify (ρ : ContDiffBump (0 : ℂ)) (f : ℂ → ℂ)
    (hf : Continuous f) : Continuous (mollify ρ f) :=
  ρ.hasCompactSupport_normed.continuous_convolution_left (lsmul ℝ ℝ)
    ρ.continuous_normed hf.locallyIntegrable

/-- The source restriction of the actual convolution is the literal continuous-kernel integral. -/
theorem mollify_eq_setIntegral (ρ : ContDiffBump (0 : ℂ)) (f : ℂ → ℂ)
    {K : Set ℂ} (hs : Function.support f ⊆ K) (z : ℂ) :
    mollify ρ f z = ∫ w in K, ρ.normed volume (z - w) • f w := by
  rw [mollify, convolution_lsmul_swap]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro w hw
  have hz : f w = 0 := by
    by_contra hn
    exact hw (hs hn)
  simp [hz]

/-- Actual L² approximation on any compact target, with the same global derivative-energy bound. -/
theorem restrictedLp_mollify_error_sq_le (K : Set ℂ) [CompactSpace K]
    (ρ : ContDiffBump (0 : ℂ)) (f : ℂ → ℂ)
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    ‖restrictedLp K (mollify ρ f) (continuous_mollify ρ f hf.continuous) -
        restrictedLp K f hf.continuous‖ ^ 2 ≤
      ρ.rOut ^ 2 * ∫ z : ℂ, ‖fderiv ℝ f z‖ ^ 2 := by
  rw [restrictedLp_sub, restrictedLp_norm_sq]
  exact (integral_mono_measure Measure.restrict_le_self
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)
    (integrable_mollify_error_sq ρ f hf hc)).trans
      (integral_mollify_error_sq_le ρ f hf hc)

end GapFamily.Analytic.LocalSobolev
