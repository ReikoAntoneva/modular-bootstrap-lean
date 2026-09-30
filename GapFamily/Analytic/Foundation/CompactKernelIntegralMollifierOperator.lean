import GapFamily.Analytic.Foundation.CompactKernelIntegral
import GapFamily.Analytic.Foundation.CompactKernelIntegralMollifier
import GapFamily.Analytic.Elliptic.LocalSobolevCompactRestriction

/-!
# Compactness of the actual localized mollifier operator

The source stays in the ambient complex plane with Lebesgue measure restricted
to its compact support. The target is a compact subset with its actual induced
topology and any finite Borel measure, in particular restricted Lebesgue measure.
-/

noncomputable section

open MeasureTheory Set
open scoped BoundedContinuousFunction

namespace GapFamily.Analytic

private theorem finiteMeasure_restrict_compact (K : Set ℂ) (hK : IsCompact K) :
    IsFiniteMeasure (volume.restrict K) :=
  ⟨by simpa using hK.measure_lt_top (μ := volume)⟩

/-- The actual normalized convolution kernel, from ambient supported `L²` to continuous output. -/
def normedMollifierIntegralOperator (ρ : ContDiffBump (0 : ℂ)) (K : Set ℂ)
    (hK : IsCompact K) (T : Set ℂ) [CompactSpace T] :
    Lp ℂ 2 (volume.restrict K) →L[ℂ] C(T, ℂ) :=
  letI := finiteMeasure_restrict_compact K hK
  boundedKernelIntegralOperator (volume.restrict K) (normedMollifierKernelFamily ρ T)

/-- Its defining ordinary integral is genuinely integrable. -/
theorem normedMollifierIntegral_integrable (ρ : ContDiffBump (0 : ℂ))
    (K : Set ℂ) (hK : IsCompact K) (T : Set ℂ) [CompactSpace T]
    (f : Lp ℂ 2 (volume.restrict K)) (z : T) :
    Integrable (fun w : ℂ => ρ.normed volume ((z : ℂ) - w) • f w) (volume.restrict K) := by
  have := finiteMeasure_restrict_compact K hK
  simpa only [normedMollifierKernelFamily_apply, Complex.real_smul] using
    boundedKernelIntegral_integrable (volume.restrict K) (normedMollifierKernelFamily ρ T) f z

/-- Exact identification with the ordinary restricted convolution integral. -/
theorem normedMollifierIntegralOperator_apply (ρ : ContDiffBump (0 : ℂ))
    (K : Set ℂ) (hK : IsCompact K) (T : Set ℂ) [CompactSpace T]
    (f : Lp ℂ 2 (volume.restrict K)) (z : T) :
    normedMollifierIntegralOperator ρ K hK T f z =
      ∫ w in K, ρ.normed volume ((z : ℂ) - w) • f w := by
  have := finiteMeasure_restrict_compact K hK
  simpa only [normedMollifierIntegralOperator, normedMollifierKernelFamily_apply,
    Complex.real_smul] using
    boundedKernelIntegralOperator_apply (volume.restrict K) (normedMollifierKernelFamily ρ T) f z

/-- Compactness of the actual fixed mollifier is derived, not assumed. -/
theorem isCompactOperator_normedMollifierIntegralOperator
    (ρ : ContDiffBump (0 : ℂ)) (K : Set ℂ) (hK : IsCompact K)
    (T : Set ℂ) [CompactSpace T] :
    IsCompactOperator (normedMollifierIntegralOperator ρ K hK T) := by
  have := finiteMeasure_restrict_compact K hK
  exact isCompactOperator_boundedKernelIntegralOperator
    (volume.restrict K) (normedMollifierKernelFamily ρ T)

/-- The same mollifier is compact into the target `L²` space. -/
def normedMollifierIntegralL2Operator (ρ : ContDiffBump (0 : ℂ)) (K : Set ℂ)
    (hK : IsCompact K) (T : Set ℂ) [CompactSpace T]
    (ν : Measure T) [IsFiniteMeasure ν] :
    Lp ℂ 2 (volume.restrict K) →L[ℂ] Lp ℂ 2 ν :=
  (ContinuousMap.toLp 2 ν ℂ).comp (normedMollifierIntegralOperator ρ K hK T)

theorem isCompactOperator_normedMollifierIntegralL2Operator
    (ρ : ContDiffBump (0 : ℂ)) (K : Set ℂ) (hK : IsCompact K)
    (T : Set ℂ) [CompactSpace T] (ν : Measure T) [IsFiniteMeasure ν] :
    IsCompactOperator (normedMollifierIntegralL2Operator ρ K hK T ν) :=
  (isCompactOperator_normedMollifierIntegralOperator ρ K hK T).clm_comp
    (ContinuousMap.toLp 2 ν ℂ)

theorem normedMollifierIntegralL2Operator_coeFn
    (ρ : ContDiffBump (0 : ℂ)) (K : Set ℂ) (hK : IsCompact K)
    (T : Set ℂ) [CompactSpace T] (ν : Measure T) [IsFiniteMeasure ν]
    (f : Lp ℂ 2 (volume.restrict K)) :
    ⇑(normedMollifierIntegralL2Operator ρ K hK T ν f) =ᵐ[ν]
      (fun z : T => ∫ w in K, ρ.normed volume ((z : ℂ) - w) • f w) := by
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (μ := ν) (𝕜 := ℂ)
    (normedMollifierIntegralOperator ρ K hK T f)] with z hz
  exact hz.trans (normedMollifierIntegralOperator_apply ρ K hK T f z)

/-- For an actual supported input function, the compact operator is literally
the already defined ordinary mollification at every target point. -/
theorem normedMollifierIntegralOperator_toLp
    (ρ : ContDiffBump (0 : ℂ)) (K : Set ℂ) (hK : IsCompact K)
    (T : Set ℂ) [CompactSpace T] (f : ℂ → ℂ)
    (hf : MemLp f 2 (volume.restrict K)) (hs : Function.support f ⊆ K) (z : T) :
    normedMollifierIntegralOperator ρ K hK T (hf.toLp f) z =
      LocalSobolev.mollify ρ f z := by
  rw [normedMollifierIntegralOperator_apply, LocalSobolev.mollify_eq_setIntegral ρ f hs]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with w hw
  rw [hw]

/-- The compact approximation map agrees exactly with the restricted mollifier
class used by the quantitative local Sobolev approximation estimate. -/
theorem normedMollifierIntegralL2Operator_toLp
    (ρ : ContDiffBump (0 : ℂ)) (K : Set ℂ) (hK : IsCompact K)
    (T : Set ℂ) [CompactSpace T] (f : ℂ → ℂ) (hc : Continuous f)
    (hf : MemLp f 2 (volume.restrict K)) (hs : Function.support f ⊆ K) :
    normedMollifierIntegralL2Operator ρ K hK T (LocalSobolev.restrictedVolume T)
        (hf.toLp f) =
      LocalSobolev.restrictedLp T (LocalSobolev.mollify ρ f)
        (LocalSobolev.continuous_mollify ρ f hc) := by
  apply congrArg (ContinuousMap.toLp 2 (LocalSobolev.restrictedVolume T) ℂ)
  ext z
  exact normedMollifierIntegralOperator_toLp ρ K hK T f hf hs z

end GapFamily.Analytic
