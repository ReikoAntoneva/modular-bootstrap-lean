import GapFamily.Analytic.Modular.Elliptic.ModularInteriorCompactUpperSmooth
import GapFamily.Analytic.Modular.Elliptic.ModularInteriorCompactUpperEnergy
import GapFamily.Analytic.Modular.Elliptic.ModularInteriorCompactCore
import GapFamily.Analytic.Elliptic.LocalSobolevCompactRestriction
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Upper-half-plane cutoff operator on the closed form domain

Ordinary cutoff multiplication on the actual smooth modular core extends to
the completed form domain. Its bound is derived from the actual energy
estimate for compact cutoffs supported in the upper half-plane, including
cutoffs meeting identified modular edges.
-/

noncomputable section

namespace GapFamily.Analytic.ModularGradient

open Set MeasureTheory UpperHalfPlane
open scoped ContDiff

/-- Ordinary multiplication by an upper-half-plane cutoff, restricted to a
compact Euclidean set, on the actual smooth modular core. -/
def upperCutoffCoreMap (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet) (T : Set ℂ) [CompactSpace T] :
    smoothCore →ₗ[ℂ] Lp ℂ 2 (LocalSobolev.restrictedVolume T) where
  toFun F := LocalSobolev.restrictedLp T (fun z => χ z * F.val z)
    (upperCutoff_contDiff hχ hs F).continuous
  map_add' F G := by
    apply Lp.ext
    filter_upwards [LocalSobolev.restrictedLp_ae T _
        (upperCutoff_contDiff hχ hs (F + G)).continuous,
      LocalSobolev.restrictedLp_ae T _ (upperCutoff_contDiff hχ hs F).continuous,
      LocalSobolev.restrictedLp_ae T _ (upperCutoff_contDiff hχ hs G).continuous,
      Lp.coeFn_add
        (LocalSobolev.restrictedLp T _ (upperCutoff_contDiff hχ hs F).continuous)
        (LocalSobolev.restrictedLp T _ (upperCutoff_contDiff hχ hs G).continuous)]
      with z hsum hF hG hadd
    rw [hsum, hadd]
    simp only [Pi.add_apply, hF, hG, Submodule.coe_add, mul_add]
  map_smul' c F := by
    apply Lp.ext
    filter_upwards [LocalSobolev.restrictedLp_ae T _
        (upperCutoff_contDiff hχ hs (c • F)).continuous,
      LocalSobolev.restrictedLp_ae T _ (upperCutoff_contDiff hχ hs F).continuous,
      Lp.coeFn_smul c (LocalSobolev.restrictedLp T _
        (upperCutoff_contDiff hχ hs F).continuous)] with z hsmul hF hcoe
    simp only [RingHom.id_apply]
    rw [hsmul, hcoe]
    simp only [Pi.smul_apply, hF, Submodule.coe_smul, smul_eq_mul]
    ring

theorem upperCutoffCoreMap_ae (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet) (T : Set ℂ) [CompactSpace T]
    (F : smoothCore) :
    upperCutoffCoreMap χ hχ hs T F =ᵐ[LocalSobolev.restrictedVolume T]
      fun z : T => χ z * F.val z :=
  LocalSobolev.restrictedLp_ae T _ (upperCutoff_contDiff hχ hs F).continuous

theorem upperCutoffCoreMap_norm_sq (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet) (T : Set ℂ) [CompactSpace T]
    (F : smoothCore) :
    ‖upperCutoffCoreMap χ hχ hs T F‖ ^ 2 = ∫ z in T, ‖χ z * F.val z‖ ^ 2 :=
  LocalSobolev.restrictedLp_norm_sq T _ (upperCutoff_contDiff hχ hs F).continuous

/-- The upper-half-plane cutoff map is bounded by the actual form norm.
The constant is supplied by the proved mass-plus-energy estimate. -/
theorem exists_upperCutoffCoreMap_bound {χ : ℂ → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ upperHalfPlaneSet)
    (T : Set ℂ) [CompactSpace T] :
    ∃ B : ℝ, 0 < B ∧ ∀ F : smoothCore,
      ‖upperCutoffCoreMap χ hχ hs T F‖ ≤ B * ‖coreForm F‖ := by
  obtain ⟨B, hB, henergy⟩ := exists_upperCutoff_energy_bound hχ hc hs
  refine ⟨B, hB, fun F => ?_⟩
  have hmem : MemLp (fun z => χ z * F.val z) 2 (volume : Measure ℂ) :=
    (upperCutoff_contDiff hχ hs F).continuous.memLp_of_hasCompactSupport
      (cutoff_hasCompactSupport hc F)
  have hint : Integrable (fun z => ‖χ z * F.val z‖ ^ 2) (volume : Measure ℂ) :=
    (memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).mp hmem
  have hsq : ‖upperCutoffCoreMap χ hχ hs T F‖ ^ 2 ≤ (B * ‖coreForm F‖) ^ 2 := by
    calc
      ‖upperCutoffCoreMap χ hχ hs T F‖ ^ 2 = ∫ z in T, ‖χ z * F.val z‖ ^ 2 :=
        upperCutoffCoreMap_norm_sq χ hχ hs T F
      _ ≤ ∫ z : ℂ, ‖χ z * F.val z‖ ^ 2 :=
        integral_mono_measure (Measure.restrict_le_self)
          (Filter.Eventually.of_forall (fun _ => sq_nonneg _)) hint
      _ ≤ B ^ 2 * (‖value F‖ ^ 2 + ‖coreGradient F‖ ^ 2) := (henergy F).1
      _ = (B * ‖coreForm F‖) ^ 2 := by rw [← coreForm_norm_sq F]; ring
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hB.le (norm_nonneg _))).mp hsq

/-- Continuous extension of the genuine upper-half-plane cutoff map to the
actual completed form domain. -/
def upperCutoffOperator (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ upperHalfPlaneSet)
    (T : Set ℂ) [CompactSpace T] :
    FormDomain →L[ℂ] Lp ℂ 2 (LocalSobolev.restrictedVolume T) := by
  have _hbound := exists_upperCutoffCoreMap_bound hχ hc hs T
  exact (upperCutoffCoreMap χ hχ hs T).extendOfNorm coreForm

/-- The completed cutoff agrees with literal multiplication on every actual
smooth modular core function. -/
@[simp] theorem upperCutoffOperator_coreForm (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ upperHalfPlaneSet)
    (T : Set ℂ) [CompactSpace T] (F : smoothCore) :
    upperCutoffOperator χ hχ hc hs T (coreForm F) = upperCutoffCoreMap χ hχ hs T F := by
  obtain ⟨B, _, hB⟩ := exists_upperCutoffCoreMap_bound hχ hc hs T
  exact LinearMap.extendOfNorm_eq coreForm_denseRange ⟨B, hB⟩ F

theorem exists_upperCutoffOperator_bound {χ : ℂ → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ upperHalfPlaneSet)
    (T : Set ℂ) [CompactSpace T] :
    ∃ B : ℝ, 0 < B ∧ ‖upperCutoffOperator χ hχ hc hs T‖ ≤ B := by
  obtain ⟨B, hB, hnorm⟩ := exists_upperCutoffCoreMap_bound hχ hc hs T
  exact ⟨B, hB, LinearMap.opNorm_extendOfNorm_le coreForm_denseRange hB.le hnorm⟩

end GapFamily.Analytic.ModularGradient
