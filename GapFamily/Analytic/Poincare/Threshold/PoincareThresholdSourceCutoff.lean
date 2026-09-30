import GapFamily.Analytic.Modular.Geometry.ModularTruncatedCutoff
import GapFamily.Analytic.Modular.Elliptic.ModularEllipticChart

/-!
# Compact smooth inverse-height localization

The literal inverse square of height is localized by an actual smooth compact
upper-half-plane cutoff. The multiplier is globally smooth because it is locally
zero outside the cutoff support. Centered chart pullbacks remain smooth and compact.
-/

noncomputable section
namespace GapFamily.Analytic.PoincareThresholdSourceCutoff

open Set Filter UpperHalfPlane
open scoped ContDiff Topology

def inverseHeightCutoff (χ : ℂ → ℝ) (z : ℂ) : ℝ :=
  χ z / z.im ^ 2

/-- The cutoff removes the real-axis singularity in an actual neighborhood. -/
theorem contDiff_inverseHeightCutoff {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet) : ContDiff ℝ ∞ (inverseHeightCutoff χ) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ upperHalfPlaneSet
  · exact hχ.contDiffAt.div (Complex.imCLM.contDiff.contDiffAt.pow 2)
      (pow_ne_zero 2 (ne_of_gt hz))
  · have hzχ : z ∉ tsupport χ := fun h => hz (hs h)
    have hzero : inverseHeightCutoff χ =ᶠ[𝓝 z] (fun _ => 0) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hzχ] with w hw
      simp only [inverseHeightCutoff, hw, zero_div, Pi.zero_apply]
    exact contDiffAt_const.congr_of_eventuallyEq hzero

theorem hasCompactSupport_inverseHeightCutoff {χ : ℂ → ℝ}
    (hc : HasCompactSupport χ) : HasCompactSupport (inverseHeightCutoff χ) := by
  unfold inverseHeightCutoff
  simp_rw [div_eq_mul_inv]
  exact hc.mul_right

theorem tsupport_inverseHeightCutoff_subset {χ : ℂ → ℝ} :
    tsupport (inverseHeightCutoff χ) ⊆ tsupport χ := by
  unfold inverseHeightCutoff
  simp_rw [div_eq_mul_inv]
  exact tsupport_mul_subset_left

@[simp] theorem inverseHeightCutoff_eq_of_eq_one {χ : ℂ → ℝ} {z : ℂ}
    (hz : χ z = 1) : inverseHeightCutoff χ z = 1 / z.im ^ 2 := by
  simp only [inverseHeightCutoff, hz]

theorem inverseHeightCutoff_eqOn {χ : ℂ → ℝ} {K : Set ℂ}
    (hχK : EqOn χ 1 K) : EqOn (inverseHeightCutoff χ) (fun z => 1 / z.im ^ 2) K :=
  fun _ hz => inverseHeightCutoff_eq_of_eq_one (hχK hz)

/-- The genuine chart multiplier has the global smoothness needed by H1 multiplication. -/
theorem contDiff_inverseHeightCutoff_chart {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet) (center : ℂ) :
    ContDiff ℝ ∞ (fun v => inverseHeightCutoff χ (ellipticChart center v)) :=
  (contDiff_inverseHeightCutoff hχ hs).comp (ellipticChart_contDiff center)

theorem hasCompactSupport_inverseHeightCutoff_chart {χ : ℂ → ℝ}
    (hc : HasCompactSupport χ) (center : ℂ) :
    HasCompactSupport (fun v => inverseHeightCutoff χ (ellipticChart center v)) :=
  (hasCompactSupport_inverseHeightCutoff hc).comp_homeomorph (ellipticChart center)

/-- An actual multiplier exists for every compact upper-half-plane set. -/
theorem exists_inverseHeightCutoff {K : Set ℂ} (hK : IsCompact K)
    (hKU : K ⊆ upperHalfPlaneSet) :
    ∃ m : ℂ → ℝ, ContDiff ℝ ∞ m ∧ HasCompactSupport m ∧
      tsupport m ⊆ upperHalfPlaneSet ∧ EqOn m (fun z => 1 / z.im ^ 2) K := by
  obtain ⟨χ, hχ, hc, hs, hχK⟩ := ModularGradient.exists_upperCutoff_eq_one hK hKU
  let φ : ℂ → ℝ := fun z => (χ z).re
  have hφ : ContDiff ℝ ∞ φ := Complex.reCLM.contDiff.comp hχ
  have hcφ : HasCompactSupport φ := hc.comp_left (map_zero Complex.reCLM)
  have hsφ : tsupport φ ⊆ upperHalfPlaneSet :=
    (tsupport_comp_subset (map_zero Complex.reCLM) χ).trans hs
  refine ⟨inverseHeightCutoff φ, contDiff_inverseHeightCutoff hφ hsφ,
    hasCompactSupport_inverseHeightCutoff hcφ,
    tsupport_inverseHeightCutoff_subset.trans hsφ, ?_⟩
  apply inverseHeightCutoff_eqOn
  intro z hz
  change (χ z).re = 1
  rw [hχK hz]
  rfl

/-- The chosen compact localization works in every centered real coordinate chart. -/
theorem exists_inverseHeightCutoff_chart {K : Set ℂ} (hK : IsCompact K)
    (hKU : K ⊆ upperHalfPlaneSet) (center : ℂ) :
    ∃ m : ℂ → ℝ, ContDiff ℝ ∞ m ∧ HasCompactSupport m ∧
      tsupport m ⊆ upperHalfPlaneSet ∧ EqOn m (fun z => 1 / z.im ^ 2) K ∧
      ContDiff ℝ ∞ (fun v => m (ellipticChart center v)) ∧
      HasCompactSupport (fun v => m (ellipticChart center v)) := by
  obtain ⟨m, hm, hc, hs, he⟩ := exists_inverseHeightCutoff hK hKU
  exact ⟨m, hm, hc, hs, he, hm.comp (ellipticChart_contDiff center),
    hc.comp_homeomorph (ellipticChart center)⟩

end GapFamily.Analytic.PoincareThresholdSourceCutoff
