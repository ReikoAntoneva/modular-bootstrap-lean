import GapFamily.Analytic.Modular.ModularLaplacianDistribution
import GapFamily.Analytic.Elliptic.WeakLaplacianMollifier
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The actual modular weak equation after normalized local mollification

Every vector in the constructed modular Laplacian domain yields genuinely smooth
local mollifications satisfying the Euclidean equation with the mollified actual
source. This is a first elliptic-regularity step, not a smoothness assertion for
an arbitrary operator-domain vector.
-/

noncomputable section

namespace GapFamily.Analytic.ModularGradient

open Set MeasureTheory Filter Metric
open scoped ContDiff Convolution Topology

/-- The compact localization of the actual operator-domain coordinate value. -/
def ellipticLocalValue (u : laplacian.domain) (x : ℂ) (r : ℝ) : ℂ → ℂ :=
  (closedBall x (3 * r)).indicator
    (fun z => coordinateValue ⟨u, laplacian_domain_le u.property⟩ z)

/-- The compact localization of the actual Euclidean source (Au)/y². -/
def ellipticLocalSource (u : laplacian.domain) (x : ℂ) (r : ℝ) : ℂ → ℂ :=
  (closedBall x (3 * r)).indicator (coordinateSource u)

/-- The actual normalized local value convolution. -/
def ellipticValueMollifier (u : laplacian.domain) (x : ℂ) (r : ℝ)
    (φ : ContDiffBump (0 : ℂ)) : ℂ → ℂ :=
  kernelConvolution (φ.normed volume) (ellipticLocalValue u x r)

/-- The actual normalized local source convolution. -/
def ellipticSourceMollifier (u : laplacian.domain) (x : ℂ) (r : ℝ)
    (φ : ContDiffBump (0 : ℂ)) : ℂ → ℂ :=
  kernelConvolution (φ.normed volume) (ellipticLocalSource u x r)

theorem ellipticLocalValue_integrable (u : laplacian.domain) (x : ℂ) {r : ℝ}
    (hK : closedBall x (3 * r) ⊆ modularInterior) :
    Integrable (ellipticLocalValue u x r) volume :=
  (integrable_indicator_iff measurableSet_closedBall).mpr
    ((coordinateValue_locallyIntegrableOn ⟨u, laplacian_domain_le u.property⟩).integrableOn_compact_subset
      hK (isCompact_closedBall _ _))

theorem ellipticLocalSource_integrable (u : laplacian.domain) (x : ℂ) {r : ℝ}
    (hK : closedBall x (3 * r) ⊆ modularInterior) :
    Integrable (ellipticLocalSource u x r) volume :=
  (integrable_indicator_iff measurableSet_closedBall).mpr
    ((coordinateSource_locallyIntegrableOn u).integrableOn_compact_subset hK
      (isCompact_closedBall _ _))

/-- Both mollified sides are globally smooth ordinary convolutions, and on the
inner ball they satisfy the pointwise equation Δuε = -hε with exact normalization. -/
theorem laplacian_mollified_weak_equation (u : laplacian.domain)
    (x : ℂ) {r : ℝ} (hr : 0 < r) (hK : closedBall x (3 * r) ⊆ modularInterior)
    (φ : ContDiffBump (0 : ℂ)) (hφ : φ.rOut < r) :
    (∫ t : ℂ, φ.normed volume t) = 1 ∧
    ContDiff ℝ ∞ (ellipticValueMollifier u x r φ) ∧
    ContDiff ℝ ∞ (ellipticSourceMollifier u x r φ) ∧
    ∀ y ∈ ball x r,
      Integrable (fun t => φ.normed volume (y - t) • ellipticLocalValue u x r t) volume ∧
      Integrable (fun t => φ.normed volume (y - t) • ellipticLocalSource u x r t) volume ∧
      euclideanLaplacian (ellipticValueMollifier u x r φ) y =
        -ellipticSourceMollifier u x r φ y := by
  refine ⟨φ.integral_normed, ?_⟩
  exact normed_kernelConvolution_laplacian_on_ball isOpen_modularInterior
    (coordinateValue_locallyIntegrableOn ⟨u, laplacian_domain_le u.property⟩)
    (coordinateSource_locallyIntegrableOn u)
    (fun ψ hψ hc hs => by
      simpa only [Complex.real_smul] using laplacian_weak_identity u ψ hψ hc hs)
    x hr hK φ hφ

/-- These normalized mollifications approximate the actual coordinate representative
almost everywhere on the chart; no smooth representative is assumed. -/
theorem ellipticValueMollifier_ae_tendsto (u : laplacian.domain)
    (x : ℂ) {r : ℝ} (hr : 0 < r) (hK : closedBall x (3 * r) ⊆ modularInterior)
    {φ : ℕ → ContDiffBump (0 : ℂ)}
    (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0))
    (hφRatio : ∀ᶠ n in atTop, (φ n).rOut ≤ 2 * (φ n).rIn) :
    ∀ᵐ y ∂volume.restrict (ball x r),
      Tendsto (fun n => ellipticValueMollifier u x r (φ n) y) atTop
        (𝓝 (coordinateValue ⟨u, laplacian_domain_le u.property⟩ y)) := by
  have h := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable hφ hφRatio
    (ellipticLocalValue_integrable u x hK).locallyIntegrable
  filter_upwards [ae_restrict_of_ae h (s := ball x r), ae_restrict_mem measurableSet_ball]
    with y hy hyB
  have hyK : y ∈ closedBall x (3 * r) := by
    change dist y x ≤ 3 * r
    have hy' : dist y x < r := hyB
    linarith
  simpa only [ellipticValueMollifier, kernelConvolution, convolution_flip,
    ellipticLocalValue, indicator_of_mem hyK] using hy

/-- The same ordinary approximation holds for the actual divided operator source. -/
theorem ellipticSourceMollifier_ae_tendsto (u : laplacian.domain)
    (x : ℂ) {r : ℝ} (hr : 0 < r) (hK : closedBall x (3 * r) ⊆ modularInterior)
    {φ : ℕ → ContDiffBump (0 : ℂ)}
    (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0))
    (hφRatio : ∀ᶠ n in atTop, (φ n).rOut ≤ 2 * (φ n).rIn) :
    ∀ᵐ y ∂volume.restrict (ball x r),
      Tendsto (fun n => ellipticSourceMollifier u x r (φ n) y) atTop
        (𝓝 (coordinateSource u y)) := by
  have h := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable hφ hφRatio
    (ellipticLocalSource_integrable u x hK).locallyIntegrable
  filter_upwards [ae_restrict_of_ae h (s := ball x r), ae_restrict_mem measurableSet_ball]
    with y hy hyB
  have hyK : y ∈ closedBall x (3 * r) := by
    change dist y x ≤ 3 * r
    have hy' : dist y x < r := hyB
    linarith
  simpa only [ellipticSourceMollifier, kernelConvolution, convolution_flip,
    ellipticLocalSource, indicator_of_mem hyK] using hy

/-- Every actual interior point has a compact chart with the margin required by mollification. -/
theorem exists_elliptic_chart_radius {x : ℂ} (hx : x ∈ modularInterior) :
    ∃ r : ℝ, 0 < r ∧ closedBall x (3 * r) ⊆ modularInterior := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_modularInterior x hx
  refine ⟨ε / 4, by positivity, ?_⟩
  intro y hy
  apply hball
  change dist y x < ε
  have hy' : dist y x ≤ 3 * (ε / 4) := hy
  linarith

/-- A concrete normalized bump sequence whose supports shrink strictly inside the chart. -/
def ellipticShrinkingBump (r : ℝ) (hr : 0 < r) (n : ℕ) : ContDiffBump (0 : ℂ) where
  rIn := (r / ((n : ℝ) + 2)) / 2
  rOut := r / ((n : ℝ) + 2)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have h : 0 < r / ((n : ℝ) + 2) := by positivity
    linarith

theorem ellipticShrinkingBump_rOut_lt (r : ℝ) (hr : 0 < r) (n : ℕ) :
    (ellipticShrinkingBump r hr n).rOut < r := by
  change r / ((n : ℝ) + 2) < r
  rw [div_lt_iff₀ (by positivity : 0 < (n : ℝ) + 2)]
  have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
  nlinarith

theorem ellipticShrinkingBump_ratio (r : ℝ) (hr : 0 < r) (n : ℕ) :
    (ellipticShrinkingBump r hr n).rOut ≤ 2 * (ellipticShrinkingBump r hr n).rIn := by
  dsimp [ellipticShrinkingBump]
  linarith

theorem ellipticShrinkingBump_tendsto (r : ℝ) (hr : 0 < r) :
    Tendsto (fun n : ℕ => (ellipticShrinkingBump r hr n).rOut) atTop (𝓝 0) := by
  simpa [ellipticShrinkingBump, Nat.cast_add] using
    (tendsto_add_atTop_iff_nat 2).2 (tendsto_const_div_atTop_nhds_zero_nat r)

/-- Concrete smooth ordinary solutions approximate both sides of the actual weak equation
on a neighborhood of every interior point. No analytic regularity of the original vector
or prescribed approximating sequence is assumed. -/
theorem exists_laplacian_smooth_local_approximation (u : laplacian.domain)
    {x : ℂ} (hx : x ∈ modularInterior) :
    ∃ r : ℝ, 0 < r ∧ ∃ f h : ℕ → ℂ → ℂ,
      (∀ n, ContDiff ℝ ∞ (f n) ∧ ContDiff ℝ ∞ (h n) ∧
        ∀ y ∈ ball x r, euclideanLaplacian (f n) y = -h n y) ∧
      (∀ᵐ y ∂volume.restrict (ball x r), Tendsto (fun n => f n y) atTop
        (𝓝 (coordinateValue ⟨u, laplacian_domain_le u.property⟩ y))) ∧
      (∀ᵐ y ∂volume.restrict (ball x r), Tendsto (fun n => h n y) atTop
        (𝓝 (coordinateSource u y))) := by
  obtain ⟨r, hr, hK⟩ := exists_elliptic_chart_radius hx
  let φ := ellipticShrinkingBump r hr
  refine ⟨r, hr, fun n => ellipticValueMollifier u x r (φ n),
    fun n => ellipticSourceMollifier u x r (φ n), ?_, ?_, ?_⟩
  · intro n
    obtain ⟨_, hf, hh, heq⟩ := laplacian_mollified_weak_equation u x hr hK (φ n)
      (ellipticShrinkingBump_rOut_lt r hr n)
    exact ⟨hf, hh, fun y hy => (heq y hy).2.2⟩
  · exact ellipticValueMollifier_ae_tendsto u x hr hK (ellipticShrinkingBump_tendsto r hr)
      (Eventually.of_forall (ellipticShrinkingBump_ratio r hr))
  · exact ellipticSourceMollifier_ae_tendsto u x hr hK (ellipticShrinkingBump_tendsto r hr)
      (Eventually.of_forall (ellipticShrinkingBump_ratio r hr))

end GapFamily.Analytic.ModularGradient
