import GapFamily.Analytic.Modular.Periodization.ModularPeriodizationUnfold
import GapFamily.Analytic.Modular.Elliptic.ModularInteriorCompactUpperSmooth

/-! Actual value-pairing unfolding for a compact seed crossing modular seams. -/

noncomputable section
namespace GapFamily.Analytic
open Set Filter MeasureTheory UpperHalfPlane ModularGradient
open scoped ContDiff MatrixGroups

/-- The actual smooth modular core obtained from a compact upper-half-plane seed. -/
def periodizedUpperCore (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ upperHalfPlaneSet) : smoothCore :=
  ⟨modularPeriodization ψ, modularPeriodization_mem_smoothCore_of_upper_support hψ hc hs⟩

/-- The compact conjugate product is globally smooth without any smoothness
assumption on the arbitrary off-upper-half-plane values of the core function. -/
theorem contDiff_conjCore_mul_upperSeed (F : smoothCore) {ψ : ℂ → ℂ}
    (hψ : ContDiff ℝ ∞ ψ) (hs : tsupport ψ ⊆ upperHalfPlaneSet) :
    ContDiff ℝ ∞ (fun z => star (F.val z) * ψ z) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ tsupport ψ
  · have hF := F.property.1.contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds (hs hz))
    exact (Complex.conjCLE.contDiff.contDiffAt.comp z hF).mul hψ.contDiffAt
  · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hz] with w hw
    simp [hw]

/-- Automorphy extracts the conjugate core value from the actual orbit sum. -/
theorem modularPeriodization_conjCore_mul (F : smoothCore) (ψ : ℂ → ℂ)
    (τ : UpperHalfPlane) :
    modularPeriodization (fun z => star (F.val z) * ψ z) τ =
      star (F.val τ) * modularPeriodization ψ τ := by
  simp only [modularPeriodization_coe, F.property.2.1]
  rw [tsum_mul_left]
  ring

/-- The unfolded compact product has ordinary hyperbolic integrability. -/
theorem conjCore_mul_upperSeed_integrable (F : smoothCore) {ψ : ℂ → ℂ}
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ upperHalfPlaneSet) :
    Integrable (fun τ : UpperHalfPlane => star (F.val τ) * ψ τ) volume := by
  apply upperSeed_integrable (contDiff_conjCore_mul_upperSeed F hψ hs).continuous
  · exact hc.mul_left
  · exact tsupport_mul_subset_right.trans hs

/-- The modular pairing also has ordinary integrability, with the actual value representatives. -/
theorem conjCore_mul_periodization_integrable (F : smoothCore) {ψ : ℂ → ℂ}
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ upperHalfPlaneSet) :
    Integrable (fun τ : UpperHalfPlane => star (F.val τ) * modularPeriodization ψ τ)
      modularMeasure := by
  have h := L2.integrable_inner (𝕜 := ℂ) (value F) (value (periodizedUpperCore ψ hψ hc hs))
  apply h.congr
  filter_upwards [value_ae F, value_ae (periodizedUpperCore ψ hψ hc hs)] with τ hF hP
  rw [hF, hP]
  simp [RCLike.inner_apply, periodizedUpperCore, mul_comm]

/-- The literal modular integral against the conjugate core unfolds across all seams. -/
theorem integral_conjCore_mul_periodization (F : smoothCore) {ψ : ℂ → ℂ}
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ upperHalfPlaneSet) :
    (∫ τ : UpperHalfPlane, star (F.val τ) * modularPeriodization ψ τ ∂modularMeasure) =
      ∫ τ : UpperHalfPlane, star (F.val τ) * ψ τ ∂volume := by
  have h := integral_modularPeriodization_upper
    (contDiff_conjCore_mul_upperSeed F hψ hs) hc.mul_left (tsupport_mul_subset_right.trans hs)
  simpa only [modularPeriodization_conjCore_mul] using h

/-- The actual Hilbert value pairing has the ordinary unfolded integral, with
conjugation on the requested first argument. -/
theorem inner_value_periodizedUpperCore (F : smoothCore) {ψ : ℂ → ℂ}
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ upperHalfPlaneSet) :
    inner ℂ (value F) (value (periodizedUpperCore ψ hψ hc hs)) =
      ∫ τ : UpperHalfPlane, star (F.val τ) * ψ τ ∂volume := by
  rw [L2.inner_def]
  calc
    _ = ∫ τ : UpperHalfPlane, star (F.val τ) * modularPeriodization ψ τ ∂modularMeasure := by
      apply integral_congr_ae
      filter_upwards [value_ae F, value_ae (periodizedUpperCore ψ hψ hc hs)] with τ hF hP
      rw [hF, hP]
      simp [RCLike.inner_apply, periodizedUpperCore, mul_comm]
    _ = _ := integral_conjCore_mul_periodization F hψ hc hs

/-- Complete ordinary-integral and actual Hilbert-pairing statement for a
compact upper-half-plane test, with no interior-support premise. -/
theorem value_pairing_modularPeriodization_upper (F : smoothCore) {ψ : ℂ → ℂ}
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ upperHalfPlaneSet) :
    Integrable (fun τ : UpperHalfPlane => star (F.val τ) * ψ τ) volume ∧
    Integrable (fun τ : UpperHalfPlane => star (F.val τ) * modularPeriodization ψ τ)
      modularMeasure ∧
    inner ℂ (value F) (value (periodizedUpperCore ψ hψ hc hs)) =
      ∫ τ : UpperHalfPlane, star (F.val τ) * ψ τ ∂volume :=
  ⟨conjCore_mul_upperSeed_integrable F hψ hc hs,
    conjCore_mul_periodization_integrable F hψ hc hs,
    inner_value_periodizedUpperCore F hψ hc hs⟩

end GapFamily.Analytic
