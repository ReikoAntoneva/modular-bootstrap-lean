import GapFamily.Analytic.Cusp.Profile.CuspUnboundedFourierProfileSmooth
import GapFamily.Analytic.Cusp.Fourier.CuspFourierCutoffProfile
import GapFamily.Analytic.Cusp.CuspPoincareDirectRemnant

/-!
The actual noncompact high-cusp Fourier lift, constructed by normalized full
modular periodization. No Hilbert-space membership is asserted.
-/

noncomputable section
namespace GapFamily.Analytic.PoincareHighCusp
open Set Filter UpperHalfPlane ModularGroup CuspFourierCutoff CuspFourierUnbounded
open scoped Topology ContDiff MatrixGroups

/-- The literal growing vertical profile with the existing high-cusp cutoff. -/
def highProfile (s : ℂ) (y : ℝ) : ℂ := (cutoff y : ℂ) * (y : ℂ) ^ s

theorem highProfile_eq_zero (s : ℂ) {y : ℝ} (hy : y ≤ 2) : highProfile s y = 0 := by
  simp only [highProfile, cutoff_eq_zero hy, Complex.ofReal_zero, zero_mul]

theorem tsupport_highProfile (s : ℂ) : tsupport (highProfile s) ⊆ Ici (2 : ℝ) := by
  apply closure_minimal _ isClosed_Ici
  intro y hy
  by_contra hn
  exact hy (highProfile_eq_zero s (le_of_lt (lt_of_not_ge hn)))

theorem tsupport_highProfile_upper (s : ℂ) : tsupport (highProfile s) ⊆ Ioi (1 : ℝ) := by
  intro y hy
  have h := tsupport_highProfile s hy
  change 1 < y
  have : 2 ≤ y := h
  linarith

theorem contDiff_highProfile (s : ℂ) : ContDiff ℝ ∞ (highProfile s) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : 0 < y
  · exact (Complex.ofRealCLM.contDiff.contDiffAt.comp y contDiff_cutoff.contDiffAt).mul
      (contDiffAt_ofReal_cpow s hy)
  · have hn : y ∉ tsupport (highProfile s) := by
      intro h
      have h2 : 2 ≤ y := tsupport_highProfile s h
      linarith
    exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hn)

/-- The actual full-SL₂ periodization keeps its established factor one half. -/
def highCuspLift (J : ℤ) (s : ℂ) : ℂ → ℂ :=
  modularPeriodization (cuspFourierProfileSeed J (highProfile s))

theorem contDiffOn_highCuspLift (J : ℤ) (s : ℂ) :
    ContDiffOn ℝ ∞ (highCuspLift J s) upperHalfPlaneSet :=
  contDiffOn_modularPeriodization_cuspFourierProfileSeed J
    (contDiff_highProfile s) (tsupport_highProfile_upper s)

theorem highCuspLift_smul (J : ℤ) (s : ℂ) (τ : UpperHalfPlane) (γ : SL(2, ℤ)) :
    highCuspLift J s (γ • τ : UpperHalfPlane) = highCuspLift J s τ :=
  modularPeriodization_invariant _ γ τ

/-- The constructed lift equals the intended cutoff seed on the entire closed domain. -/
theorem highCuspLift_eq_on_fd (J : ℤ) (s : ℂ) {τ : UpperHalfPlane}
    (hτ : τ ∈ ModularGroup.fd) :
    highCuspLift J s τ = (cutoff τ.im : ℂ) * complexPointSeed 0 J s τ := by
  rw [highCuspLift, modularPeriodization_cuspFourierProfileSeed_eq_on_fd J
    (tsupport_highProfile_upper s) hτ, complexPointSeed_zero_eq_cuspFourierMode]
  simp only [highProfile, mul_assoc]

/-- The exact cutoff seed formula holds on the open height-half strip as well. -/
theorem highCuspLift_eq_of_half_lt_im (J : ℤ) (s : ℂ) {τ : UpperHalfPlane}
    (hτ : 1 / 2 < τ.im) :
    highCuspLift J s τ = (cutoff τ.im : ℂ) * complexPointSeed 0 J s τ := by
  let k : ℤ := -⌊τ.re + 1 / 2⌋
  let σ : UpperHalfPlane := T ^ k • τ
  have him : σ.im = τ.im := im_T_zpow_smul τ k
  have hre : σ.re ∈ Icc (-1 / 2 : ℝ) (1 / 2) := by
    have hfloor := Int.floor_le (τ.re + 1 / 2)
    have hlt := Int.lt_floor_add_one (τ.re + 1 / 2)
    change (T ^ k • τ).re ∈ Icc (-1 / 2 : ℝ) (1 / 2)
    rw [re_T_zpow_smul]
    dsimp [k]
    push_cast
    constructor <;> linarith
  have hz : ∀ γ : SL(2, ℤ), γ 1 0 ≠ 0 → highProfile s (γ • σ).im = 0 := by
    intro γ hγ
    apply highProfile_eq_zero s
    apply (modular_smul_im_le_inv_of_lowerLeft_ne_zero γ σ hγ).trans
    have hp : 0 < σ.im := σ.im_pos
    apply (div_le_iff₀ hp).mpr
    rw [him]
    linarith
  have hlocal := modularPeriodization_cuspFourierProfileSeed_of_zero_nonparabolic
    J (highProfile s) σ hre hz
  have hseed : complexPointSeed 0 J s σ = complexPointSeed 0 J s τ :=
    complexPointSeed_translation 0 J s k τ
  rw [← highCuspLift_smul J s τ (T ^ k)]
  change modularPeriodization (cuspFourierProfileSeed J (highProfile s)) σ = _
  rw [hlocal, highProfile, mul_assoc, ← complexPointSeed_zero_eq_cuspFourierMode, him, hseed]

/-- The required κ-family, with exponent one half plus κ. -/
def continuedHighCusp (J : ℤ) (κ : ℂ) : ℂ → ℂ := highCuspLift J (exponent κ)

theorem contDiffOn_continuedHighCusp (J : ℤ) (κ : ℂ) :
    ContDiffOn ℝ ∞ (continuedHighCusp J κ) upperHalfPlaneSet :=
  contDiffOn_highCuspLift J (exponent κ)

theorem continuedHighCusp_smul (J : ℤ) (κ : ℂ) (τ : UpperHalfPlane) (γ : SL(2, ℤ)) :
    continuedHighCusp J κ (γ • τ : UpperHalfPlane) = continuedHighCusp J κ τ :=
  highCuspLift_smul J (exponent κ) τ γ

theorem continuedHighCusp_eq_on_fd (J : ℤ) (κ : ℂ) {τ : UpperHalfPlane}
    (hτ : τ ∈ ModularGroup.fd) :
    continuedHighCusp J κ τ = (cutoff τ.im : ℂ) * complexPointSeed 0 J (exponent κ) τ :=
  highCuspLift_eq_on_fd J (exponent κ) hτ

theorem continuedHighCusp_eq_of_half_lt_im (J : ℤ) (κ : ℂ) {τ : UpperHalfPlane}
    (hτ : 1 / 2 < τ.im) :
    continuedHighCusp J κ τ = (cutoff τ.im : ℂ) * complexPointSeed 0 J (exponent κ) τ :=
  highCuspLift_eq_of_half_lt_im J (exponent κ) hτ

end GapFamily.Analytic.PoincareHighCusp
