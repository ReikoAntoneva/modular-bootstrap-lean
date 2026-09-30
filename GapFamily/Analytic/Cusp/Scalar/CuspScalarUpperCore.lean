import GapFamily.Analytic.Cusp.Green.CuspGreenSourceLift
import GapFamily.Analytic.Modular.Elliptic.ModularUpperHilbertValue

/-! Literal scalar core values on the full high upper cusp, across every translation seam. -/
noncomputable section
namespace GapFamily.Analytic.CuspScalarUpperCore
open Set Filter MeasureTheory UpperHalfPlane ModularGroup ModularGradient
open scoped MatrixGroups ContDiff

/-- Translation to the centered strip and the actual nonparabolic height bound
identify the periodization everywhere above height one, not only on the FD. -/
theorem modularPeriodization_cuspProfileSeed_eq_high {b : ℝ → ℂ}
    (hs : tsupport b ⊆ Ioi (1 : ℝ)) (τ : UpperHalfPlane) (hτ : 1 < τ.im) :
    modularPeriodization (cuspProfileSeed b) τ = b τ.im := by
  let n : ℤ := -⌊τ.re + 1 / 2⌋
  let σ : UpperHalfPlane := T ^ n • τ
  have him : σ.im = τ.im := im_T_zpow_smul τ n
  have hre : σ.re ∈ Icc (-1 / 2 : ℝ) (1 / 2) := by
    have hlo := Int.floor_le (τ.re + 1 / 2)
    have hhi := Int.lt_floor_add_one (τ.re + 1 / 2)
    change -1 / 2 ≤ (T ^ n • τ).re ∧ (T ^ n • τ).re ≤ 1 / 2
    rw [re_T_zpow_smul]
    dsimp [n]
    push_cast
    constructor <;> linarith
  have hzero (γ : SL(2, ℤ)) (hγ : γ 1 0 ≠ 0) : b (γ • σ).im = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hm
    have hh : 1 < (γ • σ).im := hs hm
    exact (not_lt_of_gt hh) (modular_smul_im_lt_one_of_lowerLeft_ne_zero γ σ hγ
      (by simpa only [him] using hτ))
  calc
    _ = modularPeriodization (cuspProfileSeed b) σ :=
      (modularPeriodization_invariant (cuspProfileSeed b) (T ^ n) τ).symm
    _ = b σ.im := modularPeriodization_cuspProfileSeed_of_zero_nonparabolic b σ hre hzero
    _ = b τ.im := congrArg b him

theorem cuspProfileCore_eq_high (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b)
    (hc : HasCompactSupport b) (hs : tsupport b ⊆ Ioi (1 : ℝ))
    (τ : UpperHalfPlane) (hτ : 1 < τ.im) :
    (cuspProfileCore b hb hc hs).val τ = b τ.im :=
  modularPeriodization_cuspProfileSeed_eq_high hs τ hτ

/-- The actual upper Hilbert lift of the constant is the literal cutoff. -/
theorem upperCutoff_constant_ae
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet) :
    upperCutoffHilbertValueOperator χ hχ hc hs modularConstant =ᵐ[(volume : Measure ℂ)] χ := by
  rw [← value_constantCore_one]
  simpa only [constantCore, mul_one] using
    upperCutoffHilbertValueOperator_value_ae χ hχ hc hs (constantCore 1)

/-- Actual smooth logarithmic sources have their literal lifted upper value on
every high open chart, including side seams and translated strips. -/
theorem upperCutoff_sourceLift_ae_high
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hfs : tsupport f ⊆ Ioi (0 : ℝ)) :
    ∀ᵐ z : ℂ ∂volume, 1 < z.im →
      upperCutoffHilbertValueOperator χ hχ hc hs (cuspGreenSourceLift f hf hfc hfs) z =
        χ z * (Real.sqrt z.im • f (Real.log z.im)) := by
  let b := cuspLift f
  let hb := cuspGreenSourceProfile_contDiff f hf hfc hfs
  let hbc := cuspGreenSourceProfile_hasCompactSupport f hfc
  let hbs := cuspGreenSourceProfile_tsupport_subset f hfc hfs
  filter_upwards [upperCutoffHilbertValueOperator_value_ae χ hχ hc hs
    (cuspProfileCore b hb hbc hbs)] with z hz
  intro hzi
  have hy : 0 < z.im := by linarith
  have he := cuspProfileCore_eq_high b hb hbc hbs (⟨z, hy⟩ : UpperHalfPlane) hzi
  change (cuspProfileCore b hb hbc hbs).val z = b z.im at he
  change upperCutoffHilbertValueOperator χ hχ hc hs (value (cuspProfileCore b hb hbc hbs)) z = _
  rw [hz, he]
  rfl

end GapFamily.Analytic.CuspScalarUpperCore
