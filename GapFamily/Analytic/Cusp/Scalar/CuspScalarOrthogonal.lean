import GapFamily.Analytic.Cusp.Profile.CuspProfileLaplacian
import GapFamily.Analytic.Cusp.MeanZero.CuspMeanZeroResolvent
import GapFamily.Analytic.Cusp.Fourier.CuspHorizontalProjection
import GapFamily.Analytic.Modular.Geometry.ModularTruncatedIndicator

/-!
# Scalar profiles are mass- and energy-orthogonal to the zero-average cusp form

Literal compact scalar profiles are fixed by the actual horizontal averaging
projection and vanish below the high cusp. This gives their mass orthogonality.
The full modular weak Laplacian identity then gives energy orthogonality without
assuming an unrestricted PDE for constrained solutions.
-/

noncomputable section

namespace GapFamily.Analytic

open Set MeasureTheory UpperHalfPlane ModularGradient
open scoped ContDiff

/-- Actual zero extension and restriction are adjoint for the literal cusp measure. -/
theorem cuspZeroExtend_inner_restrict (H : ℝ) (f : cuspHilbert H) (g : ModularHilbert) :
    inner ℂ (cuspZeroExtend H f) g = inner ℂ f (cuspRestrict H g) := by
  rw [L2.inner_def, L2.inner_def]
  have heq : (fun τ => inner ℂ (cuspZeroExtend H f τ) (g τ)) =ᵐ[modularMeasure]
      {τ : UpperHalfPlane | H < τ.im}.indicator (fun τ => inner ℂ (f τ) (g τ)) := by
    filter_upwards [cuspZeroExtend_ae H f] with τ hτ
    rw [hτ]
    by_cases hh : H < τ.im <;> simp [hh]
  rw [integral_congr_ae heq, integral_indicator (measurableSet_highCusp H)]
  apply integral_congr_ae
  filter_upwards [cuspRestrict_ae H g] with τ hτ
  rw [hτ]

/-- The ordinary horizontal average of the genuine scalar profile is its literal profile. -/
theorem cuspHorizontalAverage_cuspProfileCore (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b)
    (hc : HasCompactSupport b) (hs : tsupport b ⊆ Ioi (1 : ℝ)) {y : ℝ} (hy : 1 < y) :
    cuspHorizontalAverage (cuspProfileCore b hb hc hs).val y = b y := by
  rw [cuspHorizontalAverage_eq_setIntegral]
  have hrow : (∫ x in Ioo (-1/2 : ℝ) (1/2),
      (cuspProfileCore b hb hc hs).val (Complex.mk x y)) =
      ∫ _x in Ioo (-1/2 : ℝ) (1/2), b y := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro x hx
    dsimp only
    let τ : UpperHalfPlane := ⟨Complex.mk x y, zero_lt_one.trans hy⟩
    have hfd : τ ∈ ModularGroup.fd := by
      constructor
      · change 1 ≤ Complex.normSq (Complex.mk x y)
        simp only [Complex.normSq_apply]
        nlinarith [sq_nonneg x]
      · change |x| ≤ 1/2
        apply abs_le.mpr
        exact ⟨by linarith [hx.1], hx.2.le⟩
    exact cuspProfileCore_eq_on_fd b hb hc hs (τ := τ) hfd
  rw [hrow, integral_const]
  norm_num [Measure.real, Real.volume_Ioo]

/-- The actual extended averaging operator fixes the restricted scalar profile. -/
theorem cuspAverage_cuspProfileCore (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b)
    (hc : HasCompactSupport b) (hs : tsupport b ⊆ Ioi (1 : ℝ)) :
    cuspAverage 1 le_rfl (cuspRestrict 1 (value (cuspProfileCore b hb hc hs))) =
      cuspRestrict 1 (value (cuspProfileCore b hb hc hs)) := by
  apply Lp.ext
  filter_upwards [cuspAverage_core_ae 1 le_rfl (cuspProfileCore b hb hc hs),
    cuspRestrict_ae 1 (value (cuspProfileCore b hb hc hs)),
    ae_restrict_of_ae (cuspProfileCore_value_ae b hb hc hs),
    ae_restrict_mem (measurableSet_highCusp 1)] with τ ha hr hv hh
  change cuspAverage 1 le_rfl (cuspRestrict 1 (value (cuspProfileCore b hb hc hs))) τ =
    cuspHorizontalAverage (cuspProfileCore b hb hc hs).val τ.im at ha
  rw [ha, hr, hv]
  exact cuspHorizontalAverage_cuspProfileCore b hb hc hs hh

/-- The compact profile is exactly its actual high-cusp zero extension. -/
theorem cuspProfileCore_value_zeroExtend (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b)
    (hc : HasCompactSupport b) (hs : tsupport b ⊆ Ioi (1 : ℝ)) :
    cuspZeroExtend 1 (cuspRestrict 1 (value (cuspProfileCore b hb hc hs))) =
      value (cuspProfileCore b hb hc hs) := by
  apply Lp.ext
  filter_upwards [modularHighCut_ae 1 (value (cuspProfileCore b hb hc hs)),
    cuspProfileCore_value_ae b hb hc hs] with τ hh hv
  change modularHighCut 1 (value (cuspProfileCore b hb hc hs)) τ = _
  rw [hh]
  by_cases hτ : 1 < τ.im
  · exact indicator_of_mem (show τ ∈ {τ : UpperHalfPlane | 1 < τ.im} from hτ) _
  · rw [indicator_of_notMem (show τ ∉ {τ : UpperHalfPlane | 1 < τ.im} from hτ), hv]
    symm
    exact image_eq_zero_of_notMem_tsupport (fun h => hτ (hs h))

/-- Literal compact scalar profiles are orthogonal in mass to every actual zero-average form value. -/
theorem cuspProfileCore_mass_orthogonal (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b)
    (hc : HasCompactSupport b) (hs : tsupport b ⊆ Ioi (1 : ℝ)) (u : cuspMeanZeroForm) :
    inner ℂ (value (cuspProfileCore b hb hc hs)) (meanZeroCuspEmbedding u) = 0 := by
  rw [← cuspProfileCore_value_zeroExtend b hb hc hs, cuspZeroExtend_inner_restrict]
  rw [← cuspAverage_cuspProfileCore b hb hc hs, cuspAverage_inner,
    meanZeroCusp_average_eq_zero 1 le_rfl u, inner_zero_right]

/-- The actual full modular gradient pairs to zero with every constrained form vector. -/
theorem cuspProfileCore_energy_orthogonal (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b)
    (hc : HasCompactSupport b) (hs : tsupport b ⊆ Ioi (1 : ℝ)) (u : cuspMeanZeroForm) :
    inner ℂ (coreGradient (cuspProfileCore b hb hc hs)) (cuspMeanZeroGradient u) = 0 := by
  change inner ℂ (coreGradient (cuspProfileCore b hb hc hs)) (formGradient (u : FormDomain)) = 0
  rw [← cuspProfileCore_form_energy]
  exact cuspProfileCore_mass_orthogonal (cuspProfileSecondOrder b)
    (contDiff_cuspProfileSecondOrder hb) (cuspProfileSecondOrder_hasCompactSupport hc)
    ((cuspProfileSecondOrder_tsupport_subset b).trans hs) u

end GapFamily.Analytic
