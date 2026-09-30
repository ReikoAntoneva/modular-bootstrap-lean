import GapFamily.Analytic.Cusp.CuspUpperHighValue
import GapFamily.Analytic.Cusp.CuspUpperGradientFiniteCover
import GapFamily.Analytic.Cusp.Threshold.CuspConstrainedThreshold
import GapFamily.Analytic.Cusp.Threshold.CuspConstrainedPoissonJet

noncomputable section
namespace GapFamily.Analytic.CuspConstrainedUpperNorm
open Set MeasureTheory UpperHalfPlane ModularGradient
open CuspUpperHighValue CuspThreeTileCover
  CuspUpperGradientFiniteCover CuspConstrainedThreshold
  CuspConstrainedPoissonJet UpperSource
open scoped ContDiff MatrixGroups Pointwise

/-- Mean-zero tail energy cancels the height growth in the actual ordinary cutoff. -/
theorem meanZero_cutoff_norm_sq_le
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet) (H : ℝ) (hH : 1 ≤ H)
    (hwindow : ∀ z ∈ tsupport χ, |z.re| ≤ 1 ∧ H < z.im)
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ z ∈ tsupport χ, z.im * ‖χ z‖ ≤ B)
    (u : cuspMeanZeroForm) :
    ‖upperCutoffValueOperator χ hχ hc hs (u : FormDomain)‖ ^ 2 ≤
      (3 * B ^ 2 / H ^ 2) * ‖formGradient (u : FormDomain)‖ ^ 2 := by
  have hv := upperCutoffHilbertValueOperator_high_norm_sq_le χ hχ hc hs H hH
    hwindow B hB hb (meanZeroCuspEmbedding u)
  have he : upperCutoffHilbertValueOperator χ hχ hc hs (meanZeroCuspEmbedding u) =
      upperCutoffValueOperator χ hχ hc hs (u : FormDomain) :=
    upperCutoffHilbertValueOperator_formEmbedding χ hχ hc hs u
  rw [he] at hv
  have ht := meanZeroCuspTail_energy_bound H hH u
  change ‖modularHighCut H (meanZeroCuspEmbedding u)‖ ^ 2 ≤ _ at ht
  calc
    _ ≤ 3 * B ^ 2 * ‖modularHighCut H (meanZeroCuspEmbedding u)‖ ^ 2 := hv
    _ ≤ 3 * B ^ 2 * ((1 / H ^ 2) * ‖formGradient (u : FormDomain)‖ ^ 2) :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    _ = _ := by ring

/-- A unit-height window has one fixed actual value-energy bound, at arbitrary height. -/
theorem meanZero_cutoff_unit_window_norm_sq_le
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet) (H : ℝ) (hH : 1 ≤ H)
    (hwindow : ∀ z ∈ tsupport χ, |z.re| ≤ 1 ∧ H < z.im ∧ z.im ≤ H + 1)
    (hamp : ∀ z ∈ tsupport χ, ‖χ z‖ ≤ 1) (u : cuspMeanZeroForm) :
    ‖upperCutoffValueOperator χ hχ hc hs (u : FormDomain)‖ ^ 2 ≤
      12 * ‖formGradient (u : FormDomain)‖ ^ 2 := by
  have hv := meanZero_cutoff_norm_sq_le χ hχ hc hs H hH
    (fun z hz => ⟨(hwindow z hz).1, (hwindow z hz).2.1⟩) (H + 1) (by linarith)
    (fun z hz => (mul_le_mul_of_nonneg_left (hamp z hz) (le_of_lt (hs hz))).trans
      (by simpa using (hwindow z hz).2.2)) u
  have hr : 3 * (H + 1) ^ 2 / H ^ 2 ≤ 12 := by
    apply (div_le_iff₀ (sq_pos_of_pos (by linarith : 0 < H))).mpr
    nlinarith
  exact hv.trans (mul_le_mul_of_nonneg_right hr (sq_nonneg _))

/-- Three actual tiles give a height-independent ordinary directional energy bound. -/
theorem gradient_cutoff_norm_sq_le
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet) (H : ℝ) (hH : 1 ≤ H)
    (hwindow : ∀ z ∈ tsupport χ, |z.re| ≤ 1 ∧ H < z.im)
    (hamp : ∀ z ∈ tsupport χ, ‖χ z‖ ≤ 1) (v : ℂ) (u : FormDomain) :
    ‖upperCutoffGradientOperator χ hχ hc hs v u‖ ^ 2 ≤
      6 * ‖v‖ ^ 2 * ‖formGradient u‖ ^ 2 := by
  have hg := upperCutoffGradientOperator_norm_sq_le_of_finite_cover hχ hc hs
    (by norm_num : (0 : ℝ) ≤ 1) hamp cuspThreeTiles
    (by intro τ hτ; exact cuspThreeTiles_cover_fd H hH (hwindow τ hτ)) v u
  have hn : (cuspThreeTiles.card : ℝ) ≤ 3 := by exact_mod_cast cuspThreeTiles_card_le
  calc
    _ ≤ 2 * 1 ^ 2 * ‖v‖ ^ 2 * (cuspThreeTiles.card : ℝ) * ‖formGradient u‖ ^ 2 := hg
    _ ≤ 2 * 1 ^ 2 * ‖v‖ ^ 2 * 3 * ‖formGradient u‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn (by positivity)) (sq_nonneg _)
    _ = _ := by ring

/-- The actual Poisson source lift gains the inverse height from its literal y^-2 factor. -/
theorem sourceOperator_high_norm_sq_le
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet) (H : ℝ) (hH : 1 ≤ H)
    (hwindow : ∀ z ∈ tsupport χ, |z.re| ≤ 1 ∧ H < z.im)
    (hamp : ∀ z ∈ tsupport χ, ‖χ z‖ ≤ 1) (f : ModularHilbert) :
    ‖sourceOperator χ hχ hc hs f‖ ^ 2 ≤ (3 / H ^ 2) * ‖f‖ ^ 2 := by
  have hHpos : 0 < H := by linarith
  have hsub := tsupport_upperSourceTestFunction_subset χ
  have hb : ∀ z ∈ tsupport (upperSourceTestFunction χ),
      z.im * ‖upperSourceTestFunction χ z‖ ≤ 1 / H := by
    intro z hz
    have hy : 0 < z.im := hs (hsub hz)
    have hHy := (hwindow z (hsub hz)).2
    rw [upperSourceTestFunction, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hy]
    calc
      z.im * (‖χ z‖ / z.im ^ 2) = ‖χ z‖ / z.im := by field_simp
      _ ≤ 1 / z.im := div_le_div_of_nonneg_right (hamp z (hsub hz)) hy.le
      _ ≤ 1 / H := one_div_le_one_div_of_le hHpos hHy.le
  have h := upperCutoffHilbertValueOperator_high_norm_sq_le (upperSourceTestFunction χ)
    (contDiff_upperSourceTestFunction hχ hs) (hasCompactSupport_upperSourceTestFunction hc)
    (hsub.trans hs) H hH (fun z hz => hwindow z (hsub hz)) (1 / H) (by positivity) hb f
  change ‖sourceOperator χ hχ hc hs f‖ ^ 2 ≤ _ at h
  calc
    _ ≤ 3 * (1 / H) ^ 2 * ‖modularHighCut H f‖ ^ 2 := h
    _ ≤ 3 * (1 / H) ^ 2 * ‖f‖ ^ 2 := mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (norm_modularHighCut_le H f)) (by positivity)
    _ = _ := by ring

/-- All four actual local Poisson fields have a single explicit uniform estimate.
Only genuine constrained energy and genuine ambient source mass occur on the right. -/
theorem constrainedJet_field_mass_bound
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet) (H : ℝ) (hH : 1 ≤ H)
    (hwindow : ∀ z ∈ tsupport χ, |z.re| ≤ 1 ∧ H < z.im ∧ z.im ≤ H + 1)
    (hamp : ∀ z ∈ tsupport χ, ‖χ z‖ ≤ 1) (f : ModularHilbert) :
    let j := constrainedJet χ hχ hc hs f
    ‖j.1‖ ^ 2 + ‖j.2.1‖ ^ 2 + ‖j.2.2.1‖ ^ 2 + ‖j.2.2.2‖ ^ 2 ≤
      24 * ‖formGradient (cuspMeanZeroPencilSolution (1 / 4) f : FormDomain)‖ ^ 2 +
        3 * ‖constrainedPoissonSource f‖ ^ 2 := by
  have hw : ∀ z ∈ tsupport χ, |z.re| ≤ 1 ∧ H < z.im :=
    fun z hz => ⟨(hwindow z hz).1, (hwindow z hz).2.1⟩
  have hv := meanZero_cutoff_unit_window_norm_sq_le χ hχ hc hs H hH hwindow hamp
    (cuspMeanZeroPencilSolution (1 / 4) f)
  have hx := gradient_cutoff_norm_sq_le χ hχ hc hs H hH hw hamp 1
    (cuspMeanZeroPencilSolution (1 / 4) f : FormDomain)
  have hy := gradient_cutoff_norm_sq_le χ hχ hc hs H hH hw hamp Complex.I
    (cuspMeanZeroPencilSolution (1 / 4) f : FormDomain)
  have hf := sourceOperator_high_norm_sq_le χ hχ hc hs H hH hw hamp (constrainedPoissonSource f)
  have hr : 3 / H ^ 2 ≤ 3 := by
    apply (div_le_iff₀ (sq_pos_of_pos (by linarith : 0 < H))).mpr
    nlinarith
  have hf' := hf.trans (mul_le_mul_of_nonneg_right hr (sq_nonneg _))
  simp only [norm_one, Complex.norm_I, one_pow, mul_one] at hx hy
  dsimp only [constrainedJet]
  linarith

end GapFamily.Analytic.CuspConstrainedUpperNorm
