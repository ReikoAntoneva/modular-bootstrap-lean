import GapFamily.Analytic.Modular.Geometry.ModularCutoffMultiplier
import GapFamily.Analytic.Modular.ModularBoundary

noncomputable section
namespace GapFamily.Analytic
open Set MeasureTheory

/-- A continuous bounded extension of the actual cusp decay weight. -/
def cuspInputWeight (α : ℝ) (z : ℂ) : ℂ :=
  ((max (1 / 2 : ℝ) z.im) ^ (-α) : ℝ)

theorem cuspInputWeight_continuous (α : ℝ) : Continuous (cuspInputWeight α) := by
  apply Complex.continuous_ofReal.comp
  exact (continuous_const.max Complex.continuous_im).rpow_const fun z =>
    Or.inl (ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2)
      (le_max_left _ _)))

theorem cuspInputWeight_norm_le {α : ℝ} (hα : 0 ≤ α) (z : ℂ) :
    ‖cuspInputWeight α z‖ ≤ (1 / 2 : ℝ) ^ (-α) := by
  rw [cuspInputWeight, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  exact Real.rpow_le_rpow_of_nonpos (by norm_num) (le_max_left _ _) (neg_nonpos.mpr hα)

theorem cuspInputWeight_of_mem_fd (α : ℝ) {τ : UpperHalfPlane}
    (hτ : τ ∈ ModularGroup.fd) : cuspInputWeight α τ = (τ.im ^ (-α) : ℝ) := by
  simp only [cuspInputWeight, UpperHalfPlane.coe_im,
    max_eq_right (one_half_lt_im_of_mem_fd hτ).le]

theorem cuspInputWeight_of_one_lt_im (α : ℝ) {τ : UpperHalfPlane}
    (hτ : 1 < τ.im) :
    cuspInputWeight α τ = Complex.exp (-(α : ℂ) * (Real.log τ.im : ℂ)) := by
  have hy : (1 / 2 : ℝ) ≤ τ.im := by linarith
  simp only [cuspInputWeight, UpperHalfPlane.coe_im, max_eq_right hy,
    Real.rpow_def_of_pos τ.im_pos, Complex.ofReal_exp, Complex.ofReal_mul,
    Complex.ofReal_neg]
  congr 1
  ring

/-- Multiplication by the actual `y⁻ᵅ` weight on modular L². -/
def cuspWeightedInput (α : ℝ) (hα : 0 ≤ α) : ModularHilbert →L[ℂ] ModularHilbert :=
  modularBoundedMultiplier (cuspInputWeight α) (cuspInputWeight_continuous α)
    ((1 / 2 : ℝ) ^ (-α)) (Real.rpow_nonneg (by norm_num) _)
    (cuspInputWeight_norm_le hα)

theorem cuspWeightedInput_ae (α : ℝ) (hα : 0 ≤ α) (f : ModularHilbert) :
    cuspWeightedInput α hα f =ᵐ[modularMeasure]
      (fun τ : UpperHalfPlane => (τ.im ^ (-α) : ℝ) * f τ) := by
  filter_upwards [modularBoundedMultiplier_ae (cuspInputWeight α)
    (cuspInputWeight_continuous α) ((1 / 2 : ℝ) ^ (-α))
    (Real.rpow_nonneg (by norm_num) _) (cuspInputWeight_norm_le hα) f,
    ae_mem_fdo] with τ hf hτ
  change modularBoundedMultiplier _ _ _ _ _ f τ = _
  rw [hf, cuspInputWeight_of_mem_fd α (ModularGroup.fdo_subset_fd hτ)]

theorem cuspWeightedInput_norm_le (α : ℝ) (hα : 0 ≤ α) :
    ‖cuspWeightedInput α hα‖ ≤ (1 / 2 : ℝ) ^ (-α) :=
  modularBoundedMultiplier_norm_le _ _ _ _ _

theorem cuspWeightedInput_inner (α : ℝ) (hα : 0 ≤ α) (f g : ModularHilbert) :
    inner ℂ (cuspWeightedInput α hα f) g = inner ℂ f (cuspWeightedInput α hα g) := by
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [cuspWeightedInput_ae α hα f, cuspWeightedInput_ae α hα g] with τ hf hg
  rw [hf, hg]
  simp only [RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

end GapFamily.Analytic
