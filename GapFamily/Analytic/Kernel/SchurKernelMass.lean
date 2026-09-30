import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Complex.Basic

/-! Ordinary joint integrability and row mass from an actual column norm bound. -/

noncomputable section
namespace GapFamily.Analytic.SchurKernelMass

open MeasureTheory Filter

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

/-- An integrable nonnegative weight and the actual almost-everywhere column
bound give genuine product integrability before any Fubini identity is used. -/
theorem integrable_weighted_kernel_and_mass_le
    {K : X × X → ℂ} (hK : AEStronglyMeasurable K (μ.prod μ))
    {C : ℝ} (hC : 0 ≤ C)
    (hcol : ∀ᵐ y ∂μ, Integrable (fun x => ‖K (x, y)‖) μ)
    (hcolbound : ∀ᵐ y ∂μ, (∫ x, ‖K (x, y)‖ ∂μ) ≤ C)
    {g : X → ℝ} (hg : Integrable g μ) (hg_nonneg : ∀ᵐ y ∂μ, 0 ≤ g y) :
    Integrable (fun p : X × X => ‖K p‖ * g p.2) (μ.prod μ) ∧
      (∫ p : X × X, ‖K p‖ * g p.2 ∂μ.prod μ) ≤ C * ∫ y, g y ∂μ := by
  have hm : AEStronglyMeasurable (fun p : X × X => ‖K p‖ * g p.2) (μ.prod μ) :=
    hK.norm.mul hg.aestronglyMeasurable.comp_snd
  have hcols : ∀ᵐ y ∂μ, Integrable (fun x => ‖K (x, y)‖ * g y) μ := by
    filter_upwards [hcol] with y hy
    exact hy.mul_const (g y)
  have hnormcolumn (y : X) (hy : 0 ≤ g y) :
      (∫ x, ‖‖K (x, y)‖ * g y‖ ∂μ) = (∫ x, ‖K (x, y)‖ ∂μ) * g y := by
    simp only [norm_mul, norm_norm, Real.norm_of_nonneg hy, integral_mul_const]
  have hmass : Integrable (fun y => ∫ x, ‖‖K (x, y)‖ * g y‖ ∂μ) μ := by
    apply (hg.const_mul C).mono hm.norm.prod_swap.integral_prod_right'
    filter_upwards [hcolbound, hg_nonneg] with y hy hgy
    change ‖∫ x, ‖‖K (x, y)‖ * g y‖ ∂μ‖ ≤ ‖C * g y‖
    rw [Real.norm_of_nonneg (integral_nonneg fun x => norm_nonneg _),
      Real.norm_of_nonneg (mul_nonneg hC hgy), hnormcolumn y hgy]
    exact mul_le_mul_of_nonneg_right hy hgy
  have hj : Integrable (fun p : X × X => ‖K p‖ * g p.2) (μ.prod μ) :=
    (integrable_prod_iff' hm).mpr ⟨hcols, hmass⟩
  refine ⟨hj, ?_⟩
  rw [integral_prod_symm _ hj]
  calc
    (∫ y, ∫ x, ‖K (x, y)‖ * g y ∂μ ∂μ) ≤ ∫ y, C * g y ∂μ := by
      apply integral_mono_ae hj.integral_prod_right (hg.const_mul C)
      filter_upwards [hcolbound, hg_nonneg] with y hy hgy
      rw [integral_mul_const]
      exact mul_le_mul_of_nonneg_right hy hgy
    _ = C * ∫ y, g y ∂μ := integral_const_mul C g

/-- The row energy is an actual integrable function, its fibers are ordinarily
integrable almost everywhere, and its total mass has the same column bound. -/
theorem weighted_row_integrable_and_mass_le
    {K : X × X → ℂ} (hK : AEStronglyMeasurable K (μ.prod μ))
    {C : ℝ} (hC : 0 ≤ C)
    (hcol : ∀ᵐ y ∂μ, Integrable (fun x => ‖K (x, y)‖) μ)
    (hcolbound : ∀ᵐ y ∂μ, (∫ x, ‖K (x, y)‖ ∂μ) ≤ C)
    {g : X → ℝ} (hg : Integrable g μ) (hg_nonneg : ∀ᵐ y ∂μ, 0 ≤ g y) :
    (∀ᵐ x ∂μ, Integrable (fun y => ‖K (x, y)‖ * g y) μ) ∧
      Integrable (fun x => ∫ y, ‖K (x, y)‖ * g y ∂μ) μ ∧
      (∫ x, ∫ y, ‖K (x, y)‖ * g y ∂μ ∂μ) ≤ C * ∫ y, g y ∂μ := by
  obtain ⟨hj, hb⟩ := integrable_weighted_kernel_and_mass_le hK hC hcol hcolbound hg hg_nonneg
  refine ⟨hj.prod_right_ae, hj.integral_prod_left, ?_⟩
  rw [← integral_prod _ hj]
  exact hb

end GapFamily.Analytic.SchurKernelMass
