import GapFamily.Analytic.Kernel.SchurKernelMass
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod

/-! Genuine product integrability and Fubini pairing for scalar Schur kernels.

The generic pairing identities below assert ordinary integrability of the full
weighted pairing. Convergence of a raw kernel fiber `∫ y, K (x, y) * f y` is a
separate obligation: it does not follow from the weighted product hypothesis
on rows where the left factor vanishes. The Schur operator construction supplies
that raw fiber integrability independently for every L² input. -/

noncomputable section
namespace GapFamily.Analytic.SchurKernelPairing

open MeasureTheory SchurKernelMass

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

/-- The two weighted square energies dominate the actual sesquilinear kernel
integrand. This lemma records ordinary product integrability before Fubini. -/
theorem integrable_pairing_of_weighted_square
    {K : X × X → ℂ} (hK : AEStronglyMeasurable K (μ.prod μ))
    (f g : Lp ℂ 2 μ)
    (hx : Integrable (fun p : X × X => ‖K p‖ * ‖g p.1‖ ^ 2) (μ.prod μ))
    (hy : Integrable (fun p : X × X => ‖K p‖ * ‖f p.2‖ ^ 2) (μ.prod μ)) :
    Integrable (fun p : X × X => star (g p.1) * K p * f p.2) (μ.prod μ) := by
  refine ((hx.add hy).div_const 2).mono'
    (((Lp.aestronglyMeasurable g).comp_fst.star.mul hK).mul
      (Lp.aestronglyMeasurable f).comp_snd) ?_
  filter_upwards with p
  simp only [norm_mul, norm_star]
  change ‖g p.1‖ * ‖K p‖ * ‖f p.2‖ ≤
    (‖K p‖ * ‖g p.1‖ ^ 2 + ‖K p‖ * ‖f p.2‖ ^ 2) / 2
  have hs := sq_nonneg (‖g p.1‖ - ‖f p.2‖)
  have hk := norm_nonneg (K p)
  nlinarith [mul_nonneg hk hs]

/-- Actual row and column norm bounds make every L² kernel pairing jointly
integrable. The row and column assumptions concern ordinary integrals. -/
theorem integrable_pairing
    {K : X × X → ℂ} (hK : AEStronglyMeasurable K (μ.prod μ))
    {C : ℝ} (hC : 0 ≤ C)
    (hrow : ∀ᵐ x ∂μ, Integrable (fun y => ‖K (x, y)‖) μ)
    (hrowbound : ∀ᵐ x ∂μ, (∫ y, ‖K (x, y)‖ ∂μ) ≤ C)
    (hcol : ∀ᵐ y ∂μ, Integrable (fun x => ‖K (x, y)‖) μ)
    (hcolbound : ∀ᵐ y ∂μ, (∫ x, ‖K (x, y)‖ ∂μ) ≤ C)
    (f g : Lp ℂ 2 μ) :
    Integrable (fun p : X × X => star (g p.1) * K p * f p.2) (μ.prod μ) := by
  have hg : Integrable (fun x => ‖g x‖ ^ 2) μ :=
    (Lp.memLp g).integrable_norm_pow (by norm_num)
  have hf : Integrable (fun y => ‖f y‖ ^ 2) μ :=
    (Lp.memLp f).integrable_norm_pow (by norm_num)
  obtain ⟨hy, _⟩ := integrable_weighted_kernel_and_mass_le hK hC hcol hcolbound hf
    (Filter.Eventually.of_forall fun y => sq_nonneg ‖f y‖)
  obtain ⟨hx', _⟩ := integrable_weighted_kernel_and_mass_le hK.prod_swap hC
    hrow hrowbound hg (Filter.Eventually.of_forall fun x => sq_nonneg ‖g x‖)
  have hx : Integrable (fun p : X × X => ‖K p‖ * ‖g p.1‖ ^ 2) (μ.prod μ) := by
    simpa only [Function.comp_def, Prod.swap_swap, Prod.snd_swap] using hx'.swap
  exact integrable_pairing_of_weighted_square hK f g hx hy

/-- Fubini exchanges the two integrations of the genuinely integrable weighted
kernel pairing. Raw kernel fiber convergence is a separate obligation. -/
theorem pairing_fubini {K : X × X → ℂ} (f g : Lp ℂ 2 μ)
    (h : Integrable (fun p : X × X => star (g p.1) * K p * f p.2) (μ.prod μ)) :
    (∫ x, star (g x) * (∫ y, K (x, y) * f y ∂μ) ∂μ) =
      ∫ y, (∫ x, star (g x) * K (x, y) ∂μ) * f y ∂μ := by
  calc
    (∫ x, star (g x) * (∫ y, K (x, y) * f y ∂μ) ∂μ) =
        ∫ x, ∫ y, star (g x) * K (x, y) * f y ∂μ ∂μ := by
      simp only [mul_assoc, integral_const_mul]
    _ = ∫ y, ∫ x, star (g x) * K (x, y) * f y ∂μ ∂μ :=
      integral_integral_swap (f := fun x y => star (g x) * K (x, y) * f y) h
    _ = _ := by simp only [integral_mul_const]


/-- The outer Hilbert-pairing integrand is ordinarily integrable. -/
theorem pairing_integrable {K : X × X → ℂ} (f g : Lp ℂ 2 μ)
    (h : Integrable (fun p : X × X => star (g p.1) * K p * f p.2) (μ.prod μ)) :
    Integrable (fun x => star (g x) * (∫ y, K (x, y) * f y ∂μ)) μ := by
  simpa only [mul_assoc, integral_const_mul] using h.integral_prod_left

/-- The iterated pairing equals its genuinely integrable product integral. -/
theorem pairing_eq_product_integral {K : X × X → ℂ} (f g : Lp ℂ 2 μ)
    (h : Integrable (fun p : X × X => star (g p.1) * K p * f p.2) (μ.prod μ)) :
    (∫ x, star (g x) * (∫ y, K (x, y) * f y ∂μ) ∂μ) =
      ∫ p : X × X, star (g p.1) * K p * f p.2 ∂μ.prod μ := by
  simpa only [mul_assoc, integral_const_mul] using (integral_prod _ h).symm

/-- An almost-everywhere Hermitian kernel gives conjugate symmetry of two
ordinarily convergent weighted pairings. Raw kernel fiber convergence is a
separate obligation, as for `pairing_fubini`. -/
theorem pairing_hermitian {K : X × X → ℂ}
    (hK : ∀ᵐ p ∂μ.prod μ, K p = star (K p.swap)) (f g : Lp ℂ 2 μ)
    (hfg : Integrable (fun p : X × X => star (g p.1) * K p * f p.2) (μ.prod μ))
    (hgf : Integrable (fun p : X × X => star (f p.1) * K p * g p.2) (μ.prod μ)) :
    (∫ x, star (g x) * (∫ y, K (x, y) * f y ∂μ) ∂μ) =
      star (∫ x, star (f x) * (∫ y, K (x, y) * g y ∂μ) ∂μ) := by
  rw [pairing_eq_product_integral f g hfg, pairing_eq_product_integral g f hgf]
  calc
    (∫ p : X × X, star (g p.1) * K p * f p.2 ∂μ.prod μ) =
        ∫ p : X × X, star (star (f p.2) * K p.swap * g p.1) ∂μ.prod μ := by
      apply integral_congr_ae
      filter_upwards [hK] with p hp
      simp only [star_mul, star_star]
      rw [← hp]
      ring
    _ = star (∫ p : X × X, star (f p.2) * K p.swap * g p.1 ∂μ.prod μ) :=
      integral_conj
    _ = star (∫ p : X × X, star (f p.1) * K p * g p.2 ∂μ.prod μ) := by
      congr 1
      exact integral_prod_swap (fun p : X × X => star (f p.1) * K p * g p.2)

end GapFamily.Analytic.SchurKernelPairing
