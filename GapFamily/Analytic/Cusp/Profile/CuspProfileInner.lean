import GapFamily.Analytic.Cusp.Fourier.CuspHorizontalProjectionPairingMeasure
import GapFamily.Analytic.Modular.ModularHilbert

/-!
# Inner products of actual scalar cusp representatives

The inverse-square scalar integral and its ordinary integrability follow from
the actual modular `L²` inner product. No regularity of either profile is assumed.
-/

noncomputable section

namespace GapFamily.Analytic

open Set MeasureTheory UpperHalfPlane

private theorem cuspProfile_inner_row (b c : ℝ → ℂ) (y : ℝ) :
    (∫ _x : ℝ in Ioo (-1/2) (1/2),
      (1 / y ^ 2 : ℝ) • inner ℂ (b y) (c y)) =
      inner ℂ (b y) (c y) / (y : ℂ) ^ 2 := by
  rw [integral_const]
  norm_num [Measure.real, Real.volume_Ioo, Complex.real_smul, div_eq_mul_inv, mul_comm]

/-- Genuine scalar integrability and the literal modular inner pairing, for any
two `L²` vectors represented by scalar profiles clipped at height one. -/
theorem cuspProfile_inner_integral (u v : ModularHilbert) (b c : ℝ → ℂ)
    (hu : u =ᵐ[modularMeasure]
      fun τ : UpperHalfPlane => if 1 < τ.im then b τ.im else 0)
    (hv : v =ᵐ[modularMeasure]
      fun τ : UpperHalfPlane => if 1 < τ.im then c τ.im else 0) :
    IntegrableOn (fun y => inner ℂ (b y) (c y) / (y : ℂ) ^ 2) (Ioi 1) ∧
      inner ℂ u v = ∫ y : ℝ in Ioi 1, inner ℂ (b y) (c y) / (y : ℂ) ^ 2 := by
  have hae : (fun τ => inner ℂ (u τ) (v τ)) =ᵐ[modularMeasure]
      (fun τ : UpperHalfPlane => if 1 < τ.im then inner ℂ (b τ.im) (c τ.im) else 0) := by
    filter_upwards [hu, hv] with τ huτ hvτ
    rw [huτ, hvτ]
    split_ifs <;> simp
  have hi := (L2.integrable_inner (𝕜 := ℂ) u v).congr hae
  have hS : MeasurableSet {τ : UpperHalfPlane | 1 < τ.im} :=
    (isOpen_lt continuous_const UpperHalfPlane.continuous_im).measurableSet
  have hhigh : IntegrableOn
      (fun τ : UpperHalfPlane => inner ℂ (b (τ : ℂ).im) (c (τ : ℂ).im))
      {τ | 1 < τ.im} modularMeasure := by
    apply hi.restrict.congr
    filter_upwards [ae_restrict_mem (μ := modularMeasure) hS] with τ hτ
    simp only [ite_eq_left hτ, coe_im]
  have hprod := integrableOn_modular_highCusp_weight
    (fun z : ℂ => inner ℂ (b z.im) (c z.im)) le_rfl hhigh
  rw [IntegrableOn, ← Measure.prod_restrict] at hprod
  refine ⟨?_, ?_⟩
  · simpa only [IntegrableOn, cuspProfile_inner_row] using hprod.integral_prod_right
  · rw [L2.inner_def, integral_congr_ae hae]
    have hzero : ∀ τ : UpperHalfPlane, τ ∉ {τ | 1 < τ.im} →
        (if 1 < τ.im then inner ℂ (b τ.im) (c τ.im) else 0) = 0 := by
      intro τ hτ
      exact ite_eq_right hτ
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
    trans ∫ τ : UpperHalfPlane in {τ | 1 < τ.im},
      inner ℂ (b τ.im) (c τ.im) ∂modularMeasure
    · apply setIntegral_congr_fun hS
      intro τ hτ
      exact ite_eq_left hτ
    · have htransport := integral_modular_highCusp_of_integrable
        (fun z : ℂ => inner ℂ (b z.im) (c z.im)) le_rfl hhigh
      simpa only [coe_im, cuspProfile_inner_row] using htransport

theorem cuspProfile_inner_integrable (u v : ModularHilbert) (b c : ℝ → ℂ)
    (hu : u =ᵐ[modularMeasure]
      fun τ : UpperHalfPlane => if 1 < τ.im then b τ.im else 0)
    (hv : v =ᵐ[modularMeasure]
      fun τ : UpperHalfPlane => if 1 < τ.im then c τ.im else 0) :
    IntegrableOn (fun y => inner ℂ (b y) (c y) / (y : ℂ) ^ 2) (Ioi 1) :=
  (cuspProfile_inner_integral u v b c hu hv).1

theorem cuspProfile_inner_eq_integral (u v : ModularHilbert) (b c : ℝ → ℂ)
    (hu : u =ᵐ[modularMeasure]
      fun τ : UpperHalfPlane => if 1 < τ.im then b τ.im else 0)
    (hv : v =ᵐ[modularMeasure]
      fun τ : UpperHalfPlane => if 1 < τ.im then c τ.im else 0) :
    inner ℂ u v = ∫ y : ℝ in Ioi 1, inner ℂ (b y) (c y) / (y : ℂ) ^ 2 :=
  (cuspProfile_inner_integral u v b c hu hv).2

end GapFamily.Analytic
