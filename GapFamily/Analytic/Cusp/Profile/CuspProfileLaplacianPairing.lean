import GapFamily.Analytic.Cusp.Profile.CuspProfileCore
import GapFamily.Analytic.Cusp.Fourier.CuspHorizontalProjectionPairing

/-!
# Actual scalar-profile value pairings in the modular cusp

Literal profile values and complex Bochner Fubini identify the modular L²
pairing with the inverse-square weighted ordinary horizontal average.
-/

noncomputable section

namespace GapFamily.Analytic

open Set MeasureTheory UpperHalfPlane ModularGradient
open scoped ContDiff

theorem cuspProfileCore_value_pairing_integrable (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b)
    (hc : HasCompactSupport b) (hs : tsupport b ⊆ Ioi (1 : ℝ)) (F : smoothCore) :
    Integrable (fun τ : UpperHalfPlane => inner ℂ (b τ.im) (F.val τ)) modularMeasure := by
  apply (L2.integrable_inner (𝕜 := ℂ) (value (cuspProfileCore b hb hc hs)) (value F)).congr
  filter_upwards [cuspProfileCore_value_ae b hb hc hs, value_ae F] with τ hbτ hFτ
  rw [hbτ, hFτ]

/-- The actual modular profile pairing is the convergent horizontal-average pairing. -/
theorem cuspProfileCore_value_pairing (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b)
    (hc : HasCompactSupport b) (hs : tsupport b ⊆ Ioi (1 : ℝ)) (F : smoothCore) :
    inner ℂ (value (cuspProfileCore b hb hc hs)) (value F) =
      ∫ y : ℝ in Ioi 1, (1 / y ^ 2 : ℝ) •
        ((starRingEnd ℂ) (b y) * cuspHorizontalAverage F.val y) := by
  have hrep : inner ℂ (value (cuspProfileCore b hb hc hs)) (value F) =
      ∫ τ : UpperHalfPlane, inner ℂ (b τ.im) (F.val τ) ∂modularMeasure := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [cuspProfileCore_value_ae b hb hc hs, value_ae F] with τ hbτ hFτ
    rw [hbτ, hFτ]
  rw [hrep]
  have hcut : (∫ τ : UpperHalfPlane in {τ | 1 < τ.im},
      inner ℂ (b τ.im) (F.val τ) ∂modularMeasure) =
      ∫ τ : UpperHalfPlane, inner ℂ (b τ.im) (F.val τ) ∂modularMeasure := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro τ hτ
    have hzero : b τ.im = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hh => hτ (hs hh))
    simp only [hzero, inner_zero_left]
  have hfub := integral_modular_highCusp_of_integrable
    (fun z => inner ℂ (b z.im) (F.val z)) le_rfl
    (cuspProfileCore_value_pairing_integrable b hb hc hs F).integrableOn
  simp only [coe_im] at hfub
  rw [← hcut, hfub]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  have hy0 : 0 < y := zero_lt_one.trans hy
  have hi : IntegrableOn (fun x => F.val (Complex.mk x y))
      (Ioo (-1/2 : ℝ) (1/2)) :=
    (contDiff_cuspHorizontalSlice F.property.1 hy0).continuous.integrableOn_Icc.mono_set
      Ioo_subset_Icc_self
  dsimp only
  rw [integral_smul, integral_inner hi, ← cuspHorizontalAverage_eq_setIntegral F y]
  rw [RCLike.inner_apply']

end GapFamily.Analytic
