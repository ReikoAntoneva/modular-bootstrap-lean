import GapFamily.Analytic.Modular.Periodization.ModularPeriodizationLp
import Mathlib.Analysis.Normed.Group.Bounded

noncomputable section
namespace GapFamily.Analytic
open Set MeasureTheory UpperHalfPlane
open scoped ContDiff

private theorem modularMultiplier_memLp (a : ℂ → ℂ) (ha : Continuous a)
    (C : ℝ) (hC : ∀ z, ‖a z‖ ≤ C) (f : ModularHilbert) :
    MemLp (fun τ : UpperHalfPlane => a τ * f τ) 2 modularMeasure := by
  apply (Lp.memLp f).of_le_mul (c := C)
    (((ha.comp continuous_coe).aestronglyMeasurable).mul (Lp.aestronglyMeasurable f))
  exact Filter.Eventually.of_forall fun τ => by
    change ‖a τ * f τ‖ ≤ C * ‖f τ‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hC τ) (norm_nonneg (f τ))

private def modularMultiplierValue (a : ℂ → ℂ) (ha : Continuous a)
    (C : ℝ) (hC : ∀ z, ‖a z‖ ≤ C) (f : ModularHilbert) : ModularHilbert :=
  (modularMultiplier_memLp a ha C hC f).toLp _

private theorem modularMultiplierValue_ae (a : ℂ → ℂ) (ha : Continuous a)
    (C : ℝ) (hC : ∀ z, ‖a z‖ ≤ C) (f : ModularHilbert) :
    modularMultiplierValue a ha C hC f =ᵐ[modularMeasure]
      (fun τ : UpperHalfPlane => a τ * f τ) := MemLp.coeFn_toLp _

private theorem modularMultiplierValue_norm_le (a : ℂ → ℂ) (ha : Continuous a)
    (C : ℝ) (hC : ∀ z, ‖a z‖ ≤ C) (f : ModularHilbert) :
    ‖modularMultiplierValue a ha C hC f‖ ≤ C * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [modularMultiplierValue_ae a ha C hC f] with τ hτ
  rw [hτ, norm_mul]
  exact mul_le_mul_of_nonneg_right (hC τ) (norm_nonneg (f τ))

/-- Multiplication on actual modular L² by a continuous globally bounded coefficient. -/
def modularBoundedMultiplier (a : ℂ → ℂ) (ha : Continuous a)
    (C : ℝ) (_hC0 : 0 ≤ C) (hC : ∀ z, ‖a z‖ ≤ C) :
    ModularHilbert →L[ℂ] ModularHilbert :=
  LinearMap.mkContinuous
    { toFun := modularMultiplierValue a ha C hC
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [modularMultiplierValue_ae a ha C hC (f + g),
          modularMultiplierValue_ae a ha C hC f,
          modularMultiplierValue_ae a ha C hC g, Lp.coeFn_add f g,
          Lp.coeFn_add (modularMultiplierValue a ha C hC f)
            (modularMultiplierValue a ha C hC g)] with τ hfg hf hg hsum hout
        simp only [Pi.add_apply] at hsum hout
        rw [hfg, hout, hf, hg, hsum, mul_add]
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [modularMultiplierValue_ae a ha C hC (c • f),
          modularMultiplierValue_ae a ha C hC f, Lp.coeFn_smul c f,
          Lp.coeFn_smul c (modularMultiplierValue a ha C hC f)] with τ hcf hf hsm hout
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply] at hsm hout ⊢
        rw [hcf, hout, hf, hsm]
        ring }
    C (modularMultiplierValue_norm_le a ha C hC)

theorem modularBoundedMultiplier_ae (a : ℂ → ℂ) (ha : Continuous a)
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ z, ‖a z‖ ≤ C) (f : ModularHilbert) :
    modularBoundedMultiplier a ha C hC0 hC f =ᵐ[modularMeasure]
      (fun τ : UpperHalfPlane => a τ * f τ) :=
  modularMultiplierValue_ae a ha C hC f

theorem modularBoundedMultiplier_norm_le (a : ℂ → ℂ) (ha : Continuous a)
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ z, ‖a z‖ ≤ C) :
    ‖modularBoundedMultiplier a ha C hC0 hC‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC0
  exact modularMultiplierValue_norm_le a ha C hC

/-- A concrete nonnegative global bound selected from compact support. -/
def modularCutoffMultiplierBound (a : ℂ → ℂ) (ha : Continuous a)
    (hc : HasCompactSupport a) : ℝ :=
  (hc.exists_bound_of_continuous ha).choose

theorem norm_le_modularCutoffMultiplierBound (a : ℂ → ℂ) (ha : Continuous a)
    (hc : HasCompactSupport a) (z : ℂ) : ‖a z‖ ≤ modularCutoffMultiplierBound a ha hc :=
  (hc.exists_bound_of_continuous ha).choose_spec z

theorem modularCutoffMultiplierBound_nonneg (a : ℂ → ℂ) (ha : Continuous a)
    (hc : HasCompactSupport a) : 0 ≤ modularCutoffMultiplierBound a ha hc :=
  (norm_nonneg (a 0)).trans (norm_le_modularCutoffMultiplierBound a ha hc 0)

/-- The actual bounded complex L² multiplier associated to a compact coefficient. -/
def modularCutoffMultiplier (a : ℂ → ℂ) (ha : Continuous a)
    (hc : HasCompactSupport a) : ModularHilbert →L[ℂ] ModularHilbert :=
  modularBoundedMultiplier a ha (modularCutoffMultiplierBound a ha hc)
    (modularCutoffMultiplierBound_nonneg a ha hc) (norm_le_modularCutoffMultiplierBound a ha hc)

theorem modularCutoffMultiplier_ae (a : ℂ → ℂ) (ha : Continuous a)
    (hc : HasCompactSupport a) (f : ModularHilbert) :
    modularCutoffMultiplier a ha hc f =ᵐ[modularMeasure]
      (fun τ : UpperHalfPlane => a τ * f τ) :=
  modularBoundedMultiplier_ae _ _ _ _ _ _

theorem modularCutoffMultiplier_norm_le (a : ℂ → ℂ) (ha : Continuous a)
    (hc : HasCompactSupport a) :
    ‖modularCutoffMultiplier a ha hc‖ ≤ modularCutoffMultiplierBound a ha hc :=
  modularBoundedMultiplier_norm_le _ _ _ _ _

theorem modularCutoffMultiplier_apply_norm_le (a : ℂ → ℂ) (ha : Continuous a)
    (hc : HasCompactSupport a) (f : ModularHilbert) :
    ‖modularCutoffMultiplier a ha hc f‖ ≤ modularCutoffMultiplierBound a ha hc * ‖f‖ :=
  ((modularCutoffMultiplier a ha hc).le_opNorm f).trans
    (mul_le_mul_of_nonneg_right (modularCutoffMultiplier_norm_le a ha hc) (norm_nonneg f))

/-- Continuity of the actual hyperbolic directional cutoff coefficient. -/
theorem continuous_modularCutoffDirectionalCoefficient (χ : ℂ → ℂ)
    (hχ : ContDiff ℝ ∞ χ) (v : ℂ) :
    Continuous (fun z : ℂ => (z.im : ℂ) * fderiv ℝ χ z v) :=
  (Complex.continuous_ofReal.comp Complex.continuous_im).mul
    (ModularGradient.continuous_complexTestDerivative χ hχ v)

/-- Multiplication by an actual hyperbolic directional derivative of a smooth cutoff. -/
def modularCutoffDirectionalMultiplier (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (v : ℂ) : ModularHilbert →L[ℂ] ModularHilbert :=
  modularCutoffMultiplier (fun z => (z.im : ℂ) * fderiv ℝ χ z v)
    (continuous_modularCutoffDirectionalCoefficient χ hχ v)
    (ModularGradient.compactSupport_testDirectional χ hc v)

theorem modularCutoffDirectionalMultiplier_ae (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (v : ℂ) (f : ModularHilbert) :
    modularCutoffDirectionalMultiplier χ hχ hc v f =ᵐ[modularMeasure]
      (fun τ : UpperHalfPlane => ((τ.im : ℂ) * fderiv ℝ χ τ v) * f τ) :=
  modularCutoffMultiplier_ae _ _ _ _

end GapFamily.Analytic
