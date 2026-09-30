import Homogenization.Sobolev.WeakDerivatives
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Complex weak derivatives from their real and imaginary components

All pairings below are ordinary integrable functions for the unnormalized
restricted Lebesgue measure. Projection through the Bochner integral is used
only after those integrability statements have been proved.
-/

noncomputable section

namespace GapFamily.Analytic.ModularElliptic

open Set MeasureTheory Homogenization

/-- Recombining actual real `L²` representatives gives an actual complex `L²` field. -/
theorem memLp_complex_of_memLp_re_im {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {R I : X → ℝ}
    (hR : MemLp R 2 μ) (hI : MemLp I 2 μ) :
    MemLp (fun v => (R v : ℂ) + (I v : ℂ) * Complex.I) 2 μ := by
  have hRc : MemLp (fun v => (R v : ℂ)) 2 μ := hR.ofReal
  have hIc : MemLp (fun v => (I v : ℂ)) 2 μ := hI.ofReal
  simpa only [Pi.add_apply, mul_comm] using! hRc.add (hIc.const_mul Complex.I)

/-- An `L²` field paired with a continuous compact real test is genuinely integrable. -/
theorem complex_mul_real_test_integrable {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
    {μ : Measure X} [IsLocallyFiniteMeasure μ] {U : Set X}
    {F : X → ℂ} (hF : MemLp F 2 (μ.restrict U))
    (φ : X → ℝ) (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    IntegrableOn (fun v => F v * (φ v : ℂ)) U μ := by
  simpa only [IntegrableOn, Complex.real_smul, mul_comm] using!
    (hF.locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport hφ hc

/-- Both products in the complex weak derivative identity are integrable,
even before any weak derivative equation is imposed. -/
theorem complex_weakPartial_test_integrable {d : ℕ} {U : Set (Vec d)}
    {F G : Vec d → ℂ}
    (hF : MemLp F 2 (volume.restrict U)) (hG : MemLp G 2 (volume.restrict U))
    (j : Fin d) (φ : Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    IntegrableOn (fun v => F v * (fderiv ℝ φ v (basisVec j) : ℂ)) U ∧
      IntegrableOn (fun v => G v * (φ v : ℂ)) U := by
  refine ⟨?_, complex_mul_real_test_integrable hG φ hφ.continuous hc⟩
  exact complex_mul_real_test_integrable hF (fun v => fderiv ℝ φ v (basisVec j))
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
    (hc.fderiv_apply ℝ (basisVec j))

/-- The real and imaginary weak derivative equations combine into the
ordinary complex equation, with its actual `L²` representatives. -/
theorem complex_hasWeakPartialDerivOn {d : ℕ} {U : Set (Vec d)}
    {F G : Vec d → ℂ} (j : Fin d)
    (hF : MemLp F 2 (volume.restrict U)) (hG : MemLp G 2 (volume.restrict U))
    (hR : HasWeakPartialDerivOn U j (fun v => (F v).re) (fun v => (G v).re))
    (hI : HasWeakPartialDerivOn U j (fun v => (F v).im) (fun v => (G v).im))
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U) :
    (∫ v in U, F v * (fderiv ℝ φ v (basisVec j) : ℂ)) =
      -(∫ v in U, G v * (φ v : ℂ)) := by
  obtain ⟨hleft, hright⟩ := complex_weakPartial_test_integrable hF hG j φ hφ hc
  apply Complex.ext
  · have hL := (Complex.reCLM.integral_comp_comm hleft).symm
    have hT := (Complex.reCLM.integral_comp_comm hright).symm
    simp only [Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero] at hL hT
    rw [Complex.neg_re, hL, hT]
    exact hR φ hφ hc hs
  · have hL := (Complex.imCLM.integral_comp_comm hleft).symm
    have hT := (Complex.imCLM.integral_comp_comm hright).symm
    simp only [Complex.imCLM_apply, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, zero_add] at hL hT
    rw [Complex.neg_im, hL, hT]
    exact hI φ hφ hc hs

end GapFamily.Analytic.ModularElliptic
