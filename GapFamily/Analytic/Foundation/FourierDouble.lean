import Mathlib.Analysis.Fourier.Inversion

/-! Ordinary Fourier double inversion in the project's literal phase
convention. All hypotheses are analytic conditions on the supplied functions;
the proof uses only mathlib's proved Fourier inversion theorem. -/

noncomputable section
namespace GapFamily.Analytic
open MeasureTheory
open scoped FourierTransform

/-- Mathlib's real Fourier transform uses exactly the literal negative phase. -/
theorem fourier_eq_literal_integral (f : ℝ → ℂ) (J : ℝ) :
    𝓕 f J = ∫ x : ℝ,
      Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (J : ℂ) * (x : ℂ)) * f x := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with x
  rw [smul_eq_mul]
  congr 2
  push_cast
  ring

/-- The Fourier transform applied twice is reflection, stated as an ordinary
literal-phase integral at any continuity point of the original function. -/
theorem integral_fourier_double (g : ℝ → ℂ) (hg : Integrable g)
    (hFg : Integrable (𝓕 g)) (J : ℝ) (hc : ContinuousAt g (-J)) :
    (∫ x : ℝ,
      Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (J : ℂ) * (x : ℂ)) * 𝓕 g x) =
      g (-J) := by
  rw [← fourier_eq_literal_integral]
  have h := hg.fourierInv_fourier_eq hFg hc
  simpa only [Real.fourierInv_eq_fourier_neg, neg_neg] using h

/-- A pointwise formula for the first Fourier transform can be substituted
without introducing any new transform or normalization convention. -/
theorem integral_fourier_double_of_eq (f g : ℝ → ℂ) (hg : Integrable g)
    (hf : Integrable f) (hfg : ∀ x, f x = 𝓕 g x) (hc : Continuous g) (J : ℝ) :
    (∫ x : ℝ,
      Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (J : ℂ) * (x : ℂ)) * f x) =
      g (-J) := by
  have heq : f = 𝓕 g := funext hfg
  subst f
  exact integral_fourier_double g hg hf J hc.continuousAt

/-- A fully literal integral interface for applying double Fourier inversion. -/
theorem integral_fourier_double_of_integral_eq (f g : ℝ → ℂ) (hg : Integrable g)
    (hf : Integrable f)
    (hfg : ∀ x : ℝ, f x = ∫ u : ℝ,
      Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (x : ℂ) * (u : ℂ)) * g u)
    (hc : Continuous g) (J : ℝ) :
    (∫ x : ℝ,
      Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (J : ℂ) * (x : ℂ)) * f x) =
      g (-J) := by
  apply integral_fourier_double_of_eq f g hg hf _ hc J
  intro x
  rw [hfg x, fourier_eq_literal_integral]

end GapFamily.Analytic
