import GapFamily.Analytic.Poincare.Fourier.PoincareFourierIndex
import GapFamily.Analytic.Poincare.Fourier.PoincareFourierDenominator

/-! The actual convergent Poincaré Fourier coefficient as its Kloosterman integral series. -/
noncomputable section
namespace GapFamily.Analytic.PoincareFourierRegroup
open Set MeasureTheory PoincareFourier PoincareFourierUnfold
open scoped Topology MatrixGroups

/-- Regrouping the genuinely convergent quotient series gives the actual denominator sum. -/
theorem hasSum_kloosterman_fourier (j J : ℤ) {s : ℂ} (hs : 1 < s.re)
    (y : ℝ) (hy : 0 < y) :
    HasSum (fun n : ℕ => kloostermanSum j J n *
      ∫ t : ℝ, fourierKernel (n + 1 : ℕ) y j J s t)
      ((∫ x in (0 : ℝ)..1, fourierSeries j J s y hy x) -
        (if j = J then (y : ℂ) ^ s else 0)) := by
  exact (hasSum_indexed_fourier_integral j J hs y hy).sigma
    (fun n => hasSum_integral_denominator j J (by linarith : 1 / 2 < s.re) n y hy)

/-- The resulting ordinary integral series converges absolutely in complex norm. -/
theorem summable_norm_kloosterman_fourier (j J : ℤ) {s : ℂ} (hs : 1 < s.re)
    (y : ℝ) (hy : 0 < y) :
    Summable (fun n : ℕ => ‖kloostermanSum j J n *
      ∫ t : ℝ, fourierKernel (n + 1 : ℕ) y j J s t‖) :=
  (hasSum_kloosterman_fourier j J hs y hy).summable.norm

/-- The actual convergent zero-energy spin series has the exact Kloosterman integral
Fourier coefficient, with one diagonal seed and no extra factor one half. -/
theorem complexPoincareSeries_fourier_eq (j J : ℤ) {s : ℂ} (hs : 1 < s.re)
    (y : ℝ) (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1, cuspFourierMode (-j) x *
      complexPoincareSeries 0 J s (rowPoint y hy x)) =
      (if j = J then (y : ℂ) ^ s else 0) +
        ∑' n : ℕ, kloostermanSum j J n *
          ∫ t : ℝ, fourierKernel (n + 1 : ℕ) y j J s t := by
  change (∫ x in (0 : ℝ)..1, fourierSeries j J s y hy x) = _
  rw [(hasSum_kloosterman_fourier j J hs y hy).tsum_eq]
  ring

end GapFamily.Analytic.PoincareFourierRegroup
