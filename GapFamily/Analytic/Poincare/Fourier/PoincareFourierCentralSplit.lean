import GapFamily.Analytic.Poincare.Fourier.PoincareFourierCentralFactor
import GapFamily.Analytic.Poincare.Fourier.PoincareFourierRemainderSeries
import GapFamily.Analytic.Poincare.Fourier.PoincareFourierRegroup
import GapFamily.Analytic.Arithmetic.KloostermanDirichlet

/-! The central Dirichlet factor is separated only where all three sums converge. -/
noncomputable section
namespace GapFamily.Analytic.PoincareFourierRemainder
open Set MeasureTheory PoincareFourier PoincareFourierUnfold
open PoincareFourierRegroup

/-- Lawful full denominator summation of the ordinary central-plus-remainder split. -/
theorem hasSum_fourierKernel_central_add_remainder {y : ℝ} (hy : 0 < y)
    (j J : ℤ) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℕ => kloostermanSum j J n *
      ∫ t : ℝ, fourierKernel (n + 1 : ℕ) y j J s t)
      (kloostermanDirichlet j J s * (∫ t : ℝ, centralFourierKernel y j s t) +
        fourierRemainder y j J s) := by
  have hcentral := (kloostermanDirichlet_hasSum_neg_cpow j J hs).mul_right
    (∫ t : ℝ, centralFourierKernel y j s t)
  have hr := hasSum_fourierRemainder hy j J (lt_trans zero_lt_one hs)
  convert hcentral.add hr using 1
  funext n
  rw [integral_fourierKernel_eq_central_add_remainder (by positivity) hy j J (by linarith)]
  simp only [Nat.cast_add, Nat.cast_one, Complex.ofReal_add, Complex.ofReal_natCast,
    Complex.ofReal_one]
  ring

/-- On Re(s)>1, the actual ordinary Fourier coefficient equals its direct term,
the actual Kloosterman Dirichlet series times the central ordinary Fourier factor,
and the absolutely convergent analytic remainder. No threshold separation is made. -/
theorem complexPoincareSeries_fourier_eq_central_add_remainder
    {y : ℝ} (hy : 0 < y) (j J : ℤ) {s : ℂ} (hs : 1 < s.re) :
    (∫ x in (0 : ℝ)..1, cuspFourierMode (-j) x *
      complexPoincareSeries 0 J s (rowPoint y hy x)) =
      (if j = J then (y : ℂ) ^ s else 0) +
        (∫ t : ℝ, centralFourierKernel y j s t) * kloostermanDirichlet j J s +
          fourierRemainder y j J s := by
  have h := (hasSum_kloosterman_fourier j J hs y hy).unique
    (hasSum_fourierKernel_central_add_remainder hy j J hs)
  change (∫ x in (0 : ℝ)..1, cuspFourierMode (-j) x *
      complexPoincareSeries 0 J s (rowPoint y hy x)) -
      (if j = J then (y : ℂ) ^ s else 0) = _ at h
  calc
    _ = (kloostermanDirichlet j J s * (∫ t : ℝ, centralFourierKernel y j s t) +
        fourierRemainder y j J s) + (if j = J then (y : ℂ) ^ s else 0) :=
      sub_eq_iff_eq_add.mp h
    _ = _ := by ring

end GapFamily.Analytic.PoincareFourierRemainder
