import GapFamily.Analytic.Spatial.SpatialOrbitFourierUnfold
import GapFamily.Analytic.Spatial.SpatialPoincareLaplace
import GapFamily.Analytic.Poincare.Fourier.PoincareLaplaceDifference

/-! The actual spatial orbit kernel and actual Poincaré series have the same
Fourier–Laplace parameter. The scalar point Fourier transform, orbit regrouping,
and all ordinary interchanges are proved. The source height difference exposes
the endpoint regularizer.
-/

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open Set MeasureTheory PoincareFourier PoincareEnergyFourier

/-- The actual orbit source Fourier coefficient equals an ordinary input
energy integral of the actual Poincaré series at the same complex parameter. -/
theorem spatialOrbitKernel_fourier_eq_poincare_laplace
    (s : ℂ) (hs : 1 < s.re) (J : ℤ) (z : UpperHalfPlane) (Y : ℝ) (hY : 0 < Y) :
    (∫ x : ℝ in 0..1, cuspFourierMode J x * spatialOrbitKernel s z (rowPoint Y hY x)) =
      spatialLaplaceConstantComplex s * (Y : ℂ) ^ s *
        ∫ E : ℝ in Ioi |(J : ℝ)|,
          pointFourierLaplaceDensity s Y J E * complexPoincareSeries E J s z := by
  rw [spatialOrbitKernel_fourier_unfold J s hs z Y hY]
  simp_rw [pointKernel_source_fourier_eq_pointSeed_laplace s hs Y hY]
  rw [tsum_mul_left]
  congr 1
  rw [← (hasSum_integral_pointFourierLaplaceDensity_mul_term s hs Y hY J z).tsum_eq]
  simp only [complexPoincareTerm_out]

/-- The normalized source height difference of the actual spatial orbit
Fourier coefficient. The normalization depends on the same parameter `s`. -/
def spatialOrbitSourceHeightDifference (s : ℂ) (J : ℤ) (l : ℕ) (z : UpperHalfPlane) : ℂ :=
  (∫ x : ℝ in 0..1, cuspFourierMode J x *
    spatialOrbitKernel s z (laplacePoint l x)) / (laplaceHeight l : ℂ) ^ s -
  (∫ x : ℝ in 0..1, cuspFourierMode J x *
    spatialOrbitKernel s z (laplacePoint (l + 1) x)) / (laplaceHeight (l + 1) : ℂ) ^ s

theorem pointFourierLaplaceDensity_height_difference (s : ℂ) (J : ℤ) (l : ℕ) (E : ℝ) :
    pointFourierLaplaceDensity s (laplaceHeight l) J E -
      pointFourierLaplaceDensity s (laplaceHeight (l + 1)) J E =
        ((E ^ 2 - (J : ℝ) ^ 2 : ℝ) : ℂ) ^ (s - 1) * (laplaceTest l E : ℂ) := by
  rw [laplaceTest_complex_eq_height_difference]
  unfold pointFourierLaplaceDensity
  push_cast
  rw [mul_sub]

/-- The input height difference has a genuinely integrable energy density
before continuation; it is the same regularizer used by the threshold pairing.
-/
theorem integrableOn_poincare_laplaceTest (s : ℂ) (hs : 1 < s.re)
    (J : ℤ) (l : ℕ) (z : UpperHalfPlane) :
    IntegrableOn (fun E : ℝ =>
      ((E ^ 2 - (J : ℝ) ^ 2 : ℝ) : ℂ) ^ (s - 1) * (laplaceTest l E : ℂ) *
        complexPoincareSeries E J s z) (Ioi |(J : ℝ)|) := by
  have h := (integrableOn_pointFourierLaplaceDensity_mul_series s hs _
    (laplaceHeight_pos l) J z).sub
      (integrableOn_pointFourierLaplaceDensity_mul_series s hs _
        (laplaceHeight_pos (l + 1)) J z)
  convert h using 1
  ext E
  rw [← pointFourierLaplaceDensity_height_difference]
  exact sub_mul _ _ _

/-- The actual spatial source Fourier/height test equals the actual
regularized Poincaré Laplace integral throughout `Re s > 1`. -/
theorem spatialOrbitSourceHeightDifference_eq_poincare_laplaceTest
    (s : ℂ) (hs : 1 < s.re) (J : ℤ) (l : ℕ) (z : UpperHalfPlane) :
    spatialOrbitSourceHeightDifference s J l z =
      spatialLaplaceConstantComplex s *
        ∫ E : ℝ in Ioi |(J : ℝ)|,
          ((E ^ 2 - (J : ℝ) ^ 2 : ℝ) : ℂ) ^ (s - 1) * (laplaceTest l E : ℂ) *
            complexPoincareSeries E J s z := by
  have hp (n : ℕ) (x : ℝ) :
      laplacePoint n x = rowPoint (laplaceHeight n) (laplaceHeight_pos n) x := rfl
  unfold spatialOrbitSourceHeightDifference
  simp_rw [hp]
  rw [spatialOrbitKernel_fourier_eq_poincare_laplace s hs,
    spatialOrbitKernel_fourier_eq_poincare_laplace s hs]
  have hn (n : ℕ) : (laplaceHeight n : ℂ) ^ s ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr
      (Or.inl (Complex.ofReal_ne_zero.mpr (laplaceHeight_pos n).ne'))
  have hcancel (a b : ℂ) {h : ℂ} (hh : h ≠ 0) : a * h * b / h = a * b := by
    field_simp
  rw [hcancel _ _ (hn l), hcancel _ _ (hn (l + 1)), ← mul_sub]
  congr 1
  rw [← integral_sub
    (integrableOn_pointFourierLaplaceDensity_mul_series s hs _ (laplaceHeight_pos l) J z)
    (integrableOn_pointFourierLaplaceDensity_mul_series s hs _ (laplaceHeight_pos (l + 1)) J z)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun E => by
    dsimp only
    rw [← sub_mul, pointFourierLaplaceDensity_height_difference]

end GapFamily.Analytic.SpatialPoint
