import GapFamily.Analytic.Spatial.SpatialPointFourierLaplace
import GapFamily.Analytic.Spatial.SpatialIntegrableSeries

/-! Ordinary same-parameter Laplace superposition of the actual cusp-coset
Poincaré series. The energy integral and coset sum genuinely converge before
they are exchanged. -/

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open Set MeasureTheory PoincareFourier

theorem norm_physical_complexPoincareTerm_le (s : ℂ) (J : ℤ)
    (z : UpperHalfPlane) (q : CuspCoset) {E : ℝ} (hE : 0 ≤ E) :
    ‖complexPoincareTerm E J s z q‖ ≤ (q.out • z).im ^ s.re := by
  rw [complexPoincareTerm_out, norm_complexPointSeed, Complex.ofReal_re]
  apply mul_le_of_le_one_right (Real.rpow_nonneg (q.out • z).im_pos.le _)
  apply Real.exp_le_one_iff.mpr
  have hn : 0 ≤ 2 * Real.pi * E * (q.out • z).im := by positivity
  linarith

theorem norm_pointFourierLaplaceDensity_mul_term_le (s : ℂ) (Y : ℝ) (J : ℤ)
    (z : UpperHalfPlane) (q : CuspCoset) {E : ℝ} (hE : |(J : ℝ)| < E) :
    ‖pointFourierLaplaceDensity s Y J E * complexPoincareTerm E J s z q‖ ≤
      (q.out • z).im ^ s.re * ‖pointFourierLaplaceDensity s Y J E‖ := by
  rw [norm_mul, mul_comm ((q.out • z).im ^ s.re)]
  exact mul_le_mul_of_nonneg_left
    (norm_physical_complexPoincareTerm_le s J z q ((abs_nonneg _).trans hE.le))
    (norm_nonneg _)

theorem integrableOn_pointFourierLaplaceDensity_mul_term (s : ℂ) (hs : 1 < s.re)
    (Y : ℝ) (hY : 0 < Y) (J : ℤ) (z : UpperHalfPlane) (q : CuspCoset) :
    IntegrableOn (fun E : ℝ => pointFourierLaplaceDensity s Y J E *
      complexPoincareTerm E J s z q) (Ioi |(J : ℝ)|) := by
  have hI := integrableOn_pointFourierLaplaceDensity hs hY (J : ℝ)
  apply (hI.norm.const_mul ((q.out • z).im ^ s.re)).mono'
  · exact hI.aestronglyMeasurable.mul
      (((differentiable_complexPoincareTerm_energy J s z q).continuous.comp
        Complex.continuous_ofReal).aestronglyMeasurable)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with E hE
    exact norm_pointFourierLaplaceDensity_mul_term_le s Y J z q hE

theorem summable_integral_norm_pointFourierLaplaceDensity_mul_term
    (s : ℂ) (hs : 1 < s.re) (Y : ℝ) (hY : 0 < Y) (J : ℤ) (z : UpperHalfPlane) :
    Summable (fun q : CuspCoset => ∫ E : ℝ in Ioi |(J : ℝ)|,
      ‖pointFourierLaplaceDensity s Y J E * complexPoincareTerm E J s z q‖) := by
  have hI := integrableOn_pointFourierLaplaceDensity hs hY (J : ℝ)
  apply ((summable_cusp_height hs z).mul_right
    (∫ E : ℝ in Ioi |(J : ℝ)|, ‖pointFourierLaplaceDensity s Y J E‖)).of_nonneg_of_le
    (fun q => integral_nonneg fun _ => norm_nonneg _) (fun q => ?_)
  rw [← integral_const_mul]
  apply integral_mono_ae
    (integrableOn_pointFourierLaplaceDensity_mul_term s hs Y hY J z q).norm
    (hI.norm.const_mul _)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with E hE
  exact norm_pointFourierLaplaceDensity_mul_term_le s Y J z q hE

theorem hasSum_integral_pointFourierLaplaceDensity_mul_term
    (s : ℂ) (hs : 1 < s.re) (Y : ℝ) (hY : 0 < Y) (J : ℤ) (z : UpperHalfPlane) :
    HasSum (fun q : CuspCoset => ∫ E : ℝ in Ioi |(J : ℝ)|,
      pointFourierLaplaceDensity s Y J E * complexPoincareTerm E J s z q)
      (∫ E : ℝ in Ioi |(J : ℝ)|,
        pointFourierLaplaceDensity s Y J E * complexPoincareSeries E J s z) := by
  let : Countable CuspCoset := cuspBottomRow_injective.countable
  have h := hasSum_integral_of_summable_integral_norm
    (fun q => integrableOn_pointFourierLaplaceDensity_mul_term s hs Y hY J z q)
    (summable_integral_norm_pointFourierLaplaceDensity_mul_term s hs Y hY J z)
  simpa only [tsum_mul_left, complexPoincareSeries] using h

/-- The full actual Poincaré series has an ordinary input-energy Laplace
integral with this same parameter. -/
theorem integrableOn_pointFourierLaplaceDensity_mul_series
    (s : ℂ) (hs : 1 < s.re) (Y : ℝ) (hY : 0 < Y) (J : ℤ) (z : UpperHalfPlane) :
    IntegrableOn (fun E : ℝ => pointFourierLaplaceDensity s Y J E *
      complexPoincareSeries E J s z) (Ioi |(J : ℝ)|) := by
  let : Countable CuspCoset := cuspBottomRow_injective.countable
  have h := integrable_tsum_of_summable_integral_norm
    (fun q => integrableOn_pointFourierLaplaceDensity_mul_term s hs Y hY J z q)
    (summable_integral_norm_pointFourierLaplaceDensity_mul_term s hs Y hY J z)
  simpa only [tsum_mul_left, complexPoincareSeries, IntegrableOn] using h

theorem pointFourierLaplaceDensity_mul_pointSeed (s : ℂ) (Y : ℝ) (J : ℤ)
    (w : UpperHalfPlane) (E : ℝ) :
    pointFourierLaplaceDensity s Y J E * complexPointSeed E J s w =
      (w.im : ℂ) ^ s * cuspFourierMode J w.re *
        pointFourierLaplaceDensity s (Y + w.im) J E := by
  unfold pointFourierLaplaceDensity complexPointSeed cuspFourierMode
  simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_neg,
    Complex.ofReal_ofNat, Complex.ofReal_intCast]
  rw [Complex.exp_add]
  have he : -2 * (Real.pi : ℂ) * ((Y : ℂ) + (w.im : ℂ)) * (E : ℂ) =
      -2 * (Real.pi : ℂ) * (Y : ℂ) * (E : ℂ) +
        (-2 * (Real.pi : ℂ) * (E : ℂ) * (w.im : ℂ)) := by ring
  have hp : 2 * (Real.pi : ℂ) * (J : ℂ) * (w.re : ℂ) * Complex.I =
      2 * (Real.pi : ℂ) * Complex.I * (J : ℂ) * (w.re : ℂ) := by ring
  rw [he, Complex.exp_add, hp]
  ring

/-- A source-coordinate Fourier coefficient of the ordinary point kernel
is exactly the same-parameter point-seed Laplace integral. -/
theorem pointKernel_source_fourier_eq_pointSeed_laplace (s : ℂ) (hs : 1 < s.re)
    (Y : ℝ) (hY : 0 < Y) (w : UpperHalfPlane) (J : ℤ) :
    (∫ x : ℝ, cuspFourierMode J x * pointKernel s (rowPoint Y hY x) w) =
      spatialLaplaceConstantComplex s * (Y : ℂ) ^ s *
        ∫ E : ℝ in Ioi |(J : ℝ)|,
          pointFourierLaplaceDensity s Y J E * complexPointSeed E J s w := by
  have hf := pointKernel_fourier_eq_laplace s hs Y hY w (-J)
  have hd (E : ℝ) : pointFourierLaplaceDensity s (Y + w.im) (-J) E =
      pointFourierLaplaceDensity s (Y + w.im) J E := by
    simp only [pointFourierLaplaceDensity, neg_sq]
  simp only [neg_neg, Int.cast_neg, abs_neg, hd] at hf
  rw [hf]
  simp_rw [pointFourierLaplaceDensity_mul_pointSeed]
  rw [integral_const_mul, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg hY.le w.im_pos.le]
  ring

end GapFamily.Analytic.SpatialPoint
