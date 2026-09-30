import GapFamily.Analytic.Spatial.SpatialPointKernelBasic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Continuity in real frequency of the ordinary complex cone Laplace integral.
The positive-part base extends the density continuously across the cone edge.
All convergence arguments use a fixed ordinary Gamma--Laplace majorant. -/

noncomputable section
namespace GapFamily.Analytic.SpatialPoint

open Set MeasureTheory Filter
open scoped Topology

/-- The cone density extended by zero across its edge, on positive energy. -/
def pointConePositiveDensity (s : ℂ) (Y J E : ℝ) : ℂ :=
  ((max 0 (E ^ 2 - J ^ 2) : ℝ) : ℂ) ^ (s - 1) *
    Complex.exp ((-2 * Real.pi * Y * E : ℝ) : ℂ)

theorem continuous_pointConePositiveDensity (s : ℂ) (hs : 1 < s.re) (Y : ℝ) :
    Continuous (fun p : ℝ × ℝ => pointConePositiveDensity s Y p.1 p.2) := by
  have hp : 0 < (s - 1).re := by simpa using sub_pos.mpr hs
  exact ((Complex.continuous_ofReal_cpow_const hp).comp
    (by fun_prop : Continuous (fun p : ℝ × ℝ => max 0 (p.2 ^ 2 - p.1 ^ 2)))).mul
      (by fun_prop)

theorem norm_pointConePositiveDensity_le (s : ℂ) (hs : 1 < s.re)
    (Y J E : ℝ) (hE : 0 < E) :
    ‖pointConePositiveDensity s Y J E‖ ≤
      E ^ (2 * (s.re - 1)) * Real.exp (-2 * Real.pi * Y * E) := by
  have hp : 0 < (s - 1).re := by simpa using sub_pos.mpr hs
  rw [pointConePositiveDensity, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_nonneg (le_max_left _ _) hp.ne']
  simp only [Complex.sub_re, Complex.one_re, Complex.norm_exp, Complex.ofReal_re]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  calc
    (max 0 (E ^ 2 - J ^ 2)) ^ (s.re - 1) ≤ (E ^ 2) ^ (s.re - 1) :=
      Real.rpow_le_rpow (le_max_left _ _)
        (max_le (sq_nonneg E) (by nlinarith [sq_nonneg J])) (by linarith)
    _ = E ^ (2 * (s.re - 1)) := by
      rw [← Real.rpow_two, ← Real.rpow_mul hE.le]

theorem integrableOn_pointConePositiveDensity_majorant (s : ℂ) (hs : 1 < s.re)
    (Y : ℝ) (hY : 0 < Y) :
    IntegrableOn (fun E : ℝ =>
      E ^ (2 * (s.re - 1)) * Real.exp (-2 * Real.pi * Y * E)) (Ioi 0) := by
  simpa only [Real.rpow_one, neg_mul] using
    (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 2 * (s.re - 1))
      (b := 2 * Real.pi * Y) (by linarith) zero_lt_one (by positivity))

theorem integrableOn_pointConePositiveDensity (s : ℂ) (hs : 1 < s.re)
    (Y : ℝ) (hY : 0 < Y) (J : ℝ) :
    IntegrableOn (pointConePositiveDensity s Y J) (Ioi 0) := by
  apply (integrableOn_pointConePositiveDensity_majorant s hs Y hY).mono'
  · exact ((continuous_pointConePositiveDensity s hs Y).comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with E hE
    exact norm_pointConePositiveDensity_le s hs Y J E hE

theorem integral_pointConePositiveDensity_eq (s : ℂ) (hs : 1 < s.re) (Y J : ℝ) :
    (∫ E : ℝ in Ioi 0, pointConePositiveDensity s Y J E) =
      ∫ E : ℝ in Ioi |J|, ((E ^ 2 - J ^ 2 : ℝ) : ℂ) ^ (s - 1) *
        Complex.exp ((-2 * Real.pi * Y * E : ℝ) : ℂ) := by
  have hp : s - 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at this
    linarith
  have hsub : Ioi |J| ⊆ Ioi (0 : ℝ) := fun E hE => (abs_nonneg J).trans_lt hE
  rw [← inter_eq_right.mpr hsub, ← setIntegral_indicator measurableSet_Ioi]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro E hE
  change 0 < E at hE
  by_cases hcone : |J| < E
  · have hbase : 0 ≤ E ^ 2 - J ^ 2 := by
      nlinarith [sq_abs J, (sq_lt_sq₀ (abs_nonneg J) hE.le).mpr hcone]
    simp [pointConePositiveDensity, max_eq_right hbase, hcone]
  · have hbase : E ^ 2 - J ^ 2 ≤ 0 := by
      have hle : E ≤ |J| := le_of_not_gt hcone
      nlinarith [sq_abs J, sq_nonneg (|J| - E)]
    simp [pointConePositiveDensity, max_eq_left hbase, hcone, Complex.zero_cpow hp]

/-- The ordinary cone Fourier density is continuous at every real frequency,
including zero, by dominated convergence on a fixed integration domain. -/
theorem continuous_pointConeFrequencyIntegral (s : ℂ) (hs : 1 < s.re)
    (Y : ℝ) (hY : 0 < Y) :
    Continuous (fun J : ℝ => ∫ E : ℝ in Ioi |J|,
      ((E ^ 2 - J ^ 2 : ℝ) : ℂ) ^ (s - 1) *
        Complex.exp ((-2 * Real.pi * Y * E : ℝ) : ℂ)) := by
  simp_rw [← integral_pointConePositiveDensity_eq s hs Y]
  apply continuous_of_dominated
    (bound := fun E : ℝ => E ^ (2 * (s.re - 1)) * Real.exp (-2 * Real.pi * Y * E))
  · intro J
    exact (integrableOn_pointConePositiveDensity s hs Y hY J).aestronglyMeasurable
  · intro J
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with E hE
    exact norm_pointConePositiveDensity_le s hs Y J E hE
  · exact integrableOn_pointConePositiveDensity_majorant s hs Y hY
  · apply Eventually.of_forall
    intro E
    exact (continuous_pointConePositiveDensity s hs Y).comp
      (continuous_id.prodMk continuous_const)

end GapFamily.Analytic.SpatialPoint
