import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section
namespace GapFamily.Analytic.PoincareFourierRemainder
open Set MeasureTheory Filter
open scoped Topology

private theorem radialPrimitive_hasDerivAt {y σ : ℝ} (hy : 0 < y) (hσ : 0 < σ)
    (t : ℝ) :
    HasDerivAt (fun t : ℝ => -(t ^ 2 + y ^ 2) ^ (-σ) / (2 * σ))
      (t * (t ^ 2 + y ^ 2) ^ (-σ - 1)) t := by
  have hd := (((hasDerivAt_id t).pow 2).add_const (y ^ 2)).rpow_const
    (p := -σ) (Or.inl (by positivity : t ^ 2 + y ^ 2 ≠ 0))
  convert hd.neg.div_const (2 * σ) using 1 <;> dsimp
  field_simp [hσ.ne']

private theorem radialPrimitive_tendsto {y σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun t : ℝ => -(t ^ 2 + y ^ 2) ^ (-σ) / (2 * σ)) atTop (𝓝 0) := by
  have ht : Tendsto (fun t : ℝ => t ^ 2 + y ^ 2) atTop atTop :=
    tendsto_atTop_mono (fun t => le_add_of_nonneg_right (sq_nonneg y))
      (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0))
  have h := ((tendsto_rpow_neg_atTop hσ).comp ht).neg.div_const (2 * σ)
  simpa using h

theorem integrableOn_mul_quadratic_rpow_Ioi {y σ : ℝ} (hy : 0 < y) (hσ : 0 < σ) :
    IntegrableOn (fun t : ℝ => t * (t ^ 2 + y ^ 2) ^ (-σ - 1)) (Ioi 0) := by
  apply integrableOn_Ioi_deriv_of_nonneg'
    (fun t _ => radialPrimitive_hasDerivAt hy hσ t)
  · intro t ht
    exact mul_nonneg ht.le (Real.rpow_nonneg (by positivity) _)
  · exact radialPrimitive_tendsto hσ

theorem integral_mul_quadratic_rpow_Ioi {y σ : ℝ} (hy : 0 < y) (hσ : 0 < σ) :
    (∫ t : ℝ in Ioi 0, t * (t ^ 2 + y ^ 2) ^ (-σ - 1)) =
      (y ^ 2) ^ (-σ) / (2 * σ) := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg'
    (fun t (_ : t ∈ Ici (0 : ℝ)) => radialPrimitive_hasDerivAt hy hσ t)
    (fun t (ht : t ∈ Ioi (0 : ℝ)) =>
      mul_nonneg ht.le (Real.rpow_nonneg (by positivity) _) : ∀ t ∈ Ioi (0 : ℝ),
      0 ≤ t * (t ^ 2 + y ^ 2) ^ (-σ - 1)) (radialPrimitive_tendsto hσ)
  simpa [neg_div] using h


private theorem integrable_of_even_integrableOn_Ioi
    {f : ℝ → ℝ} (heven : ∀ x, f (-x) = f x)
    (hf : IntegrableOn f (Ioi 0)) : Integrable f := by
  have hleft : IntegrableOn f (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp_rw [Function.comp_def, heven, neg_preimage, neg_Iic, neg_zero]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hf
  have hall := hleft.union hf
  simpa only [Iic_union_Ioi, integrableOn_univ] using hall

private theorem integral_of_even_integrableOn_Ioi
    {f : ℝ → ℝ} (heven : ∀ x, f (-x) = f x)
    (hf : IntegrableOn f (Ioi 0)) :
    (∫ x : ℝ, f x) = 2 * ∫ x in Ioi (0 : ℝ), f x := by
  have hall := integrable_of_even_integrableOn_Ioi heven hf
  have hleft : (∫ x in Iic (0 : ℝ), f x) = ∫ x in Ioi (0 : ℝ), f x := by
    simpa only [heven, neg_zero] using integral_comp_neg_Iic 0 f
  calc
    (∫ x : ℝ, f x) = (∫ x in Iic (0 : ℝ), f x) + ∫ x in Ioi (0 : ℝ), f x := by
      simpa only [compl_Iic] using (integral_add_compl measurableSet_Iic hall).symm
    _ = 2 * ∫ x in Ioi (0 : ℝ), f x := by rw [hleft, two_mul]

/-- The phase-subtracted radial majorant is genuinely integrable for every positive exponent. -/
theorem integrable_abs_mul_quadratic_rpow {y σ : ℝ} (hy : 0 < y) (hσ : 0 < σ) :
    Integrable (fun t : ℝ => |t| * (t ^ 2 + y ^ 2) ^ (-σ - 1)) volume := by
  apply integrable_of_even_integrableOn_Ioi (fun t => by simp only [abs_neg, neg_sq])
  apply (integrableOn_mul_quadratic_rpow_Ioi hy hσ).congr_fun
  · intro t ht
    simp only [abs_of_pos (show 0 < t from ht)]
  · exact measurableSet_Ioi

/-- Exact full-line mass, including the height scaling, for the radial remainder majorant. -/
theorem integral_abs_mul_quadratic_rpow {y σ : ℝ} (hy : 0 < y) (hσ : 0 < σ) :
    (∫ t : ℝ, |t| * (t ^ 2 + y ^ 2) ^ (-σ - 1)) = y ^ (-2 * σ) / σ := by
  have hhalf : IntegrableOn (fun t : ℝ => |t| * (t ^ 2 + y ^ 2) ^ (-σ - 1)) (Ioi 0) :=
    (integrable_abs_mul_quadratic_rpow hy hσ).integrableOn
  rw [integral_of_even_integrableOn_Ioi (fun t => by simp only [abs_neg, neg_sq]) hhalf]
  have hcongr : (∫ t : ℝ in Ioi 0, |t| * (t ^ 2 + y ^ 2) ^ (-σ - 1)) =
      ∫ t : ℝ in Ioi 0, t * (t ^ 2 + y ^ 2) ^ (-σ - 1) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    simp only [abs_of_pos (show 0 < t from ht)]
  rw [hcongr, integral_mul_quadratic_rpow_Ioi hy hσ,
    ← Real.rpow_natCast_mul hy.le 2 (-σ)]
  norm_num
  field_simp

end GapFamily.Analytic.PoincareFourierRemainder
