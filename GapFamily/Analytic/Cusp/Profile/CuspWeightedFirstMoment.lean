import GapFamily.Analytic.Cusp.Profile.CuspHalfLineLaplacePairingBound

/-!
# Genuine weighted first moments of half-line L2 vectors

The first-moment weight is dominated by a slower exponential. Ordinary L2
Holder bounds then give both integrability and an explicit finite norm bound.
-/

noncomputable section
namespace GapFamily.Analytic.CuspWeightedFirstMoment

open Set Filter MeasureTheory CuspHalfLineLaplace

private theorem norm_square_integral (f : HalfLineL2) :
    (∫ u : ℝ in Ioi 0, ‖f u‖ ^ 2) = ‖f‖ ^ 2 := by
  symm
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

private theorem norm_product_integral_le (g f : HalfLineL2) :
    (∫ u : ℝ in Ioi 0, ‖g u‖ * ‖f u‖) ≤ ‖g‖ * ‖f‖ := by
  have h := integral_mul_norm_le_Lp_mul_Lq (p := 2) (q := 2)
    (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩ : Real.HolderConjugate 2 2)
    (by simpa using Lp.memLp g) (by simpa using Lp.memLp f)
  simpa only [Real.rpow_two, norm_square_integral, ← Real.sqrt_eq_rpow,
    Real.sqrt_sq (norm_nonneg g), Real.sqrt_sq (norm_nonneg f)] using h

private theorem exponential_norm_ae {α : ℝ} (hα : 0 < α) :
    (fun u : ℝ => ‖exponential (α : ℂ) u‖) =ᵐ[volume.restrict (Ioi 0)]
      (fun u => Real.exp (-α * u)) := by
  filter_upwards [exponential_ae (by simpa using hα : 0 < (α : ℂ).re)] with u hu
  rw [hu, Complex.norm_exp]
  simp

/-- The actual exponential norm pairing is an ordinary convergent integral. -/
theorem exponential_norm_product_integrable {α : ℝ} (hα : 0 < α) (f : HalfLineL2) :
    IntegrableOn (fun u : ℝ => Real.exp (-α * u) * ‖f u‖) (Ioi 0) := by
  have hi := (Lp.memLp (exponential (α : ℂ))).norm.integrable_mul (Lp.memLp f).norm
  apply hi.congr
  filter_upwards [exponential_norm_ae hα] with u hu
  change ‖exponential (α : ℂ) u‖ * ‖f u‖ = _
  rw [hu]

/-- Ordinary L2 Holder for the literal positive exponential weight. -/
theorem exponential_norm_product_integral_le {α : ℝ} (hα : 0 < α) (f : HalfLineL2) :
    (∫ u : ℝ in Ioi 0, Real.exp (-α * u) * ‖f u‖) ≤
      ‖exponential (α : ℂ)‖ * ‖f‖ := by
  have he : (∫ u : ℝ in Ioi 0, Real.exp (-α * u) * ‖f u‖) =
      ∫ u : ℝ in Ioi 0, ‖exponential (α : ℂ) u‖ * ‖f u‖ := by
    apply integral_congr_ae
    filter_upwards [exponential_norm_ae hα] with u hu
    rw [hu]
  rw [he]
  exact norm_product_integral_le _ _

/-- A slower exponential controls the full first-moment weight. -/
theorem firstMoment_weight_le {α : ℝ} (hα : 0 < α) (u : ℝ) :
    u * Real.exp (-α * u) ≤ (2 / α) * Real.exp (-(α / 2) * u) := by
  have hle : ((α / 2) * u) * Real.exp (-((α / 2) * u)) ≤ 1 :=
    (Real.mul_exp_neg_le_exp_neg_one _).trans
      (Real.exp_le_one_iff.mpr (by norm_num))
  have hfactor : u * Real.exp (-(α / 2) * u) ≤ 2 / α := by
    apply (le_div_iff₀ hα).mpr
    calc
      _ = 2 * (((α / 2) * u) * Real.exp (-((α / 2) * u))) := by
        rw [neg_mul]
        ring
      _ ≤ 2 * 1 := mul_le_mul_of_nonneg_left hle (by norm_num)
      _ = 2 := by ring
  calc
    _ = (u * Real.exp (-(α / 2) * u)) * Real.exp (-(α / 2) * u) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hfactor (Real.exp_nonneg _)

/-- The literal weighted first moment of every actual half-line L2 vector is integrable. -/
theorem firstMoment_integrable {α : ℝ} (hα : 0 < α) (f : HalfLineL2) :
    IntegrableOn (fun u : ℝ => u * Real.exp (-α * u) * ‖f u‖) (Ioi 0) := by
  have hi := (exponential_norm_product_integrable (half_pos hα) f).const_mul (2 / α)
  apply hi.mono'
  · exact (by fun_prop : Continuous (fun u : ℝ => u * Real.exp (-α * u))).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable f).norm
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := hu
    rw [Real.norm_of_nonneg (by positivity)]
    exact (mul_le_mul_of_nonneg_right (firstMoment_weight_le hα u) (norm_nonneg _)).trans_eq
      (mul_assoc _ _ _)

/-- Explicit finite bound for the genuine ordinary weighted first moment. -/
theorem firstMoment_integral_le {α : ℝ} (hα : 0 < α) (f : HalfLineL2) :
    (∫ u : ℝ in Ioi 0, u * Real.exp (-α * u) * ‖f u‖) ≤
      ((2 / α) * ‖exponential ((α / 2 : ℝ) : ℂ)‖) * ‖f‖ := by
  have hi := firstMoment_integrable hα f
  have hmajor := (exponential_norm_product_integrable (half_pos hα) f).const_mul (2 / α)
  calc
    _ ≤ ∫ u : ℝ in Ioi 0, (2 / α) * (Real.exp (-(α / 2) * u) * ‖f u‖) := by
      apply integral_mono_ae hi hmajor
      exact Eventually.of_forall fun u =>
        (mul_le_mul_of_nonneg_right (firstMoment_weight_le hα u) (norm_nonneg _)).trans_eq
          (mul_assoc _ _ _)
    _ = (2 / α) * ∫ u : ℝ in Ioi 0, Real.exp (-(α / 2) * u) * ‖f u‖ := integral_const_mul _ _
    _ ≤ (2 / α) * (‖exponential ((α / 2 : ℝ) : ℂ)‖ * ‖f‖) :=
      mul_le_mul_of_nonneg_left (exponential_norm_product_integral_le (half_pos hα) f)
        (by positivity)
    _ = _ := (mul_assoc _ _ _).symm

theorem firstMoment_constant_pos {α : ℝ} (hα : 0 < α) :
    0 < (2 / α) * ‖exponential ((α / 2 : ℝ) : ℂ)‖ := by
  have hs := exponential_norm_sq (by simpa using half_pos hα :
    0 < (((α / 2 : ℝ) : ℂ)).re)
  have hn : 0 < ‖exponential ((α / 2 : ℝ) : ℂ)‖ := by
    have hi : 0 < α⁻¹ := inv_pos.mpr hα
    have he : 2 * (((α / 2 : ℝ) : ℂ)).re = α := by
      rw [Complex.ofReal_re]
      ring
    rw [he] at hs
    nlinarith [norm_nonneg (exponential ((α / 2 : ℝ) : ℂ))]
  exact mul_pos (by positivity) hn

end GapFamily.Analytic.CuspWeightedFirstMoment
