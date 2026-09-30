import GapFamily.Analytic.Cusp.Scalar.CuspConstantResponseForm
import GapFamily.Analytic.Cusp.Profile.CuspProfileLaplacianIBP

/-! Ordinary compact-test integration by parts for the actual constant-source response. -/

noncomputable section
namespace GapFamily.Analytic
open MeasureTheory Set
open scoped ContDiff

private theorem support_positive {b : ℝ → ℂ}
    (hs : tsupport b ⊆ Ioi (1 : ℝ)) : tsupport b ⊆ Ioi (0 : ℝ) := by
  intro y hy
  have hy1 : (1 : ℝ) < y := hs hy
  exact lt_trans (by norm_num : (0 : ℝ) < 1) hy1

private theorem compact_factor_integrable {b A g : ℝ → ℂ}
    (hc : HasCompactSupport b) (hs : tsupport b ⊆ Ioi (1 : ℝ))
    (hg : Continuous g) (hA : ContinuousOn A (Ioi (0 : ℝ)))
    (hzero : ∀ y ∉ tsupport b, g y = 0) :
    Integrable (fun y => g y * A y) := by
  have hcont : ContinuousOn (fun y => g y * A y) (tsupport b) :=
    hg.continuousOn.mul (hA.mono (support_positive hs))
  apply (hcont.integrableOn_compact hc).integrable_of_forall_notMem_eq_zero
  intro y hy
  rw [hzero y hy, zero_mul]

private theorem compact_integral_mul_deriv {b A : ℝ → ℂ}
    (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b)
    (hs : tsupport b ⊆ Ioi (1 : ℝ)) (hA : ContDiffOn ℝ ∞ A (Ioi (0 : ℝ))) :
    (∫ y in Ioi (1 : ℝ), star (b y) * deriv A y) =
      -(∫ y in Ioi (1 : ℝ), star (deriv b y) * A y) := by
  have hu : ∀ y, HasDerivAt (fun t => star (b t)) (star (deriv b y)) y :=
    fun y => (hb.differentiable (by simp) y).hasDerivAt.star
  have hsupport : tsupport (fun y => star (b y)) ⊆ tsupport b :=
    tsupport_comp_subset (g := star) (by simp) b
  have hv : ∀ y ∈ tsupport (fun t => star (b t)), HasDerivAt A (deriv A y) y := by
    intro y hy
    have hy0 : y ∈ Ioi (0 : ℝ) := support_positive hs (hsupport hy)
    exact ((hA.differentiableOn (by simp) y hy0).differentiableAt
      (isOpen_Ioi.mem_nhds hy0)).hasDerivAt
  have huv' : Integrable (fun y => star (b y) * deriv A y) := by
    apply compact_factor_integrable hc hs hb.continuous.star
      (hA.continuousOn_deriv_of_isOpen isOpen_Ioi (by simp))
    intro y hy
    rw [image_eq_zero_of_notMem_tsupport hy, star_zero]
  have hu'v : Integrable (fun y => star (deriv b y) * A y) := by
    apply compact_factor_integrable hc hs (hb.continuous_deriv (by simp)).star hA.continuousOn
    intro y hy
    rw [deriv_of_notMem_tsupport hy, star_zero]
  have huv : Integrable (fun y => star (b y) * A y) := by
    apply compact_factor_integrable hc hs hb.continuous.star hA.continuousOn
    intro y hy
    rw [image_eq_zero_of_notMem_tsupport hy, star_zero]
  have hwhole := MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun y _ => hu y) hv huv' hu'v huv
  have hfirst : (∫ y in Ioi (1 : ℝ), star (b y) * deriv A y) =
      ∫ y, star (b y) * deriv A y := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    have hyb : y ∉ tsupport b := fun h => hy (hs h)
    rw [image_eq_zero_of_notMem_tsupport hyb, star_zero, zero_mul]
  have hsecond : (∫ y in Ioi (1 : ℝ), star (deriv b y) * A y) =
      ∫ y, star (deriv b y) * A y := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    have hyb : y ∉ tsupport b := fun h => hy (hs h)
    rw [deriv_of_notMem_tsupport hyb, star_zero, zero_mul]
  rw [hfirst, hsecond]
  exact hwhole

theorem compact_integral_second_deriv_transfer {b A : ℝ → ℂ}
    (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b)
    (hs : tsupport b ⊆ Ioi (1 : ℝ)) (hA : ContDiffOn ℝ ∞ A (Ioi (0 : ℝ))) :
    (∫ y in Ioi (1 : ℝ), star (deriv (deriv b) y) * A y) =
      ∫ y in Ioi (1 : ℝ), star (b y) * deriv (deriv A) y := by
  rw [compact_integral_mul_deriv hb hc hs
    (hA.deriv_of_isOpen isOpen_Ioi (by simp)),
    cuspProfileLaplacian_integral_deriv_mul hb hc hs hA, neg_neg]

theorem cuspConstant_compact_mass_integrable {b : ℝ → ℂ} (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b)
    (hs : tsupport b ⊆ Ioi (1 : ℝ)) {κ : ℂ} (hκ : κ ≠ -(1 / 2 : ℂ)) :
    IntegrableOn (fun y : ℝ =>
      star (b y) * cuspConstantPhysicalResponse κ y / (y : ℂ)^2) (Ioi 1) := by
  have hA : ContinuousOn
      (fun y : ℝ => cuspConstantPhysicalResponse κ y / (y : ℂ)^2) (Ioi 0) :=
    (cuspConstantPhysicalResponse_contDiffOn hκ).continuousOn.div
      (Complex.continuous_ofReal.pow 2).continuousOn
      (fun y hy => pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (ne_of_gt hy)))
  have hi := compact_factor_integrable hc hs hb.continuous.star hA (by
    intro y hy
    rw [image_eq_zero_of_notMem_tsupport hy, star_zero])
  simpa only [mul_div_assoc] using hi.integrableOn (s := Ioi 1)

theorem cuspConstant_compact_source_integrable {b : ℝ → ℂ} (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b)
    (hs : tsupport b ⊆ Ioi (1 : ℝ)) :
    IntegrableOn (fun y : ℝ => star (b y) / (y : ℂ)^2) (Ioi 1) := by
  have hA : ContinuousOn (fun y : ℝ => (1 : ℂ) / (y : ℂ)^2) (Ioi 0) :=
    continuousOn_const.div (Complex.continuous_ofReal.pow 2).continuousOn
      (fun y hy => pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (ne_of_gt hy)))
  have hi := compact_factor_integrable hc hs hb.continuous.star hA (by
    intro y hy
    rw [image_eq_zero_of_notMem_tsupport hy, star_zero])
  simpa only [div_eq_mul_inv, one_mul] using hi.integrableOn (s := Ioi 1)



/-- Every compact scalar test pairs integrably with the actual second derivative. -/
theorem cuspConstant_compact_second_deriv_integrable {b : ℝ → ℂ}
    (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b)
    (hs : tsupport b ⊆ Ioi (1 : ℝ)) {κ : ℂ} (hκ : κ ≠ -(1 / 2 : ℂ)) :
    IntegrableOn (fun y : ℝ => star (b y) *
      deriv (deriv (cuspConstantPhysicalResponse κ)) y) (Ioi 1) := by
  have hA := cuspConstantPhysicalResponse_contDiffOn hκ
  have hd : ContDiffOn ℝ ∞ (deriv (cuspConstantPhysicalResponse κ)) (Ioi 0) :=
    hA.deriv_of_isOpen isOpen_Ioi (by simp)
  have hi := compact_factor_integrable hc hs hb.continuous.star
    (hd.continuousOn_deriv_of_isOpen isOpen_Ioi (by simp)) (by
      intro y hy
      rw [image_eq_zero_of_notMem_tsupport hy, star_zero])
  exact hi.integrableOn

/-- The actual scalar compact-test equation, with derivatives transferred to
the test. It includes the removable parameter and only excludes the true pole. -/
theorem cuspConstantPhysicalResponse_compact_test_weak (b : ℝ → ℂ)
    (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b)
    (hs : tsupport b ⊆ Ioi (1 : ℝ)) {κ : ℂ} (hκ : κ ≠ -(1 / 2 : ℂ)) :
    -(∫ y in Ioi (1 : ℝ), star (deriv (deriv b) y) * cuspConstantPhysicalResponse κ y) -
      (1 / 4 - κ ^ 2) *
        (∫ y in Ioi (1 : ℝ), star (b y) * cuspConstantPhysicalResponse κ y / (y : ℂ)^2) =
      ∫ y in Ioi (1 : ℝ), star (b y) / (y : ℂ)^2 := by
  rw [compact_integral_second_deriv_transfer hb hc hs
    (cuspConstantPhysicalResponse_contDiffOn hκ)]
  have hd := cuspConstant_compact_second_deriv_integrable hb hc hs hκ
  have hm := cuspConstant_compact_mass_integrable hb hc hs hκ
  have hdneg : IntegrableOn (fun y : ℝ =>
      -(star (b y) * deriv (deriv (cuspConstantPhysicalResponse κ)) y)) (Ioi 1) := hd.neg
  calc
    _ = ∫ y in Ioi (1 : ℝ),
        -(star (b y) * deriv (deriv (cuspConstantPhysicalResponse κ)) y) -
          (1 / 4 - κ ^ 2) *
            (star (b y) * cuspConstantPhysicalResponse κ y / (y : ℂ)^2) := by
      rw [integral_sub hdneg (hm.const_mul (1 / 4 - κ ^ 2)),
        integral_neg, integral_const_mul]
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      dsimp only
      have hy1 : (1 : ℝ) < y := hy
      have hy0 : (0 : ℝ) < y := lt_trans (by norm_num : (0 : ℝ) < 1) hy1
      have hyn : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy0.ne'
      have hode := cuspConstantPhysicalResponse_forcedODE hκ hy0
      calc
        _ = star (b y) *
            (-(y : ℂ)^2 * deriv (deriv (cuspConstantPhysicalResponse κ)) y -
              (1 / 4 - κ ^ 2) * cuspConstantPhysicalResponse κ y) / (y : ℂ)^2 := by
          field_simp [hyn]
        _ = _ := by rw [hode, mul_one]


end GapFamily.Analytic
