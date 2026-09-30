import GapFamily.Analytic.Cusp.Scalar.CuspScalarUpperProfile
import GapFamily.Analytic.Poincare.Threshold.PoincareThresholdHeightBridge
import GapFamily.Analytic.Cusp.Threshold.CuspConstrainedPointBound

noncomputable section
namespace GapFamily.Analytic.PoincareThresholdCuspBound
open Set Filter MeasureTheory UpperHalfPlane ModularGradient
  PoincareCanonical PoincareHighCusp PoincareThresholdSchurValue
  CuspThresholdScalar CuspScalarUpperProfile CuspConstrainedThreshold
  CuspConstrainedPointBound CuspUniformBump FixedPoissonPointBound
open scoped Topology ContDiff

/-- The actual high-cusp lift at threshold has its expected square-root bound. -/
theorem norm_continuedHighCusp_zero_le_sqrt (J : ℤ) (τ : UpperHalfPlane)
    (hτ : 1 / 2 < τ.im) : ‖continuedHighCusp J 0 τ‖ ≤ Real.sqrt τ.im := by
  rw [continuedHighCusp_eq_of_half_lt_im J 0 hτ, norm_mul, norm_complexPointSeed]
  have he : (CuspFourierCutoff.exponent (0 : ℂ)).re = (1 / 2 : ℝ) := by
    norm_num [CuspFourierCutoff.exponent]
  rw [he]
  simp only [Complex.zero_re, mul_zero, zero_mul, Real.exp_zero, mul_one,
    Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (show 0 ≤ CuspFourierCutoff.cutoff τ.im from Real.smoothTransition.nonneg _),
    Real.rpow_div_two_eq_sqrt 1 τ.im_pos.le]
  simpa only [one_mul, pow_one, Real.rpow_one] using mul_le_mul_of_nonneg_right
    (show CuspFourierCutoff.cutoff τ.im ≤ 1 from Real.smoothTransition.le_one _) (Real.sqrt_nonneg τ.im)

/-- The canonical remainder after its actual high and scalar components satisfies
one uniform constrained point estimate, including charts crossing the side seams. -/
theorem exists_threshold_remainder_bound :
    ∃ A : ℝ, 0 < A ∧ ∀ (J : ℤ) (p : ℂ), |p.re| ≤ (1 / 2 : ℝ) → 2 ≤ p.im →
      ‖thresholdSeed J (ofComplex p) - continuedHighCusp J 0 p -
        Real.sqrt p.im • scalarProfile (1 / 4) (by norm_num)
          (cuspPoincareResidualSource J (1 / 4) (by norm_num) 0) (Real.log p.im)‖ ≤
        A * ‖cuspPoincareResidualSource J (1 / 4) (by norm_num) 0‖ := by
  obtain ⟨A, hA, hpoint⟩ := exists_constrained_point_bound (1 / 4) (by norm_num)
  refine ⟨A, hA, ?_⟩
  intro J p hp hpy
  let χ := bump p
  let U : Set ℂ := {z : ℂ | z - p ∈ referenceSquare}
  let F := cuspPoincareResidualSource J (1 / 4) (by norm_num) 0
  let g : ℂ → ℂ := fun z => thresholdSeed J (ofComplex z) - continuedHighCusp J 0 z -
    Real.sqrt z.im • scalarProfile (1 / 4) (by norm_num) F (Real.log z.im)
  have hχ := contDiff_bump p
  have hc := hasCompactSupport_bump p
  have hs := tsupport_bump_subset_upperHalfPlane hpy
  have hU := isOpen_translatedReferenceSquare p
  have hχU := bump_eq_one_on_referenceSquare p
  have hhigh := translatedReferenceSquare_subset_high hpy
  obtain ⟨L, hL, hBL, hAbs, hAE⟩ :=
    exists_thresholdResidual_ae_constrained_scalar_of_lower_height χ hχ hc hs U hU hχU J
      (Real.log (p.im + 1))
  have hcap : ∀ z ∈ U, z.im ≤ Real.exp L := by
    intro z hz
    have hz' : |(z - p).im| < (1 / 4 : ℝ) := hz.2
    have hh : z.im ≤ p.im + 1 := by
      simp only [Complex.sub_im] at hz'
      linarith [(abs_lt.mp hz').2]
    calc
      z.im ≤ p.im + 1 := hh
      _ = Real.exp (Real.log (p.im + 1)) := (Real.exp_log (by linarith)).symm
      _ ≤ Real.exp L := Real.exp_le_exp.mpr hBL
  have hscalar := ae_restrict_of_ae (s := U)
    (upperCutoff_scalarOutput_ae_high χ hχ hc hs (by norm_num : (0 : ℝ) < 1 / 4)
      hL hL le_rfl hAbs F)
  have hga : g =ᵐ[volume.restrict U]
      (upperCutoffValueOperator χ hχ hc hs (constrainedForm (1 / 4) (by norm_num) F : FormDomain)) := by
    have hform := upperCutoffHilbertValueOperator_formEmbedding χ hχ hc hs
      (constrainedForm (1 / 4) (by norm_num) F : FormDomain)
    filter_upwards [hAE, hscalar, ae_restrict_mem hU.measurableSet] with z hz hsz hzU
    have hs' := hsz (hhigh hzU) (hcap z hzU)
    have hχz : χ z = 1 := hχU hzU
    rw [hχz, one_mul] at hs'
    change _ = upperCutoffHilbertValueOperator χ hχ hc hs
      (meanZeroCuspEmbedding (constrainedForm (1 / 4) (by norm_num) F)) z + _ at hz
    have he : upperCutoffHilbertValueOperator χ hχ hc hs
        (meanZeroCuspEmbedding (constrainedForm (1 / 4) (by norm_num) F)) z =
        upperCutoffValueOperator χ hχ hc hs
          (constrainedForm (1 / 4) (by norm_num) F : FormDomain) z :=
      congrArg (fun f : Lp ℂ 2 (volume : Measure ℂ) => f z) hform
    dsimp only [g]
    rw [hz, hs', he]
    ring
  have hUH : U ⊆ upperHalfPlaneSet := by
    intro z hz
    change 0 < z.im
    exact lt_trans (by norm_num : (0 : ℝ) < 1) (hhigh hz)
  have hcont : ContinuousOn ofComplex upperHalfPlaneSet := by
    apply ofComplex.continuousOn.mono
    intro z hz
    simpa [ofComplex] using hz
  have hg : ContinuousOn g U :=
    (((continuous_thresholdSeed J).comp_continuousOn hcont).mono hUH).sub
      ((contDiffOn_continuedHighCusp J 0).continuousOn.mono hUH) |>.sub
      ((continuousOn_scalarLift (by norm_num : (0 : ℝ) < 1 / 4) F).mono hhigh)
  exact hpoint p hp hpy F g hg hga

/-- The actual full spin-one threshold seed grows at most as square-root height
throughout the centered high cusp, with no assumed representative or PDE. -/
theorem exists_thresholdSeed_one_high_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : UpperHalfPlane, |τ.re| ≤ (1 / 2 : ℝ) → 2 ≤ τ.im →
      ‖thresholdSeed 1 τ‖ ≤ C * Real.sqrt τ.im := by
  obtain ⟨A, hA, ha⟩ := exists_threshold_remainder_bound
  let F := cuspPoincareResidualSource 1 (1 / 4) (by norm_num) 0
  let B : ℝ := 16 + ‖traceCoefficient (1 / 4) (by norm_num)‖
  refine ⟨(A + B) * ‖F‖ + 1, by dsimp [B]; positivity, ?_⟩
  intro τ hre hy
  have hrem := ha 1 (τ : ℂ) hre hy
  simp only [ofComplex_apply] at hrem
  have hhigh := norm_continuedHighCusp_zero_le_sqrt 1 τ (by linarith)
  have hscalar := scalarProfile_lift_norm_le (by norm_num : (0 : ℝ) < 1 / 4)
    (by linarith : 1 ≤ τ.im) F
  rw [CuspThresholdGreenProfile.greenProfile_quarter_constant] at hscalar
  change ‖Real.sqrt τ.im • scalarProfile (1 / 4) (by norm_num) F (Real.log τ.im)‖ ≤
    (B * ‖F‖) * Real.sqrt τ.im at hscalar
  have hsqrt : 1 ≤ Real.sqrt τ.im := (Real.le_sqrt (by norm_num) τ.im_pos.le).mpr (by nlinarith)
  have htri : ‖thresholdSeed 1 τ‖ ≤
      ‖thresholdSeed 1 τ - continuedHighCusp 1 0 τ -
        Real.sqrt τ.im • scalarProfile (1 / 4) (by norm_num) F (Real.log τ.im)‖ +
      ‖continuedHighCusp 1 0 τ‖ +
      ‖Real.sqrt τ.im • scalarProfile (1 / 4) (by norm_num) F (Real.log τ.im)‖ := by
    calc
      _ = ‖(thresholdSeed 1 τ - continuedHighCusp 1 0 τ -
        Real.sqrt τ.im • scalarProfile (1 / 4) (by norm_num) F (Real.log τ.im)) +
        continuedHighCusp 1 0 τ +
        Real.sqrt τ.im • scalarProfile (1 / 4) (by norm_num) F (Real.log τ.im)‖ := by congr 1; ring
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  calc
    _ ≤ A * ‖F‖ + Real.sqrt τ.im + (B * ‖F‖) * Real.sqrt τ.im :=
      htri.trans (add_le_add (add_le_add hrem hhigh) hscalar)
    _ ≤ (A * ‖F‖) * Real.sqrt τ.im + Real.sqrt τ.im + (B * ‖F‖) * Real.sqrt τ.im := by
      apply add_le_add _ le_rfl
      apply add_le_add _ le_rfl
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hsqrt (mul_nonneg hA.le (norm_nonneg F))
    _ = ((A + B) * ‖F‖ + 1) * Real.sqrt τ.im := by ring

end GapFamily.Analytic.PoincareThresholdCuspBound
