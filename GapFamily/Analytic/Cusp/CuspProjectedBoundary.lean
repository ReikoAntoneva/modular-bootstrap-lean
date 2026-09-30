import GapFamily.Analytic.Cusp.CuspProjectedCore
import GapFamily.Analytic.Cusp.CuspProjectedEnergy
import GapFamily.Analytic.Cusp.Profile.CuspCollarIntegral
import GapFamily.Analytic.Cusp.Fourier.CuspAverageTraceIntegral

/-! # Upper boundary trace for actual projected core residuals -/

noncomputable section
namespace GapFamily.Analytic

open Set Filter MeasureTheory UpperHalfPlane ModularGradient
open scoped Topology

/-- The actual ordinary vertical derivative of the smooth upper residual. -/
def cuspUpperResidualVertical (F : smoothCore) (z : ℂ) : ℂ :=
  fderiv ℝ F.val z Complex.I - deriv (cuspHorizontalAverage F.val) z.im

theorem continuousOn_cuspUpperResidualVertical (F : smoothCore) :
    ContinuousOn (cuspUpperResidualVertical F) upperHalfPlaneSet :=
  ((F.property.1.continuousOn_fderiv_of_isOpen isOpen_upperHalfPlaneSet (by simp)).clm_apply
    continuousOn_const).sub
      ((continuousOn_deriv_cuspHorizontalAverage F).comp Complex.continuous_im.continuousOn
        (fun _ hz => hz))

/-- Ordinary horizontal integrals are continuous at every positive height. -/
theorem continuousOn_cuspHorizontalIntegral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {G : ℂ → E} (hG : ContinuousOn G upperHalfPlaneSet) :
    ContinuousOn (fun y : ℝ => ∫ x in (-1/2 : ℝ)..(1/2), G (Complex.mk x y)) (Ioi 0) := by
  let : LocallyCompactSpace (Ioi (0 : ℝ)) := isOpen_Ioi.locallyCompactSpace
  rw [continuousOn_iff_continuous_domRestrict]
  have hj : Continuous (Function.uncurry
      (fun y : Ioi (0 : ℝ) => fun x : ℝ => G (Complex.mk x y))) := by
    apply hG.comp_continuous
    · simp only [cuspPoint_eq]
      fun_prop
    · intro p
      exact p.1.property
  have hi := continuous_parametric_integral_of_continuous (μ := volume) hj
    (s := Icc (-1/2 : ℝ) (1/2)) isCompact_Icc
  apply hi.congr
  intro y
  change (∫ x in Icc (-1/2 : ℝ) (1/2), G (Complex.mk x (y : ℝ))) =
    ∫ x in (-1/2 : ℝ)..(1/2), G (Complex.mk x (y : ℝ))
  rw [intervalIntegral.integral_of_le (by norm_num : (-1/2 : ℝ) ≤ 1/2),
    ← integral_Icc_eq_integral_Ioc]

theorem cuspResidual_boundary_integrable (F : smoothCore) :
    IntervalIntegrable (fun x : ℝ => ‖cuspHorizontalResidual F.val (Complex.mk x 1)‖^2)
      volume (-1/2) (1/2) := by
  have hc : Continuous (fun x : ℝ => F.val (Complex.mk x 1) - cuspHorizontalAverage F.val 1) :=
    (contDiff_cuspHorizontalSlice F.property.1 zero_lt_one).continuous.sub continuous_const
  change IntervalIntegrable (fun x : ℝ => ‖F.val (Complex.mk x 1) -
    cuspHorizontalAverage F.val 1‖^2) volume (-1/2) (1/2)
  exact (hc.norm.pow 2).intervalIntegrable _ _

/-- The two fields in the vertical trace inequality have genuine ordinary
square integrals on the closed collar. -/
theorem cuspResidual_collar_integrable (F : smoothCore) :
    IntegrableOn (fun p : ℝ × ℝ => ‖cuspHorizontalResidual F.val (Complex.mk p.1 p.2)‖^2)
        (Icc (-1/2 : ℝ) (1/2) ×ˢ Icc (1 : ℝ) 2) (volume.prod volume) ∧
    IntegrableOn (fun p : ℝ × ℝ => ‖cuspUpperResidualVertical F (Complex.mk p.1 p.2)‖^2)
        (Icc (-1/2 : ℝ) (1/2) ×ˢ Icc (1 : ℝ) 2) (volume.prod volume) := by
  constructor
  · simpa only [Pi.pow_apply, show (1 : ℝ) + 1 = 2 by norm_num] using
      cuspCollar_product_integrable
        ((continuousOn_cuspHorizontalResidual F.property.1.continuousOn).norm.pow 2) 1
  · simpa only [Pi.pow_apply, show (1 : ℝ) + 1 = 2 by norm_num] using
      cuspCollar_product_integrable ((continuousOn_cuspUpperResidualVertical F).norm.pow 2) 1

theorem cuspResidual_vertical_trace_sq_le (F : smoothCore) (x : ℝ) :
    ‖cuspHorizontalResidual F.val (Complex.mk x 1)‖^2 ≤
      2 * (∫ y in (1 : ℝ)..2, ‖cuspHorizontalResidual F.val (Complex.mk x y)‖^2) +
      2 * (∫ y in (1 : ℝ)..2, ‖cuspUpperResidualVertical F (Complex.mk x y)‖^2) := by
  have hs : Icc (1 : ℝ) 2 ⊆ Ioi 0 := by
    intro y hy
    exact zero_lt_one.trans_le hy.1
  have hc : ContinuousOn (fun y : ℝ => cuspHorizontalResidual F.val (Complex.mk x y))
      (Icc (1 : ℝ) 2) :=
    ((continuousOn_cuspVerticalSlice F.property.1.continuousOn x).sub
      (continuousOn_cuspHorizontalAverage F.property.1.continuousOn)).mono hs
  have hd : ContinuousOn (fun y : ℝ => cuspUpperResidualVertical F (Complex.mk x y))
      (Icc (1 : ℝ) 2) :=
    ((continuousOn_cuspVerticalDerivative F.property.1 x).sub
      (continuousOn_deriv_cuspHorizontalAverage F)).mono hs
  have hdiff : ∀ y ∈ Ioo (1 : ℝ) 2,
      HasDerivAt (fun t : ℝ => cuspHorizontalResidual F.val (Complex.mk x t))
        (cuspUpperResidualVertical F (Complex.mk x y)) y := by
    intro y hy
    have hy0 : 0 < y := zero_lt_one.trans hy.1
    exact (hasDerivAt_cuspVerticalSlice F.property.1 x hy0).sub
      (hasDerivAt_cuspHorizontalAverage F hy0).differentiableAt.hasDerivAt
  simpa only [show (2 : ℝ) - 1 = 1 by norm_num, div_one, mul_one] using
    IntervalTrace.left_norm_sq_le (by norm_num : (1 : ℝ) < 2) hc hd hdiff

/-- Integrated unit-row Poincaré controls residual mass by the ordinary
horizontal component energy on the same collar. -/
theorem cuspResidual_collar_mass_le_horizontal_energy (F : smoothCore) :
    (∫ x in (-1/2 : ℝ)..(1/2), ∫ y in (1 : ℝ)..2,
      ‖cuspHorizontalResidual F.val (Complex.mk x y)‖^2) ≤
    ∫ x in (-1/2 : ℝ)..(1/2), ∫ y in (1 : ℝ)..2,
      ‖fderiv ℝ F.val (Complex.mk x y) 1‖^2 := by
  have hR : ContinuousOn (fun z => ‖cuspHorizontalResidual F.val z‖^2) upperHalfPlaneSet :=
    (continuousOn_cuspHorizontalResidual F.property.1.continuousOn).norm.pow 2
  have hX : ContinuousOn (fun z => ‖fderiv ℝ F.val z 1‖^2) upperHalfPlaneSet :=
    ((F.property.1.continuousOn_fderiv_of_isOpen isOpen_upperHalfPlaneSet (by simp)).clm_apply
      continuousOn_const).norm.pow 2
  have hswapR := cuspCollar_integral_swap _ hR (show (0 : ℝ) ≤ 1 from zero_le_one)
  have hswapX := cuspCollar_integral_swap _ hX (show (0 : ℝ) ≤ 1 from zero_le_one)
  simp only [show (1 : ℝ) + 1 = 2 by norm_num] at hswapR hswapX
  rw [hswapR, hswapX]
  have hs : Icc (1 : ℝ) 2 ⊆ Ioi 0 := by
    intro y hy
    exact zero_lt_one.trans_le hy.1
  apply intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (1 : ℝ) ≤ 2)
    (((continuousOn_cuspHorizontalIntegral hR).mono hs).intervalIntegrable_of_Icc (by norm_num))
    (((continuousOn_cuspHorizontalIntegral hX).mono hs).intervalIntegrable_of_Icc (by norm_num))
  intro y hy
  exact modular_horizontal_poincare F.property.1 (zero_lt_one.trans_le hy.1)

/-- The raw boundary residual is bounded by twice the sum of its actual
horizontal and vertical ordinary collar energies. -/
theorem cuspResidual_boundary_le_collar_energy (F : smoothCore) :
    (∫ x in (-1/2 : ℝ)..(1/2), ‖cuspHorizontalResidual F.val (Complex.mk x 1)‖^2) ≤
      2 * (∫ x in (-1/2 : ℝ)..(1/2), ∫ y in (1 : ℝ)..2,
        ‖fderiv ℝ F.val (Complex.mk x y) 1‖^2) +
      2 * (∫ x in (-1/2 : ℝ)..(1/2), ∫ y in (1 : ℝ)..2,
        ‖cuspUpperResidualVertical F (Complex.mk x y)‖^2) := by
  have hR : Continuous (fun x : ℝ => ∫ y in (1 : ℝ)..2,
      ‖cuspHorizontalResidual F.val (Complex.mk x y)‖^2) := by
    simpa only [Pi.pow_apply, show (1 : ℝ) + 1 = 2 by norm_num] using
      continuous_cuspVerticalIntegral
        ((continuousOn_cuspHorizontalResidual F.property.1.continuousOn).norm.pow 2) zero_le_one
  have hV : Continuous (fun x : ℝ => ∫ y in (1 : ℝ)..2,
      ‖cuspUpperResidualVertical F (Complex.mk x y)‖^2) := by
    simpa only [Pi.pow_apply, show (1 : ℝ) + 1 = 2 by norm_num] using
      continuous_cuspVerticalIntegral ((continuousOn_cuspUpperResidualVertical F).norm.pow 2)
        zero_le_one
  have hm := intervalIntegral.integral_mono_on (μ := volume)
    (by norm_num : (-1/2 : ℝ) ≤ 1/2) (cuspResidual_boundary_integrable F)
    (((hR.const_mul 2).add (hV.const_mul 2)).intervalIntegrable (-1/2) (1/2))
    (fun x _ => cuspResidual_vertical_trace_sq_le F x)
  simp only [Pi.add_apply] at hm
  rw [intervalIntegral.integral_add (μ := volume)
      ((hR.const_mul 2).intervalIntegrable _ _) ((hV.const_mul 2).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hm
  have hmass := cuspResidual_collar_mass_le_horizontal_energy F
  linarith

/-- The height-one residual has an actual ordinary L² boundary trace bounded
by twice the energy of the actual projected core vector. No smoothness of
that completed projected vector is assumed. -/
theorem cuspProjected_boundary_trace_sq_le (F : smoothCore) :
    (∫ x in (-1/2 : ℝ)..(1/2),
      ‖F.val (Complex.mk x 1) - cuspHorizontalAverage F.val 1‖^2) ≤
      2 * ‖formGradient (cuspMeanZeroFormPart (coreForm F) : FormDomain)‖^2 := by
  have ht := cuspResidual_boundary_le_collar_energy F
  have hx := cuspProjected_horizontal_collar_energy_le F
  have hy := cuspProjected_vertical_collar_energy_le F
  change (∫ x in (-1/2 : ℝ)..(1/2), ∫ y in (1 : ℝ)..2,
    ‖cuspUpperResidualVertical F (Complex.mk x y)‖^2) ≤ _ at hy
  have hsum := WithLp.prod_norm_sq_eq_of_L2
    (formGradient (cuspMeanZeroFormPart (coreForm F) : FormDomain))
  change ‖formGradient (cuspMeanZeroFormPart (coreForm F) : FormDomain)‖^2 =
    ‖(formGradient (cuspMeanZeroFormPart (coreForm F) : FormDomain)).ofLp.1‖^2 +
    ‖(formGradient (cuspMeanZeroFormPart (coreForm F) : FormDomain)).ofLp.2‖^2 at hsum
  change (∫ x in (-1/2 : ℝ)..(1/2),
    ‖cuspHorizontalResidual F.val (Complex.mk x 1)‖^2) ≤ _
  linarith

end GapFamily.Analytic
