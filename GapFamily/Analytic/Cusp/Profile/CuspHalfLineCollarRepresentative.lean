import GapFamily.Analytic.Cusp.Profile.CuspHalfLineSourceCollar
import GapFamily.Analytic.Cusp.Profile.CuspHalfLineSourceTruncation
import GapFamily.Analytic.Cusp.Green.CuspGreenHeightSupport

noncomputable section

namespace GapFamily.Analytic

open Set MeasureTheory

private theorem collar_restrict_le_halfLine (T : ℝ) :
    volume.restrict (Icc 0 T) ≤ volume.restrict (Ioi (0 : ℝ)) := by
  rw [← Measure.restrict_congr_set (Ioc_ae_eq_Icc (a := (0 : ℝ)) (b := T))]
  exact Measure.restrict_mono Ioc_subset_Ioi_self le_rfl

/-- A half-line square-integrable source has its literal representative on every
finite collar, including a collar of zero measure. -/
theorem cuspHalfLineCollar_memLp (T : ℝ) (f : cuspHalfLineSourceHilbert) :
    MemLp (fun t : CuspGreenCollar 0 T => f t) 2 (cuspGreenCollarMeasure 0 T) := by
  exact ((Lp.memLp f).mono_measure (collar_restrict_le_halfLine T)).comp_measurePreserving
    (measurePreserving_subtype_coe measurableSet_Icc)

/-- The Hilbert adjoint restriction is the ordinary restriction of representatives. -/
theorem cuspHalfLineCollarRestriction_ae (T : ℝ) (f : cuspHalfLineSourceHilbert) :
    cuspHalfLineCollarRestriction T f =ᵐ[cuspGreenCollarMeasure 0 T]
      (fun t : CuspGreenCollar 0 T => f t) := by
  let r := (cuspHalfLineCollar_memLp T f).toLp (fun t : CuspGreenCollar 0 T => f t)
  have hr : r =ᵐ[cuspGreenCollarMeasure 0 T]
      (fun t : CuspGreenCollar 0 T => f t) := MemLp.coeFn_toLp _
  have heq : cuspHalfLineCollarRestriction T f = r := by
    apply (cuspGreenSourceRestriction_denseRange T).eq_of_inner_right ℂ
    intro g
    rw [cuspHalfLineCollarRestriction_inner_right, cuspHalfLineCollarInclusion_restriction,
      L2.inner_def, L2.inner_def]
    calc
      _ = ∫ t : ℝ in Ioi 0, inner ℂ ((g : ℝ → ℂ) t) (f t) := by
        apply integral_congr_ae
        filter_upwards [cuspHalfLineCollarSmoothValue_ae T g] with t ht
        rw [ht]
      _ = ∫ t : ℝ in Icc 0 T, inner ℂ ((g : ℝ → ℂ) t) (f t) := by
        have hi : (∫ t : ℝ in Ioi 0, inner ℂ ((g : ℝ → ℂ) t) (f t)) =
            ∫ t : ℝ, inner ℂ ((g : ℝ → ℂ) t) (f t) := by
          apply setIntegral_eq_integral_of_forall_compl_eq_zero
          intro t ht
          have hg : (g : ℝ → ℂ) t = 0 := image_eq_zero_of_notMem_tsupport
            (fun h => ht ((g.property.2.2 h).1))
          rw [hg, inner_zero_left]
        have hc : (∫ t : ℝ in Icc 0 T, inner ℂ ((g : ℝ → ℂ) t) (f t)) =
            ∫ t : ℝ, inner ℂ ((g : ℝ → ℂ) t) (f t) := by
          apply setIntegral_eq_integral_of_forall_compl_eq_zero
          intro t ht
          have hg : (g : ℝ → ℂ) t = 0 := image_eq_zero_of_notMem_tsupport
            (fun h => ht (Ioo_subset_Icc_self (g.property.2.2 h)))
          rw [hg, inner_zero_left]
        exact hi.trans hc.symm
      _ = ∫ t : CuspGreenCollar 0 T,
          inner ℂ ((g : ℝ → ℂ) t) (f t) ∂cuspGreenCollarMeasure 0 T :=
        (integral_subtype_comap measurableSet_Icc _).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [cuspGreenSourceRestriction_coeFn T g, hr] with t hg ht
        rw [hg, ht]
  exact heq ▸ hr

/-- Collar pairing uses the ordinary logarithmic integral of the same source.
The equality holds for the total Bochner integral without an integrability premise. -/
theorem cuspHalfLineCollarRestriction_integral (T : ℝ) (f : cuspHalfLineSourceHilbert)
    (k : ℝ → ℂ) :
    (∫ t : CuspGreenCollar 0 T, k t * cuspHalfLineCollarRestriction T f t
      ∂cuspGreenCollarMeasure 0 T) = ∫ t : ℝ in Ioc 0 T, k t * f t := by
  calc
    _ = ∫ t : CuspGreenCollar 0 T, k t * f t ∂cuspGreenCollarMeasure 0 T := by
      apply integral_congr_ae
      filter_upwards [cuspHalfLineCollarRestriction_ae T f] with t ht
      rw [ht]
    _ = ∫ t : ℝ in Icc 0 T, k t * f t :=
      integral_subtype_comap measurableSet_Icc (fun t : ℝ => k t * f t)
    _ = _ := integral_Icc_eq_integral_Ioc

/-- Zero extension after actual adjoint restriction is precisely the literal
half-line source truncation. -/
theorem cuspHalfLineCollarInclusion_restriction_eq_truncation (T : ℝ)
    (f : cuspHalfLineSourceHilbert) :
    cuspHalfLineCollarInclusion T (cuspHalfLineCollarRestriction T f) =
      cuspHalfLineSourceTruncation T f := by
  apply ext_inner_right ℂ
  intro g
  rw [← cuspHalfLineCollarRestriction_inner_right, L2.inner_def, L2.inner_def]
  calc
    _ = ∫ t : CuspGreenCollar 0 T, inner ℂ (f t) (g t)
        ∂cuspGreenCollarMeasure 0 T := by
      apply integral_congr_ae
      filter_upwards [cuspHalfLineCollarRestriction_ae T f,
        cuspHalfLineCollarRestriction_ae T g] with t hf hg
      rw [hf, hg]
    _ = ∫ t : ℝ in Icc 0 T, inner ℂ (f t) (g t) :=
      integral_subtype_comap measurableSet_Icc (fun t : ℝ => inner ℂ (f t) (g t))
    _ = ∫ t : ℝ in Ioc 0 T, inner ℂ (f t) (g t) := integral_Icc_eq_integral_Ioc
    _ = ∫ t : ℝ in Ioi 0, (Iic T).indicator (fun t => inner ℂ (f t) (g t)) t := by
      rw [integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
        inter_comm, Ioi_inter_Iic]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [cuspHalfLineSourceTruncation_ae T f] with t ht
      rw [ht]
      by_cases h : t ∈ Iic T <;> simp [Set.indicator, h]

/-- Every actual collar inclusion has precisely its declared logarithmic height support. -/
theorem cuspHalfLineSourceTruncation_collarInclusion (T : ℝ)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure 0 T)) :
    cuspHalfLineSourceTruncation T (cuspHalfLineCollarInclusion T f) =
      cuspHalfLineCollarInclusion T f := by
  rw [← cuspHalfLineCollarInclusion_restriction_eq_truncation,
    cuspHalfLineCollarRestriction_inclusion]

/-- The actual finite collar embedding is unchanged by its physical height cutoff. -/
theorem modularLowCut_cuspGreenSourceEmbedding (T : ℝ)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure 0 T)) :
    modularLowCut (Real.exp T) (cuspGreenSourceEmbedding T f) =
      cuspGreenSourceEmbedding T f := by
  rw [← cuspHalfLineSourceEmbedding_collarInclusion,
    ← cuspHalfLineSourceEmbedding_truncation, cuspHalfLineSourceTruncation_collarInclusion]

/-- Finite collar coefficient extraction absorbs the same physical height cutoff
for every ambient Hilbert source. -/
theorem cuspGreenSourceCoefficient_lowCut (T : ℝ) (F : ModularHilbert) :
    cuspGreenSourceCoefficient T (modularLowCut (Real.exp T) F) =
      cuspGreenSourceCoefficient T F := by
  apply ext_inner_right ℂ
  intro f
  rw [cuspGreenSourceCoefficient_inner_left, cuspGreenSourceCoefficient_inner_left,
    modularLowCut_inner_symm, modularLowCut_cuspGreenSourceEmbedding]

end GapFamily.Analytic
