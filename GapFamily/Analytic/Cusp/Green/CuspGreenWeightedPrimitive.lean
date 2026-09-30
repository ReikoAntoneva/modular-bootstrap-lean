import GapFamily.Analytic.Cusp.Green.CuspGreenWeightedLocal
import GapFamily.Analytic.Cusp.Green.CuspGreenOperatorTrace
import GapFamily.Analytic.Cusp.Profile.CuspCollarPrimitiveInterval

/-!
# The primitive and trace of a weighted half-line source

The finite-collar primitive integrates the same ordinary half-line source up
to the observation point, independently of a larger source cutoff. The full
shifted Laplace trace is the weighted finite-collar trace plus its genuine
noncompact tail. All ordinary integrals have explicit integrability proofs.
-/

noncomputable section

namespace GapFamily.Analytic

open Set Filter MeasureTheory CuspHalfLineLaplace CuspHalfLineLaplaceTail
open scoped Topology

/-- Every half-line Hilbert source is ordinarily integrable on a finite collar. -/
theorem cuspHalfLine_integrableOn_Ioc (T : ℝ) (f : HalfLineL2) :
    IntegrableOn f (Ioc 0 T) := by
  have hf : MemLp f 2 (volume.restrict (Ioc 0 T)) :=
    (Lp.memLp f).mono_measure (Measure.restrict_mono_set volume Ioc_subset_Ioi_self)
  exact hf.integrable (by norm_num)

/-- The finite-collar primitive is the literal ordinary primitive of the same
half-line source whenever the source cutoff contains the observation collar. -/
theorem cuspCollarPrimitive_halfLineRestriction_apply {L T : ℝ} (hLT : L ≤ T)
    (f : HalfLineL2) (t : CuspGreenCollar 0 L) :
    cuspCollarPrimitive L T (cuspHalfLineCollarRestriction T f) t =
      ∫ u : ℝ in Ioc 0 (t : ℝ), f u := by
  rw [cuspCollarPrimitive_apply]
  calc
    _ = ∫ u : CuspGreenCollar 0 T in {u | (u : ℝ) ≤ (t : ℝ)},
        f u ∂cuspGreenCollarMeasure 0 T := by
      apply integral_congr_ae
      exact ae_restrict_of_ae (cuspHalfLineCollarRestriction_ae T f)
    _ = ∫ u : ℝ in Icc 0 (min T (t : ℝ)), f u :=
      cuspCollarPrimitiveSlice_integral T t f
    _ = _ := by
      rw [min_eq_right (t.property.2.trans hLT), integral_Icc_eq_integral_Ioc]

/-- The source primitive on a fixed observation collar is unchanged when its
source cap is reduced to that observation collar. -/
theorem cuspCollarPrimitive_halfLineRestriction_cutoff_eq {L T : ℝ} (hLT : L ≤ T)
    (f : HalfLineL2) :
    cuspCollarPrimitive L T (cuspHalfLineCollarRestriction T f) =
      cuspCollarPrimitive L L (cuspHalfLineCollarRestriction L f) := by
  ext t
  rw [cuspCollarPrimitive_halfLineRestriction_apply hLT,
    cuspCollarPrimitive_halfLineRestriction_apply le_rfl]

/-- The cutoff independence holds for the actual bounded primitive operators. -/
theorem cuspCollarPrimitive_halfLineRestriction_comp_eq {L T : ℝ} (hLT : L ≤ T) :
    (cuspCollarPrimitive L T).comp (cuspHalfLineCollarRestriction T) =
      (cuspCollarPrimitive L L).comp (cuspHalfLineCollarRestriction L) := by
  apply ContinuousLinearMap.ext
  intro f
  exact cuspCollarPrimitive_halfLineRestriction_cutoff_eq hLT f

/-- The weighted collar trace is the literal finite shifted Laplace integral. -/
theorem cuspGreenWeightedCollarTrace_apply (α : ℝ) (hα : 0 ≤ α) (T : ℝ) (κ : ℂ)
    (f : HalfLineL2) :
    cuspGreenCollarTraceOperator 0 T κ
      (cuspHalfLineCollarRestriction T (cuspHalfLineWeight α hα f)) =
      ∫ u : ℝ in Ioc 0 T, Complex.exp (-((α : ℂ) + κ) * (u : ℂ)) * f u := by
  rw [cuspGreenCollarTraceOperator_apply]
  simp only [sub_zero]
  rw [cuspHalfLineCollarRestriction_integral T (cuspHalfLineWeight α hα f)
    (fun u => Complex.exp (-κ * (u : ℂ)))]
  apply integral_congr_ae
  have hw := (MeasureTheory.ae_mono
    (Measure.restrict_mono_set volume (Ioc_subset_Ioi_self : Ioc (0 : ℝ) T ⊆ Ioi 0)))
      (cuspHalfLineWeight_ae α hα f)
  filter_upwards [hw] with u hu
  rw [hu, Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- The finite shifted Laplace trace is genuinely integrable for every parameter. -/
theorem cuspGreenWeightedCollarTrace_integrable (T : ℝ) (β : ℂ) (f : HalfLineL2) :
    IntegrableOn (fun u : ℝ => Complex.exp (-β * (u : ℂ)) * f u) (Ioc 0 T) := by
  have hcont : Continuous (fun u : ℝ => Complex.exp (-β * (u : ℂ))) := by fun_prop
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (0 : ℝ) T) hcont.continuousOn
  exact (cuspHalfLine_integrableOn_Ioc T f).bdd_mul hcont.aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall
      (fun u hu => hC u (Ioc_subset_Icc_self hu))))

/-- The full shifted Laplace trace splits into the weighted collar trace and
the genuine noncompact tail on the natural shifted half-plane. -/
theorem cuspGreenWeighted_laplace_split {α T : ℝ} (hα : 0 ≤ α) (hT : 0 ≤ T)
    {κ : ℂ} (hβ : 0 < ((α : ℂ) + κ).re) (f : HalfLineL2) :
    laplace ((α : ℂ) + κ) f =
      cuspGreenCollarTraceOperator 0 T κ
        (cuspHalfLineCollarRestriction T (cuspHalfLineWeight α hα f)) +
      tailLaplace T ((α : ℂ) + κ) f := by
  rw [laplace_apply hβ, cuspGreenWeightedCollarTrace_apply, tailLaplace_apply hT hβ]
  have h := setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
    ((laplace_integrable hβ f).mono_set (Ioc_subset_Ioi_self : Ioc (0 : ℝ) T ⊆ Ioi 0))
    ((laplace_integrable hβ f).mono_set (Ioi_subset_Ioi hT))
  simpa only [Ioc_union_Ioi_eq_Ioi hT] using h

end GapFamily.Analytic
