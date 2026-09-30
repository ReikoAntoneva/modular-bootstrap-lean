import GapFamily.Analytic.Cusp.Fourier.CuspHorizontalHilbertClosed

/-!
# Coherence of cusp operators under increasing cutoff height

All restrictions use the actual high-cusp hyperbolic L² measures. Equality of
horizontal averaging at different heights is proved first from its literal
ordinary-integral formula on the smooth automorphic core, then extended by
the proved density of the core values.
-/

noncomputable section

namespace GapFamily.Analytic

open MeasureTheory Set Filter UpperHalfPlane

/-- Increasing the height decreases the actual restricted measure. -/
theorem cuspMeasure_mono {H K : ℝ} (hHK : H ≤ K) :
    modularMeasure.restrict {τ : UpperHalfPlane | K < τ.im} ≤
      modularMeasure.restrict {τ : UpperHalfPlane | H < τ.im} :=
  Measure.restrict_mono (fun _ hτ => hHK.trans_lt hτ) le_rfl

/-- Restriction from one cusp Hilbert space to a higher cusp. -/
def cuspHeightRestrict (H K : ℝ) (_hHK : H ≤ K) : cuspHilbert H →L[ℂ] cuspHilbert K :=
  (cuspRestrict K).comp (cuspZeroExtension H).toContinuousLinearMap

/-- The map has the literal original representative almost everywhere above K. -/
theorem cuspHeightRestrict_ae (H K : ℝ) (hHK : H ≤ K) (f : cuspHilbert H) :
    cuspHeightRestrict H K hHK f =ᵐ[modularMeasure.restrict {τ : UpperHalfPlane | K < τ.im}] f :=
  (cuspRestrict_ae K (cuspZeroExtend H f)).trans
    ((cuspZeroExtend_restrict_ae H f).filter_mono (ae_mono (cuspMeasure_mono hHK)))

theorem norm_cuspHeightRestrict_le (H K : ℝ) (hHK : H ≤ K) (f : cuspHilbert H) :
    ‖cuspHeightRestrict H K hHK f‖ ≤ ‖f‖ := by
  exact (norm_cuspRestrict_le K (cuspZeroExtend H f)).trans_eq (cuspZeroExtend_norm H f)

theorem cuspHeightRestrict_norm_le_one (H K : ℝ) (hHK : H ≤ K) :
    ‖cuspHeightRestrict H K hHK‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [one_mul] using norm_cuspHeightRestrict_le H K hHK f

/-- Direct ambient restriction agrees with successive restrictions. -/
theorem cuspHeightRestrict_cuspRestrict (H K : ℝ) (hHK : H ≤ K) (f : ModularHilbert) :
    cuspHeightRestrict H K hHK (cuspRestrict H f) = cuspRestrict K f := by
  apply Lp.ext
  exact ((cuspHeightRestrict_ae H K hHK (cuspRestrict H f)).trans
    ((cuspRestrict_ae H f).filter_mono (ae_mono (cuspMeasure_mono hHK)))).trans
    (cuspRestrict_ae K f).symm

theorem cuspHeightRestrict_coreValue (H K : ℝ) (hHK : H ≤ K)
    (F : ModularGradient.smoothCore) :
    cuspHeightRestrict H K hHK (cuspCoreValue H F) = cuspCoreValue K F :=
  cuspHeightRestrict_cuspRestrict H K hHK (ModularGradient.value F)

/-- The literal ordinary horizontal average is independent of the lower cutoff. -/
theorem cuspHeightRestrict_coreAverage (H K : ℝ) (hH : 1 ≤ H) (hHK : H ≤ K)
    (F : ModularGradient.smoothCore) :
    cuspHeightRestrict H K hHK (cuspCoreAverage H hH F) =
      cuspCoreAverage K (hH.trans hHK) F := by
  apply Lp.ext
  exact ((cuspHeightRestrict_ae H K hHK (cuspCoreAverage H hH F)).trans
    ((cuspCoreAverage_ae H hH F).filter_mono (ae_mono (cuspMeasure_mono hHK)))).trans
    (cuspCoreAverage_ae K (hH.trans hHK) F).symm

/-- Bounded averaging commutes with restriction to a higher cusp. -/
theorem cuspHeightRestrict_comp_average (H K : ℝ) (hH : 1 ≤ H) (hHK : H ≤ K) :
    (cuspHeightRestrict H K hHK).comp (cuspAverage H hH) =
      (cuspAverage K (hH.trans hHK)).comp (cuspHeightRestrict H K hHK) := by
  apply ContinuousLinearMap.ext
  intro f
  apply congrFun ((cuspCoreValue_dense_range H).equalizer
    (((cuspHeightRestrict H K hHK).comp (cuspAverage H hH)).continuous)
    (((cuspAverage K (hH.trans hHK)).comp (cuspHeightRestrict H K hHK)).continuous) _)
  funext F
  simp only [Function.comp_apply, ContinuousLinearMap.comp_apply,
    cuspAverage_core, cuspHeightRestrict_coreValue, cuspHeightRestrict_coreAverage]

theorem cuspHeightRestrict_average (H K : ℝ) (hH : 1 ≤ H) (hHK : H ≤ K)
    (f : cuspHilbert H) :
    cuspHeightRestrict H K hHK (cuspAverage H hH f) =
      cuspAverage K (hH.trans hHK) (cuspHeightRestrict H K hHK f) :=
  congrArg (fun T : cuspHilbert H →L[ℂ] cuspHilbert K => T f)
    (cuspHeightRestrict_comp_average H K hH hHK)

/-- The actual nonconstant horizontal residual is coherent across cut heights. -/
theorem cuspHeightRestrict_residual (H K : ℝ) (hH : 1 ≤ H) (hHK : H ≤ K)
    (f : cuspHilbert H) :
    cuspHeightRestrict H K hHK (cuspResidual H hH f) =
      cuspResidual K (hH.trans hHK) (cuspHeightRestrict H K hHK f) := by
  rw [cuspResidual_apply, map_sub, cuspHeightRestrict_average, cuspResidual_apply]

theorem cuspHeightRestrict_comp_residual (H K : ℝ) (hH : 1 ≤ H) (hHK : H ≤ K) :
    (cuspHeightRestrict H K hHK).comp (cuspResidual H hH) =
      (cuspResidual K (hH.trans hHK)).comp (cuspHeightRestrict H K hHK) := by
  apply ContinuousLinearMap.ext
  intro f
  exact cuspHeightRestrict_residual H K hH hHK f

/-- The completed form-domain residual agrees after increasing the cutoff. -/
theorem cuspHeightRestrict_formResidual (H K : ℝ) (hH : 1 ≤ H) (hHK : H ≤ K)
    (u : ModularGradient.FormDomain) :
    cuspHeightRestrict H K hHK (cuspFormResidual H hH u) =
      cuspFormResidual K (hH.trans hHK) u := by
  change cuspHeightRestrict H K hHK
      (cuspResidual H hH (cuspRestrict H (ModularGradient.formEmbedding u))) =
    cuspResidual K (hH.trans hHK) (cuspRestrict K (ModularGradient.formEmbedding u))
  rw [cuspHeightRestrict_residual, cuspHeightRestrict_cuspRestrict]

theorem cuspHeightRestrict_comp_formResidual (H K : ℝ) (hH : 1 ≤ H) (hHK : H ≤ K) :
    (cuspHeightRestrict H K hHK).comp (cuspFormResidual H hH) =
      cuspFormResidual K (hH.trans hHK) := by
  apply ContinuousLinearMap.ext
  intro u
  exact cuspHeightRestrict_formResidual H K hH hHK u

/-- Every higher tail is the restriction of the single baseline tail at height one. -/
theorem cuspFormResidual_eq_restrict_one (K : ℝ) (hK : 1 ≤ K) :
    cuspFormResidual K hK =
      (cuspHeightRestrict 1 K hK).comp (cuspFormResidual 1 le_rfl) :=
  (cuspHeightRestrict_comp_formResidual 1 K le_rfl hK).symm

end GapFamily.Analytic
