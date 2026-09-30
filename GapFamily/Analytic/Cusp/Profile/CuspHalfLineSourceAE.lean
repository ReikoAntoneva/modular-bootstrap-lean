import GapFamily.Analytic.Cusp.Green.CuspGreenSourceRepresentative

noncomputable section

namespace GapFamily.Analytic

open Set Filter MeasureTheory
open scoped Topology

/-- Null exceptional sets on the complete logarithmic half-line remain null
under the actual exponential change of variables. -/
theorem cuspHalfLine_ae_log_height {P : ℝ → Prop}
    (hP : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), P t) :
    ∀ᵐ y ∂(volume : Measure ℝ), 1 < y → P (Real.log y) := by
  have hmap := map_withDensity_abs_det_fderiv_eq_addHaar (volume : Measure ℝ)
    (s := Ioi (0 : ℝ)) measurableSet_Ioi.nullMeasurableSet
    (fun t _ => (Real.hasDerivAt_exp t).hasFDerivAt.hasFDerivWithinAt)
    Real.exp_injective.injOn
  have hh : ∀ᵐ y ∂volume.restrict (Ioi (1 : ℝ)), P (Real.log y) := by
    rw [← Real.exp_zero, ← Real.image_exp_Ioi, ← hmap]
    apply (Real.continuous_exp.measurableEmbedding Real.exp_injective).ae_map_iff.mpr
    apply (withDensity_absolutelyContinuous _ _).ae_le
    filter_upwards [hP] with t ht
    simpa only [Real.log_exp] using ht
  exact (ae_restrict_iff' measurableSet_Ioi).mp hh

/-- The logarithmic half-line exceptional set is null for the actual modular
measure throughout the entire cusp above height one. -/
theorem cuspHalfLine_ae_log_modular {P : ℝ → Prop}
    (hP : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), P t) :
    ∀ᵐ τ : UpperHalfPlane ∂modularMeasure, 1 < τ.im → P (Real.log τ.im) := by
  have hy := cuspHalfLine_ae_log_height hP
  have hxy := (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ))
    (ν := (volume : Measure ℝ))).ae hy
  have hz := Complex.volume_preserving_equiv_real_prod.quasiMeasurePreserving.ae hxy
  have hm := modularCoordinateMeasure_absolutelyContinuous_volume.ae_le hz
  exact (ae_modularCoordinate_iff
    (fun z : ℂ => 1 < z.im → P (Real.log z.im))).mp hm

/-- The literal zero-extended cusp lift is independent of the representative
of a half-line source, with respect to the actual modular measure. -/
theorem cuspHalfLine_lift_congr_ae {f g : ℝ → ℂ}
    (hfg : f =ᵐ[volume.restrict (Ioi (0 : ℝ))] g) :
    (fun τ : UpperHalfPlane => if 1 < τ.im then cuspLift f τ.im else 0)
      =ᵐ[modularMeasure]
    (fun τ : UpperHalfPlane => if 1 < τ.im then cuspLift g τ.im else 0) := by
  filter_upwards [cuspHalfLine_ae_log_modular hfg] with τ hτ
  by_cases hy : 1 < τ.im
  · simp only [ite_eq_left hy, cuspLift, hτ hy]
  · simp only [ite_eq_right hy]

end GapFamily.Analytic
