import GapFamily.Analytic.Cusp.Green.CuspGreenOperatorTrace
import GapFamily.Analytic.Cusp.Green.CuspGreenBoundaryData
import GapFamily.Analytic.Cusp.Green.CuspGreenBoundaryHeight

/-!
# The actual exterior response of a collar source

For every ordinary collar L² source the actual Green integral is one outgoing
exponential above the collar. The upper endpoint truncates the source; its
actual exterior derivative is a Robin trace, with no upper Dirichlet condition.
-/

noncomputable section
namespace GapFamily.Analytic
open MeasureTheory Set Filter
open scoped Topology

/-- Every collar source contributes only its outgoing boundary value above the collar. -/
theorem cuspGreenCollarResponse_eq_outgoing (a T t : ℝ) (ht : T ≤ t) (κ : ℂ)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure a T)) :
    cuspGreenCollarResponse a T κ f t =
      Complex.exp (-κ * ((t - T : ℝ) : ℂ)) * cuspGreenCollarResponse a T κ f T := by
  simp only [cuspGreenCollarResponse]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [cuspGreen_boundaryHeight_below a T t u ht u.property.2 κ, mul_assoc]

/-- Identification with the actual smooth homogeneous mode, including at zero. -/
theorem cuspGreenCollarResponse_eq_boundaryMode (a T t : ℝ) (ht : T ≤ t) (κ : ℂ)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure a T)) :
    cuspGreenCollarResponse a T κ f t =
      cuspBoundaryMode T κ (cuspGreenCollarResponse a T κ f T) t := by
  rw [cuspGreenCollarResponse_eq_outgoing a T t ht κ f, cuspBoundaryMode, mul_comm]

/-- The exterior derivative exists on the entire closed exterior, including its endpoint. -/
theorem hasDerivWithinAt_cuspGreenCollarResponse_exterior (a T t : ℝ)
    (ht : T ≤ t) (κ : ℂ) (f : Lp ℂ 2 (cuspGreenCollarMeasure a T)) :
    HasDerivWithinAt (cuspGreenCollarResponse a T κ f)
      (-κ * cuspGreenCollarResponse a T κ f t) (Ici T) t := by
  have hd := (hasDerivAt_cuspBoundaryMode T κ
    (cuspGreenCollarResponse a T κ f T) t).hasDerivWithinAt (s := Ici T)
  rw [← cuspGreenCollarResponse_eq_boundaryMode a T t ht κ f] at hd
  apply hd.congr_of_mem
  · intro v hv
    exact cuspGreenCollarResponse_eq_boundaryMode a T v hv κ f
  · exact ht

/-- The derivative from above at the collar endpoint is the actual outgoing Robin trace. -/
theorem hasDerivWithinAt_cuspGreenCollarResponse_upper (a T : ℝ) (κ : ℂ)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure a T)) :
    HasDerivWithinAt (cuspGreenCollarResponse a T κ f)
      (-κ * cuspGreenCollarResponse a T κ f T) (Ici T) T :=
  hasDerivWithinAt_cuspGreenCollarResponse_exterior a T T le_rfl κ f

theorem derivWithin_cuspGreenCollarResponse_upper (a T : ℝ) (κ : ℂ)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure a T)) :
    derivWithin (cuspGreenCollarResponse a T κ f) (Ici T) T =
      -κ * cuspGreenCollarResponse a T κ f T :=
  (hasDerivWithinAt_cuspGreenCollarResponse_upper a T κ f).derivWithin
    (uniqueDiffWithinAt_Ici T)

/-- The ordinary first derivative above the source collar. -/
theorem hasDerivAt_cuspGreenCollarResponse_exterior (a T : ℝ) (κ : ℂ)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure a T)) {t : ℝ} (ht : T < t) :
    HasDerivAt (cuspGreenCollarResponse a T κ f)
      (-κ * cuspGreenCollarResponse a T κ f t) t :=
  (hasDerivWithinAt_cuspGreenCollarResponse_exterior a T t ht.le κ f).hasDerivAt
    (Ici_mem_nhds ht)

/-- The exterior amplitude has an exact exponential norm, valid for every parameter. -/
theorem norm_cuspGreenCollarResponse_exterior (a T t : ℝ) (ht : T ≤ t) (κ : ℂ)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure a T)) :
    ‖cuspGreenCollarResponse a T κ f t‖ =
      Real.exp (-κ.re * (t - T)) * ‖cuspGreenCollarResponse a T κ f T‖ := by
  rw [cuspGreenCollarResponse_eq_outgoing a T t ht κ f, norm_mul, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
    Complex.neg_im, Complex.ofReal_im, mul_zero, sub_zero]

/-- Physical positive-real-part parameters give actual outgoing decay for every L² source. -/
theorem cuspGreenCollarResponse_tendsto_zero (a T : ℝ) {κ : ℂ} (hκ : 0 < κ.re)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure a T)) :
    Tendsto (cuspGreenCollarResponse a T κ f) atTop (𝓝 0) := by
  apply (cuspBoundaryMode_tendsto_zero T hκ
    (cuspGreenCollarResponse a T κ f T)).congr'
  filter_upwards [eventually_ge_atTop T] with t ht
  exact (cuspGreenCollarResponse_eq_boundaryMode a T t ht κ f).symm

/-- At threshold the whole exterior response is constant. -/
theorem cuspGreenCollarResponse_zero_exterior (a T t : ℝ) (ht : T ≤ t)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure a T)) :
    cuspGreenCollarResponse a T 0 f t = cuspGreenCollarResponse a T 0 f T := by
  simpa using cuspGreenCollarResponse_eq_outgoing a T t ht 0 f

end GapFamily.Analytic
