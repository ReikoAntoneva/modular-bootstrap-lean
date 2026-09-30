import GapFamily.Analytic.Poincare.PoincarePrimitiveSpin
import GapFamily.Analytic.Poincare.Fourier.PoincareFourierIntegral

/-! Ordinary Fourier coefficients as convergent signed primitive-row integral series. -/
noncomputable section
namespace GapFamily.Analytic.PoincareFourier
open Set MeasureTheory UpperHalfPlane
open scoped Topology MatrixGroups

/-- The literal ordinary Fourier integrand for an actual primitive-row representative. -/
def primitiveFourierTerm (j J : ℤ) (s : ℂ) (y : ℝ) (hy : 0 < y)
    (v : PrimitiveRow) (x : ℝ) : ℂ :=
  cuspFourierMode (-j) x * primitiveSpinTerm J s (rowPoint y hy x) v

theorem primitiveFourierTerm_signed (j J : ℤ) (s : ℂ) (y : ℝ) (hy : 0 < y)
    (q : CuspCoset) (b : Bool) (x : ℝ) :
    primitiveFourierTerm j J s y hy (cuspSignedRowEquiv (q, b)) x =
      fourierTerm j J s y hy q x := by
  simp only [primitiveFourierTerm, primitiveSpinTerm_signed, fourierTerm]

/-- Every primitive-row integrand has a genuine ordinary interval integral. -/
theorem intervalIntegrable_primitiveFourierTerm (j J : ℤ) (s : ℂ) (y : ℝ)
    (hy : 0 < y) (v : PrimitiveRow) :
    IntervalIntegrable (primitiveFourierTerm j J s y hy v) volume 0 1 := by
  obtain ⟨⟨q, b⟩, rfl⟩ := cuspSignedRowEquiv.surjective v
  have heq : primitiveFourierTerm j J s y hy (cuspSignedRowEquiv (q, b)) =
      fourierTerm j J s y hy q := funext (primitiveFourierTerm_signed j J s y hy q b)
  rw [heq]
  exact intervalIntegrable_fourierTerm j J s y hy q

/-- The actual integral norms over both signs of the primitive rows are summable. -/
theorem summable_integral_norm_primitiveFourierTerm (j J : ℤ) {s : ℂ}
    (hs : 1 < s.re) (y : ℝ) (hy : 0 < y) :
    Summable (fun v : PrimitiveRow => ∫ x in (0 : ℝ)..1,
      ‖primitiveFourierTerm j J s y hy v x‖) := by
  apply cuspSignedRowEquiv.summable_iff.mp
  have h : Summable (fun p : CuspCoset × Bool =>
      ∫ x in (0 : ℝ)..1, ‖fourierTerm j J s y hy p.1 x‖) := by
    apply (summable_prod_of_nonneg (fun p : CuspCoset × Bool =>
      intervalIntegral.integral_nonneg_of_forall zero_le_one (fun x => norm_nonneg _))).mpr
    refine ⟨fun q => by apply summable_of_hasFiniteSupport; exact Set.toFinite _, ?_⟩
    simpa only [tsum_bool, ← two_mul] using
      (summable_integral_norm_fourierTerm j J hs y hy).mul_left 2
  apply h.congr
  rintro ⟨q, b⟩
  simp only [Function.comp_def, primitiveFourierTerm_signed]

/-- Absolute convergence of the actual primitive-row Fourier integrals. -/
theorem summable_norm_integral_primitiveFourierTerm (j J : ℤ) {s : ℂ}
    (hs : 1 < s.re) (y : ℝ) (hy : 0 < y) :
    Summable (fun v : PrimitiveRow =>
      ‖∫ x in (0 : ℝ)..1, primitiveFourierTerm j J s y hy v x‖) :=
  (summable_integral_norm_primitiveFourierTerm j J hs y hy).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun _ => intervalIntegral.norm_integral_le_integral_norm zero_le_one)

/-- Both signs give exactly twice the actual ordinary Fourier coefficient. -/
theorem primitiveFourierTerm_integral_sum_eq_two (j J : ℤ) {s : ℂ}
    (hs : 1 < s.re) (y : ℝ) (hy : 0 < y) :
    (∑' v : PrimitiveRow, ∫ x in (0 : ℝ)..1, primitiveFourierTerm j J s y hy v x) =
      2 * ∫ x in (0 : ℝ)..1, fourierSeries j J s y hy x := by
  have hsum := (summable_norm_integral_primitiveFourierTerm j J hs y hy).of_norm
  rw [← cuspSignedRowEquiv.tsum_eq]
  have hp := cuspSignedRowEquiv.summable_iff.mpr hsum
  simp only [Function.comp_def] at hp
  rw [hp.tsum_prod]
  simp_rw [primitiveFourierTerm_signed, tsum_bool, ← two_mul]
  rw [tsum_mul_left, ← integral_fourierSeries_eq_tsum j J hs y hy]

/-- The ordinary coefficient is a true convergent half-weighted signed-row integral series.
The one-half factor occurs here because PrimitiveRow contains both matrix signs. -/
theorem hasSum_half_integral_primitiveFourierTerm (j J : ℤ) {s : ℂ}
    (hs : 1 < s.re) (y : ℝ) (hy : 0 < y) :
    HasSum (fun v : PrimitiveRow => (1 / 2 : ℂ) *
      ∫ x in (0 : ℝ)..1, primitiveFourierTerm j J s y hy v x)
      (∫ x in (0 : ℝ)..1, fourierSeries j J s y hy x) := by
  have h := (summable_norm_integral_primitiveFourierTerm j J hs y hy).of_norm.hasSum.mul_left
    (1 / 2 : ℂ)
  rw [primitiveFourierTerm_integral_sum_eq_two j J hs y hy] at h
  simpa only [← mul_assoc, one_div_mul_cancel (by norm_num : (2 : ℂ) ≠ 0), one_mul] using h

end GapFamily.Analytic.PoincareFourier
