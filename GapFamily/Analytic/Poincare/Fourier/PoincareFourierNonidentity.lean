import GapFamily.Analytic.Poincare.Fourier.PoincareFourierIdentity

/-! Actual convergence certificates on the nonidentity cusp quotient. -/
noncomputable section
namespace GapFamily.Analytic.PoincareFourierRegroup
open Set MeasureTheory PoincareFourier

/-- Restricting the proved integrated-norm convergence to the actual nonidentity cosets. -/
theorem summable_integral_norm_nonidentity (j J : ℤ) {s : ℂ} (hs : 1 < s.re)
    (y : ℝ) (hy : 0 < y) :
    Summable (fun q : {q : CuspCoset // q ≠ identityCuspCoset} =>
      ∫ x in (0 : ℝ)..1, ‖fourierTerm j J s y hy q.val x‖) :=
  (summable_integral_norm_fourierTerm j J hs y hy).subtype _

/-- The nonidentity subseries has the actual Fourier coefficient minus its exact diagonal term. -/
theorem hasSum_integral_nonidentity (j J : ℤ) {s : ℂ} (hs : 1 < s.re)
    (y : ℝ) (hy : 0 < y) :
    HasSum (fun q : {q : CuspCoset // q ≠ identityCuspCoset} =>
      ∫ x in (0 : ℝ)..1, fourierTerm j J s y hy q.val x)
      ((∫ x in (0 : ℝ)..1, fourierSeries j J s y hy x) -
        (if j = J then (y : ℂ) ^ s else 0)) := by
  classical
  apply (hasSum_subtype_iff_indicator
    (f := fun q : CuspCoset => ∫ x in (0 : ℝ)..1, fourierTerm j J s y hy q x)
    (s := {q : CuspCoset | q ≠ identityCuspCoset})).mpr
  convert hasSum_integral_fourierTerm_nonidentity j J hs y hy using 1
  funext q
  by_cases hq : q = identityCuspCoset <;> simp [Set.indicator, hq]

end GapFamily.Analytic.PoincareFourierRegroup
