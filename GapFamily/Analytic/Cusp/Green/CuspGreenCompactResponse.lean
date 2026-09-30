import GapFamily.Analytic.Cusp.Green.CuspGreenCoefficient
import GapFamily.Analytic.Cusp.Green.CuspGreenHeightSupport
import GapFamily.Analytic.Cusp.Scalar.CuspScalarSourcePairing
import GapFamily.Analytic.Cusp.Green.CuspGreenSourceRepresentative

noncomputable section
namespace GapFamily.Analytic
open Set MeasureTheory ModularGradient
open scoped ContDiff

/-- Extracting and re-lifting the coefficient of an actual compact scalar test
is its literal height truncation. -/
theorem cuspGreenSourceEmbedding_coefficient_profileCore {T : ℝ} (hT : 0 ≤ T)
    (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b)
    (hs : tsupport b ⊆ Ioi 1) :
    cuspGreenSourceEmbedding T
      (cuspGreenSourceCoefficient T (value (cuspProfileCore b hb hc hs))) =
      modularLowCut (Real.exp T) (value (cuspProfileCore b hb hc hs)) := by
  rw [cuspGreenSourceCoefficient_profileCore]
  apply Lp.ext
  filter_upwards [cuspGreenSourceEmbedding_continuous_ae T hT (cuspLogCoordinate b)
      (continuous_cuspLogCoordinate hb.continuous),
    modularLowCut_ae (Real.exp T) (value (cuspProfileCore b hb hc hs)),
    cuspProfileCore_value_ae b hb hc hs] with τ hJ hcut hvalue
  rw [hJ, hcut]
  by_cases hy : 1 < τ.im
  · by_cases hTτ : τ.im ≤ Real.exp T
    · simp only [hy, hTτ, and_self, ite_true, indicator_of_mem, mem_ofPred_eq, hvalue]
      exact cuspLift_cuspLogCoordinate (zero_lt_one.trans hy)
    · simp only [hy, hTτ, and_false, ite_false]
      exact (indicator_of_notMem (show τ ∉ {τ : UpperHalfPlane | τ.im ≤ Real.exp T} from hTτ) _).symm
  · have hbzero : b τ.im = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hy (hs h))
    simp only [hy, false_and, ite_false]
    by_cases hTτ : τ.im ≤ Real.exp T
    · rw [indicator_of_mem (show τ ∈ {τ : UpperHalfPlane | τ.im ≤ Real.exp T} from hTτ), hvalue, hbzero]
    · exact (indicator_of_notMem (show τ ∉ {τ : UpperHalfPlane | τ.im ≤ Real.exp T} from hTτ) _).symm

/-- A source with a literal finite upper-height support is seen by scalar tests
exactly through the adjoint-extracted logarithmic collar coefficient. -/
theorem cuspGreenSourceCoefficient_pairing_of_highCut_zero {T : ℝ} (hT : 0 ≤ T)
    (F : ModularHilbert) (hF : modularHighCut (Real.exp T) F = 0)
    (w : cuspScalarForm) :
    inner ℂ (scalarCuspEmbedding w)
      (cuspGreenSourceEmbedding T (cuspGreenSourceCoefficient T F)) =
      inner ℂ (scalarCuspEmbedding w) F := by
  apply cuspScalarForm_source_pairing_of_compact
  intro b hb hc hs
  rw [← cuspGreenSourceCoefficient_inner_left,
    cuspGreenSourceCoefficient_inner_right,
    cuspGreenSourceEmbedding_coefficient_profileCore hT b hb hc hs]
  exact modularLowCut_inner_of_highCut_zero (Real.exp T) F _ hF

/-- The actual physical scalar response to a height-supported ambient modular
L² source is the existing literal Green response of its extracted coefficient. -/
theorem cuspScalarPencilSolution_eq_greenCoefficient {T : ℝ} (hT : 0 ≤ T)
    {κ : ℂ} (hκ : 0 < κ.re) (F : ModularHilbert)
    (hF : modularHighCut (Real.exp T) F = 0) :
    cuspScalarPencilSolution (1/4 - κ^2) F =
      cuspGreenScalarFormOperator T κ (cuspGreenSourceCoefficient T F) := by
  symm
  apply cuspScalarPencilSolution_unique_physical hκ
  intro w
  exact (cuspGreenScalarFormOperator_weak hκ (cuspGreenSourceCoefficient T F) w).trans
    (cuspGreenSourceCoefficient_pairing_of_highCut_zero hT F hF w)

/-- Its actual modular Hilbert representative is the ordinary scalar Green integral. -/
theorem cuspScalarPencilSolution_greenCoefficient_ae {T : ℝ} (hT : 0 ≤ T)
    {κ : ℂ} (hκ : 0 < κ.re) (F : ModularHilbert)
    (hF : modularHighCut (Real.exp T) F = 0) :
    scalarCuspEmbedding (cuspScalarPencilSolution (1/4 - κ^2) F) =ᵐ[modularMeasure]
      fun τ : UpperHalfPlane => if 1 < τ.im then Real.sqrt τ.im •
        cuspGreenCollarResponse 0 T κ (cuspGreenSourceCoefficient T F) (Real.log τ.im) else 0 := by
  rw [cuspScalarPencilSolution_eq_greenCoefficient hT hκ F hF]
  exact cuspGreenScalarResponseOperator_ae hT hκ _

/-- Every compact AE-supported modular Hilbert source has a single source collar
that gives its genuine physical scalar Green response for every Re κ > 0. -/
theorem exists_cuspScalarPencilSolution_greenCoefficient_of_compact (F : ModularHilbert)
    {K : Set UpperHalfPlane} (hK : IsCompact K)
    (hF : ∀ᵐ τ ∂modularMeasure, τ ∉ K → F τ = 0) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ (κ : ℂ), 0 < κ.re →
      cuspScalarPencilSolution (1/4 - κ^2) F =
        cuspGreenScalarFormOperator T κ (cuspGreenSourceCoefficient T F) := by
  obtain ⟨T, hT, hTF⟩ := exists_cuspGreen_source_height_of_compact F hK hF
  exact ⟨T, hT, fun κ hκ => cuspScalarPencilSolution_eq_greenCoefficient hT hκ F hTF⟩

end GapFamily.Analytic
