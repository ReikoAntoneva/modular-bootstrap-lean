import GapFamily.Analytic.Modular.Elliptic.ModularEllipticChart
import Mathlib.MeasureTheory.Integral.Bochner.Set

noncomputable section

namespace GapFamily.Analytic.ChartComplexIntegrability

open MeasureTheory

/-- Every integrable complex field pulls back to an integrable field on an arbitrary
coordinate subset. The set need not be measurable. -/
theorem integrable_comp_ellipticChart_restrict
    (z : ℂ) (S : Set (Fin 2 → ℝ)) {g : ℂ → ℂ}
    (hg : Integrable g volume) :
    Integrable (fun v => g (ellipticChart z v)) (volume.restrict S) := by
  exact ((ellipticChart_measurePreserving z).integrable_comp_of_integrable hg).restrict

/-- Exact restricted integrability transport under the volume-preserving affine chart. -/
theorem integrable_comp_ellipticChart_image_iff
    (z : ℂ) (S : Set (Fin 2 → ℝ)) (g : ℂ → ℂ) :
    Integrable (fun v => g (ellipticChart z v)) (volume.restrict S) ↔
      Integrable g (volume.restrict (ellipticChart z '' S)) :=
  (ellipticChart_measurePreserving_restrict_image z S).integrable_comp_emb
    (ellipticChart z).toMeasurableEquiv.measurableEmbedding

/-- A supported chart pullback has the same ordinary Bochner integral as the
original field. This equality of total integrals does not assert integrability. -/
theorem integral_comp_ellipticChart_restrict_of_support
    (z : ℂ) (S : Set (Fin 2 → ℝ)) (g : ℂ → ℂ)
    (h : ∀ v, v ∉ S → g (ellipticChart z v) = 0) :
    (∫ v in S, g (ellipticChart z v)) = ∫ w, g w := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero h]
  exact (ellipticChart_measurePreserving z).integral_comp
    (ellipticChart z).toMeasurableEquiv.measurableEmbedding g

end GapFamily.Analytic.ChartComplexIntegrability
