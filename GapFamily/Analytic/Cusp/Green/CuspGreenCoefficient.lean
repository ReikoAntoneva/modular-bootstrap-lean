import GapFamily.Analytic.Cusp.Green.CuspGreenScalarResponse
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Actual collar coefficient extraction

The coefficient map is the Hilbert adjoint of the proved source isometry.
Its action on compact scalar profiles is the literal logarithmic restriction.
-/

noncomputable section
namespace GapFamily.Analytic

open Set MeasureTheory ModularGradient
open scoped ContDiff

/-- The actual bounded coefficient map adjoint to logarithmic collar source lifting. -/
def cuspGreenSourceCoefficient (T : ℝ) :
    ModularHilbert →L[ℂ] Lp ℂ 2 (cuspGreenCollarMeasure 0 T) :=
  (cuspGreenSourceEmbedding T).toContinuousLinearMap.adjoint

theorem cuspGreenSourceCoefficient_inner_left (T : ℝ)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure 0 T)) (F : ModularHilbert) :
    inner ℂ (cuspGreenSourceCoefficient T F) f =
      inner ℂ F (cuspGreenSourceEmbedding T f) :=
  (cuspGreenSourceEmbedding T).toContinuousLinearMap.adjoint_inner_left f F

theorem cuspGreenSourceCoefficient_inner_right (T : ℝ)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure 0 T)) (F : ModularHilbert) :
    inner ℂ f (cuspGreenSourceCoefficient T F) =
      inner ℂ (cuspGreenSourceEmbedding T f) F :=
  (cuspGreenSourceEmbedding T).toContinuousLinearMap.adjoint_inner_right f F

/-- Coefficient extraction recovers every source class exactly. -/
@[simp] theorem cuspGreenSourceCoefficient_embedding (T : ℝ)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure 0 T)) :
    cuspGreenSourceCoefficient T (cuspGreenSourceEmbedding T f) = f := by
  apply ext_inner_right ℂ
  intro g
  rw [cuspGreenSourceCoefficient_inner_left]
  exact (cuspGreenSourceEmbedding T).inner_map_map f g

theorem cuspGreenSourceCoefficient_opNorm_le (T : ℝ) :
    ‖cuspGreenSourceCoefficient T‖ ≤ 1 := by
  unfold cuspGreenSourceCoefficient
  rw [ContinuousLinearMap.adjoint.norm_map]
  exact (cuspGreenSourceEmbedding T).norm_toContinuousLinearMap_le

/-- The true coefficient map is a contraction, including degenerate collars. -/
theorem cuspGreenSourceCoefficient_norm_le (T : ℝ) (F : ModularHilbert) :
    ‖cuspGreenSourceCoefficient T F‖ ≤ ‖F‖ := by
  calc
    _ ≤ ‖cuspGreenSourceCoefficient T‖ * ‖F‖ :=
      (cuspGreenSourceCoefficient T).le_opNorm F
    _ ≤ 1 * ‖F‖ := mul_le_mul_of_nonneg_right
      (cuspGreenSourceCoefficient_opNorm_le T) (norm_nonneg F)
    _ = _ := one_mul _

/-- The residual after coefficient extraction and lifting is orthogonal to every lifted source. -/
theorem cuspGreenSourceCoefficient_residual_orthogonal (T : ℝ)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure 0 T)) (F : ModularHilbert) :
    inner ℂ (cuspGreenSourceEmbedding T f)
      (F - cuspGreenSourceEmbedding T (cuspGreenSourceCoefficient T F)) = 0 := by
  rw [inner_sub_right, ← cuspGreenSourceCoefficient_inner_right T f F,
    (cuspGreenSourceEmbedding T).inner_map_map, sub_self]

/-- On every actual compact scalar core, the adjoint is its literal logarithmic collar profile. -/
theorem cuspGreenSourceCoefficient_profileCore (T : ℝ)
    (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b)
    (hs : tsupport b ⊆ Ioi 1) :
    cuspGreenSourceCoefficient T (value (cuspProfileCore b hb hc hs)) =
      cuspGreenCollarSource 0 T (cuspLogCoordinate b)
        (continuous_cuspLogCoordinate hb.continuous) := by
  apply ext_inner_right ℂ
  intro f
  rw [cuspGreenSourceCoefficient_inner_left,
    cuspGreenSourceEmbedding_compact_pairing T f b hb hc hs]
  exact (cuspGreenCollarSource_inner_integral T (cuspLogCoordinate b)
    (continuous_cuspLogCoordinate hb.continuous) f).2.symm

end GapFamily.Analytic
