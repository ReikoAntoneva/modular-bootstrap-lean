import GapFamily.Analytic.Modular.ModularProjectedResponseBasic
import GapFamily.Analytic.Modular.ModularQuarterGap
import GapFamily.Analytic.Foundation.PositiveQuarterPencil

noncomputable section
namespace GapFamily.Analytic.ModularProjected
open ModularGradient

/-- The actual projected response obeys the sharp quarter-gap resolvent bound. -/
theorem projectedWeakResolvent_bound (f : ModularHilbert) :
    ‖projectedWeakResolvent f‖ ≤ (4 / 5 : ℝ) * ‖f‖ := by
  let g := modularMeanZeroProjection f
  let u := weakSolution g
  have horth : inner ℂ modularConstant (formEmbedding u) = 0 := by
    change inner ℂ modularConstant (weakResolvent (modularMeanZeroProjection f)) = 0
    rw [weakResolvent_meanZeroProjection, modularConstant_inner]
    exact modularMeanZeroProjection_integral _
  have hgap := form_quarter_mass_le_energy_of_constant_orthogonal u horth
  have henergy := weakSolution_equation g u
  change inner ℂ (formGradient u) (formGradient u) +
      inner ℂ (formEmbedding u) (formEmbedding u) = inner ℂ g (formEmbedding u) at henergy
  have he : ‖formGradient u‖ ^ 2 + ‖formEmbedding u‖ ^ 2 =
      (inner ℂ g (formEmbedding u)).re := by
    have h := congrArg Complex.re henergy
    have hE : (inner ℂ (formGradient u) (formGradient u)).re = ‖formGradient u‖ ^ 2 :=
      inner_self_eq_norm_sq (𝕜 := ℂ) (formGradient u)
    have hM : (inner ℂ (formEmbedding u) (formEmbedding u)).re = ‖formEmbedding u‖ ^ 2 :=
      inner_self_eq_norm_sq (𝕜 := ℂ) (formEmbedding u)
    simpa only [Complex.add_re, hE, hM] using h
  have hc : (inner ℂ g (formEmbedding u)).re ≤ ‖g‖ * ‖formEmbedding u‖ :=
    re_inner_le_norm (𝕜 := ℂ) _ _
  have hg : ‖g‖ ≤ ‖f‖ := by
    calc
      ‖g‖ ≤ ‖modularMeanZeroProjection‖ * ‖f‖ := modularMeanZeroProjection.le_opNorm f
      _ ≤ 1 * ‖f‖ := mul_le_mul_of_nonneg_right modularMeanZeroProjection_norm_le (norm_nonneg _)
      _ = ‖f‖ := one_mul _
  have hc' : (inner ℂ g (formEmbedding u)).re ≤ ‖f‖ * ‖formEmbedding u‖ :=
    hc.trans (mul_le_mul_of_nonneg_right hg (norm_nonneg _))
  have hn : ‖formEmbedding u‖ ≤ (4 / 5 : ℝ) * ‖f‖ := by
    by_cases hz : ‖formEmbedding u‖ = 0
    · rw [hz]
      positivity
    · have hp : 0 < ‖formEmbedding u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
      have hbound : ((5 / 4 : ℝ) * ‖formEmbedding u‖) * ‖formEmbedding u‖ ≤
          ‖f‖ * ‖formEmbedding u‖ := by
        nlinarith [hgap, he, hc']
      have hlin := (mul_le_mul_iff_of_pos_right hp).mp hbound
      linarith
  rw [projectedWeakResolvent_eq_resolvent_projection]
  exact hn

/-- The actual projected ambient shifted response has operator norm at most four fifths. -/
theorem projectedWeakResolvent_norm_le_four_fifths :
    ‖projectedWeakResolvent‖ ≤ (4 / 5 : ℝ) :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num) projectedWeakResolvent_bound

/-- The actual projected response pencil; no compactness hypothesis is involved. -/
def projectedPencil (z : ℂ) : ModularHilbert →L[ℂ] ModularHilbert :=
  1 - (z + 1) • projectedWeakResolvent

theorem projectedPencil_isUnit_regular {z : ℂ}
    (hz : z.im ≠ 0 ∨ z.re < (1 / 4 : ℝ)) : IsUnit (projectedPencil z) :=
  positiveQuarterPencil_isUnit projectedWeakResolvent projectedWeakResolvent_isPositive
    projectedWeakResolvent_norm_le_four_fifths hz

theorem projectedPencil_isUnit_physical {κ : ℂ} (hκ : 0 < κ.re) :
    IsUnit (projectedPencil ((1 / 4 : ℂ) - κ ^ 2)) :=
  positiveQuarterPencil_isUnit_physical projectedWeakResolvent projectedWeakResolvent_isPositive
    projectedWeakResolvent_norm_le_four_fifths hκ

end GapFamily.Analytic.ModularProjected
