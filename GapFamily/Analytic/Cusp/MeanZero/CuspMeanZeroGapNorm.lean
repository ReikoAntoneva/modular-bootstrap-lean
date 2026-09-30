import GapFamily.Analytic.Cusp.MeanZero.CuspMeanZeroResolvent

/-!
# The constrained response norm from an explicit mass–energy gap

The stated mass bound implies that at most five sevenths of the actual form
norm is mass. The adjoint identity for the actual response `i i†` then gives
its quantitative operator norm. The gap remains an explicit premise, and no
compactness argument is used.
-/

noncomputable section

namespace GapFamily.Analytic

open ModularGradient

private theorem gap_formResolvent_norm_sq {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (i : V →L[ℂ] H) : ‖Dirichlet.formResolvent i‖ = ‖i‖ ^ 2 := by
  have h := ContinuousLinearMap.norm_adjoint_comp_self i.adjoint
  simpa only [ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.adjoint.norm_map,
    pow_two, Dirichlet.formResolvent] using h

/-- The actual mass fraction follows from the explicit constrained energy gap. -/
theorem meanZeroCuspEmbedding_norm_sq_le_five_sevenths_of_mass_le
    (hgap : ∀ v : cuspMeanZeroForm,
      ‖meanZeroCuspEmbedding v‖ ^ 2 ≤ (5 / 2 : ℝ) * ‖cuspMeanZeroGradient v‖ ^ 2)
    (v : cuspMeanZeroForm) :
    ‖meanZeroCuspEmbedding v‖ ^ 2 ≤ (5 / 7 : ℝ) * ‖v‖ ^ 2 := by
  have hg := hgap v
  have hn := cuspMeanZeroForm_norm_sq v
  linarith

/-- The embedding bound in the genuine complete constrained form norm. -/
theorem meanZeroCuspEmbedding_opNorm_le_sqrt_five_sevenths_of_mass_le
    (hgap : ∀ v : cuspMeanZeroForm,
      ‖meanZeroCuspEmbedding v‖ ^ 2 ≤ (5 / 2 : ℝ) * ‖cuspMeanZeroGradient v‖ ^ 2) :
    ‖meanZeroCuspEmbedding‖ ≤ Real.sqrt (5 / 7 : ℝ) := by
  apply @ContinuousLinearMap.opNorm_le_bound ℂ ℂ cuspMeanZeroForm ModularHilbert
    (inferInstance : SeminormedAddCommGroup cuspMeanZeroForm)
    (inferInstance : SeminormedAddCommGroup ModularHilbert) inferInstance inferInstance
    (inferInstance : NormedSpace ℂ cuspMeanZeroForm)
    (inferInstance : NormedSpace ℂ ModularHilbert) (RingHom.id ℂ)
    meanZeroCuspEmbedding (Real.sqrt (5 / 7 : ℝ)) (Real.sqrt_nonneg _)
  intro v
  have h := meanZeroCuspEmbedding_norm_sq_le_five_sevenths_of_mass_le hgap v
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5 / 7)
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, hs]
  exact h

/-- The actual ambient response is `i i†`, so its norm is the squared embedding norm. -/
theorem cuspMeanZeroWeakResolvent_norm_eq_embedding_norm_sq :
    ‖cuspMeanZeroWeakResolvent‖ = ‖meanZeroCuspEmbedding‖ ^ 2 := by
  unfold cuspMeanZeroWeakResolvent
  have h := gap_formResolvent_norm_sq (V := cuspMeanZeroForm) (H := ModularHilbert)
    meanZeroCuspEmbedding
  exact h

/-- The explicit mass–energy gap bounds the genuine constrained response by `5/7`. -/
theorem cuspMeanZeroWeakResolvent_norm_le_five_sevenths_of_mass_le
    (hgap : ∀ v : cuspMeanZeroForm,
      ‖meanZeroCuspEmbedding v‖ ^ 2 ≤ (5 / 2 : ℝ) * ‖cuspMeanZeroGradient v‖ ^ 2) :
    ‖cuspMeanZeroWeakResolvent‖ ≤ (5 / 7 : ℝ) := by
  rw [cuspMeanZeroWeakResolvent_norm_eq_embedding_norm_sq]
  have hn := meanZeroCuspEmbedding_opNorm_le_sqrt_five_sevenths_of_mass_le hgap
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5 / 7)
  nlinarith [norm_nonneg meanZeroCuspEmbedding]

end GapFamily.Analytic
