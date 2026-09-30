import BTZEntropy.Analytic.SaddleRescaledTail
import BTZEntropy.Analytic.IntegralTaylor
import BTZEntropy.Analytic.SaddleLocal

/-!
# Whole-contour expansion from the local saddle estimate

The complement of the closed local interval is contained in the closed tail.
Absolute integrability therefore combines the local Taylor remainder and the
nonlocal suppression without a boundary convention or an integral substitution.
-/

noncomputable section

open MeasureTheory

namespace BTZEntropy

/-- A local remainder and an absolute tail bound control the whole integral. -/
theorem norm_integral_sub_le_of_local_and_tail {f : ℝ → ℂ} {S T : Set ℝ}
    {P : ℂ} {A B : ℝ} (hf : Integrable f) (hS : MeasurableSet S)
    (hST : Sᶜ ⊆ T) (hlocal : ‖(∫ t in S, f t) - P‖ ≤ A)
    (htail : (∫ t in T, ‖f t‖) ≤ B) :
    ‖(∫ t : ℝ, f t) - P‖ ≤ A + B := by
  have hc : ‖∫ t in Sᶜ, f t‖ ≤ B := by
    calc
      _ ≤ ∫ t in Sᶜ, ‖f t‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t in T, ‖f t‖ := setIntegral_mono_set hf.norm.integrableOn
        (Filter.Eventually.of_forall (fun t => norm_nonneg (f t)))
        (Filter.Eventually.of_forall hST)
      _ ≤ B := htail
  rw [← integral_add_compl hS hf]
  calc
    _ = ‖((∫ t in S, f t) - P) + ∫ t in Sᶜ, f t‖ := by congr 1; abel
    _ ≤ ‖(∫ t in S, f t) - P‖ + ‖∫ t in Sᶜ, f t‖ := norm_add_le _ _
    _ ≤ A + B := add_le_add hlocal hc

/-- The nonlocal estimate turns a uniform actual local Taylor bound into the
same order of expansion on the entire real contour. -/
theorem actualRescaledSaddle_wholeTaylor_of_local (φ : SmoothKernel)
    {L U R : ℝ} (hL : 0 < L) (hLU : L ≤ U) (hR : 0 < R) (N : ℕ)
    (hlocal : ∃ C > 0, ∀ x ∈ Set.Icc L U, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ‖(∫ t in {t : ℝ | |ε * t| ≤ R},
        rescaledSaddleIntegrand (complexAmplitude φ) (saddleBeta x) t (ε : ℂ)) -
          Analytic.integralTaylorPolynomial volume
            (fun e t : ℝ => rescaledSaddleIntegrand (complexAmplitude φ)
              (saddleBeta x) t (e : ℂ)) N ε‖ ≤ C * ε ^ (N + 1)) :
    ∃ C > 0, ∀ x ∈ Set.Icc L U, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ‖rescaledBTZContour φ x ε - Analytic.integralTaylorPolynomial volume
        (fun e t : ℝ => rescaledSaddleIntegrand (complexAmplitude φ)
          (saddleBeta x) t (e : ℂ)) N ε‖ ≤ C * ε ^ (N + 1) := by
  obtain ⟨C₀, hC₀, hbound⟩ := hlocal
  obtain ⟨C₁, hC₁, htail⟩ := actualRescaledSaddle_tail_uniform φ hL hLU hR (N + 1)
  refine ⟨C₀ + C₁, add_pos hC₀ hC₁, ?_⟩
  intro x hx ε hε hε1
  unfold rescaledBTZContour
  rw [add_mul]
  apply norm_integral_sub_le_of_local_and_tail
    (integrable_rescaledBTZContour φ (hL.trans_le hx.1) (ne_of_gt hε))
    (measurableSet_le ((continuous_const.mul continuous_id).abs.measurable) measurable_const)
    (S := {t : ℝ | |ε * t| ≤ R}) (T := {t : ℝ | R ≤ |ε * t|})
  · intro t ht
    change ¬ |ε * t| ≤ R at ht
    exact (lt_of_not_ge ht).le
  · exact hbound x hx ε hε hε1
  · exact htail x hx ε hε hε1

/-- Uniform finite Taylor expansion of the actual whole rescaled BTZ contour.
The local analytic estimate and the nonlocal tail are both discharged. -/
theorem actualRescaledSaddle_wholeTaylor_uniform (φ : SmoothKernel)
    {L U : ℝ} (hL : 0 < L) (hLU : L ≤ U) (N : ℕ) :
    ∃ C > 0, ∀ x ∈ Set.Icc L U, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ‖rescaledBTZContour φ x ε - Analytic.integralTaylorPolynomial volume
        (fun e t : ℝ => rescaledSaddleIntegrand (complexAmplitude φ)
          (saddleBeta x) t (e : ℂ)) N ε‖ ≤ C * ε ^ (N + 1) := by
  apply actualRescaledSaddle_wholeTaylor_of_local φ hL hLU
    (show 0 < saddleBeta U / 4 by exact div_pos (saddleBeta_pos (hL.trans_le hLU)) (by norm_num)) N
  obtain ⟨C, hC, hb⟩ := uniform_localSaddleIntegral_taylor φ hL hLU N
  refine ⟨C, hC, ?_⟩
  intro x hx ε hε hε1
  simpa only [saddleLocalDomain, abs_of_pos hε] using (hb x hx ε).2

end BTZEntropy
