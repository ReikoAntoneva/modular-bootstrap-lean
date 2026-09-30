import GapFamily.Analytic.Modular.Elliptic.ModularUpperCutoffGradientCore
import GapFamily.Analytic.Modular.Elliptic.ModularInteriorCompactUpperEnergy
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Actual ordinary cutoff gradient fields on the completed modular form domain

The finite translated-tile energy bound controls the literal Euclidean
fields χ ∂v F, including cutoffs crossing fundamental-domain seams. Their
continuous extension uses the proved dense smooth core in the actual form
norm. No weak-PDE or seam-regularity premise is introduced.
-/

noncomputable section
namespace GapFamily.Analytic.ModularGradient
open Set MeasureTheory UpperHalfPlane Filter
open scoped ContDiff Topology

theorem upperCutoffGradient_pointwise_le {χ : ℂ → ℂ} {A : ℝ} (hA : 0 ≤ A)
    (hb : ∀ z ∈ tsupport χ, ‖χ z‖ ≤ A) (F : smoothCore) (v : ℂ)
    {z : ℂ} (hz : z ∈ tsupport χ) :
    ‖χ z * fderiv ℝ F.val z v‖ ^ 2 ≤ 2 * A ^ 2 * ‖v‖ ^ 2 *
      (‖F.val z‖ ^ 2 + ‖fderiv ℝ F.val z 1‖ ^ 2 +
        ‖fderiv ℝ F.val z Complex.I‖ ^ 2) := by
  have hd : ‖fderiv ℝ F.val z v‖ ≤
      (‖fderiv ℝ F.val z 1‖ + ‖fderiv ℝ F.val z Complex.I‖) * ‖v‖ :=
    ((fderiv ℝ F.val z).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (complex_real_opNorm_le _) (norm_nonneg _))
  have hm : ‖χ z * fderiv ℝ F.val z v‖ ≤
      A * ((‖fderiv ℝ F.val z 1‖ + ‖fderiv ℝ F.val z Complex.I‖) * ‖v‖) := by
    rw [norm_mul]
    exact mul_le_mul (hb z hz) hd (norm_nonneg _) hA
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hm 2
  have hn : 0 ≤ A ^ 2 * ‖v‖ ^ 2 *
      ((‖fderiv ℝ F.val z 1‖ - ‖fderiv ℝ F.val z Complex.I‖) ^ 2 +
        2 * ‖F.val z‖ ^ 2) := by positivity
  nlinarith only [hsq, hn]

/-- A genuine finite-tile bound for the ordinary cutoff gradient on the smooth core. -/
theorem exists_upperCutoffGradientCoreMap_bound {χ : ℂ → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet) (v : ℂ) :
    ∃ B : ℝ, 0 < B ∧ ∀ F : smoothCore,
      ‖upperCutoffGradientCoreMap χ hχ hc hs v F‖ ≤ B * ‖coreForm F‖ := by
  obtain ⟨A, hA, hb⟩ := exists_upperCutoff_coefficient_bound hχ hc
  obtain ⟨C, hC, hlocal⟩ := exists_compact_euclidean_graphEnergy_bound hc hs
  let D := 2 * A ^ 2 * ‖v‖ ^ 2 * C
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hDb : D ≤ (D + 1) ^ 2 := by nlinarith [sq_nonneg D]
  refine ⟨D + 1, by positivity, fun F => ?_⟩
  obtain ⟨hint, hlocalF⟩ := hlocal F
  have hI : (∫ z : ℂ, ‖χ z * fderiv ℝ F.val z v‖ ^ 2) ≤ D * ‖coreForm F‖ ^ 2 := by
    calc
      _ = ∫ z in tsupport χ, ‖χ z * fderiv ℝ F.val z v‖ ^ 2 := by
        symm
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro z hz
        simp [image_eq_zero_of_notMem_tsupport hz]
      _ ≤ ∫ z in tsupport χ, 2 * A ^ 2 * ‖v‖ ^ 2 *
          (‖F.val z‖ ^ 2 + ‖fderiv ℝ F.val z 1‖ ^ 2 +
            ‖fderiv ℝ F.val z Complex.I‖ ^ 2) := by
        apply integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun _ => sq_nonneg _) (hint.const_mul _)
        filter_upwards [ae_restrict_mem (isClosed_tsupport χ).measurableSet] with z hz
        exact upperCutoffGradient_pointwise_le hA.le (fun z hz => (hb z hz).1) F v hz
      _ = (2 * A ^ 2 * ‖v‖ ^ 2) * ∫ z in tsupport χ,
          (‖F.val z‖ ^ 2 + ‖fderiv ℝ F.val z 1‖ ^ 2 +
            ‖fderiv ℝ F.val z Complex.I‖ ^ 2) := integral_const_mul _ _
      _ ≤ (2 * A ^ 2 * ‖v‖ ^ 2) *
          (C * (‖value F‖ ^ 2 + ‖coreGradient F‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hlocalF (by positivity)
      _ = D * ‖coreForm F‖ ^ 2 := by rw [coreForm_norm_sq]; dsimp [D]; ring
  have hsq : ‖upperCutoffGradientCoreMap χ hχ hc hs v F‖ ^ 2 ≤
      ((D + 1) * ‖coreForm F‖) ^ 2 := by
    rw [upperCutoffGradientCoreMap_norm_sq]
    calc
      _ ≤ D * ‖coreForm F‖ ^ 2 := hI
      _ ≤ (D + 1) ^ 2 * ‖coreForm F‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hDb (sq_nonneg _)
      _ = _ := by ring
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsq

/-- Bounded ordinary Euclidean gradient field on the actual completed form domain.
The directions `1` and `Complex.I` are the horizontal and vertical components. -/
def upperCutoffGradientOperator (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ upperHalfPlaneSet) (v : ℂ) :
    FormDomain →L[ℂ] Lp ℂ 2 (volume : Measure ℂ) := by
  have _hbound := exists_upperCutoffGradientCoreMap_bound hχ hc hs v
  exact (upperCutoffGradientCoreMap χ hχ hc hs v).extendOfNorm coreForm

@[simp] theorem upperCutoffGradientOperator_coreForm (χ : ℂ → ℂ)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet) (v : ℂ) (F : smoothCore) :
    upperCutoffGradientOperator χ hχ hc hs v (coreForm F) =
      upperCutoffGradientCoreMap χ hχ hc hs v F := by
  obtain ⟨B, _, hB⟩ := exists_upperCutoffGradientCoreMap_bound hχ hc hs v
  exact LinearMap.extendOfNorm_eq coreForm_denseRange ⟨B, hB⟩ F

/-- Exact core identification with χ times the ordinary derivative, not a
 derivative of χF and not the hyperbolic frame coefficient y∂vF. -/
theorem upperCutoffGradientOperator_coreForm_ae (χ : ℂ → ℂ)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet) (v : ℂ) (F : smoothCore) :
    upperCutoffGradientOperator χ hχ hc hs v (coreForm F) =ᵐ[(volume : Measure ℂ)]
      fun z => χ z * fderiv ℝ F.val z v := by
  rw [upperCutoffGradientOperator_coreForm]
  exact upperCutoffGradientCoreMap_ae χ hχ hc hs v F

theorem exists_upperCutoffGradientOperator_bound {χ : ℂ → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet) (v : ℂ) :
    ∃ B : ℝ, 0 < B ∧ ‖upperCutoffGradientOperator χ hχ hc hs v‖ ≤ B := by
  obtain ⟨B, hB, hnorm⟩ := exists_upperCutoffGradientCoreMap_bound hχ hc hs v
  exact ⟨B, hB, LinearMap.opNorm_extendOfNorm_le coreForm_denseRange hB.le hnorm⟩

/-- Every genuine form-core approximation converges to the constructed local field. -/
theorem upperCutoffGradientCoreMap_tendsto {χ : ℂ → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet) (v : ℂ)
    (F : ℕ → smoothCore) (u : FormDomain)
    (hF : Tendsto (fun n => coreForm (F n)) atTop (𝓝 u)) :
    Tendsto (fun n => upperCutoffGradientCoreMap χ hχ hc hs v (F n)) atTop
      (𝓝 (upperCutoffGradientOperator χ hχ hc hs v u)) := by
  simpa only [Function.comp_def, upperCutoffGradientOperator_coreForm] using
    (upperCutoffGradientOperator χ hχ hc hs v).continuous.continuousAt.tendsto.comp hF

end GapFamily.Analytic.ModularGradient
