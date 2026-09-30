import GapFamily.Analytic.Elliptic.GradientLocalIBP
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Bounded compact-test integrals

A continuous compact test supported in K pairs with C(K, ℂ) by a bounded
complex-linear map. Any ambient function agreeing on K gives the same
ordinary integrable product, regardless of its behavior outside K.
-/

noncomputable section

namespace GapFamily.Analytic.PoincareThresholdWeak

open Set MeasureTheory

private def compactAmbient (K : Set ℂ) (A : C(K, ℂ)) (z : ℂ) : ℂ := by
  classical
  exact if hz : z ∈ K then A ⟨z, hz⟩ else 0

/-- Matching a continuous compact-set function suffices for ordinary integrability. -/
theorem compactTestIntegral_integrable (K : Set ℂ) [CompactSpace K]
    (w : ℂ → ℂ) (hw : Continuous w) (hc : HasCompactSupport w)
    (hWK : tsupport w ⊆ K) (A : C(K, ℂ)) (f : ℂ → ℂ)
    (hmatch : ∀ z : K, A z = f z) :
    Integrable (fun z : ℂ => w z * f z) := by
  have hf : ContinuousOn f K := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    change Continuous (fun z : K => f z)
    have he : (fun z : K => f z) = A := by
      funext z
      exact (hmatch z).symm
    rw [he]
    exact A.continuous
  simpa only [mul_comm] using Dirichlet.local_mul_test_integrable hf hw hc hWK

private theorem compactAmbient_integrable (K : Set ℂ) [CompactSpace K]
    (w : ℂ → ℂ) (hw : Continuous w) (hc : HasCompactSupport w)
    (hWK : tsupport w ⊆ K) (A : C(K, ℂ)) :
    Integrable (fun z : ℂ => w z * compactAmbient K A z) := by
  apply compactTestIntegral_integrable K w hw hc hWK A
  intro z
  simp [compactAmbient, z.property]

/-- The bounded ordinary test-integral map on a compact observation set. -/
def compactTestIntegral (K : Set ℂ) [CompactSpace K]
    (w : ℂ → ℂ) (hw : Continuous w) (hc : HasCompactSupport w)
    (hWK : tsupport w ⊆ K) : C(K, ℂ) →L[ℂ] ℂ := by
  classical
  let L : C(K, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun A => ∫ z : ℂ, w z * compactAmbient K A z
      map_add' := by
        intro A B
        have he : (fun z : ℂ => w z * compactAmbient K (A + B) z) =
            fun z => w z * compactAmbient K A z + w z * compactAmbient K B z := by
          funext z
          by_cases hz : z ∈ K <;> simp [compactAmbient, hz, mul_add]
        rw [he, integral_add (compactAmbient_integrable K w hw hc hWK A)
          (compactAmbient_integrable K w hw hc hWK B)]
      map_smul' := by
        intro c A
        have he : (fun z : ℂ => w z * compactAmbient K (c • A) z) =
            fun z => c • (w z * compactAmbient K A z) := by
          funext z
          by_cases hz : z ∈ K
          · simp only [compactAmbient, dite_eq_left hz, ContinuousMap.smul_apply, smul_eq_mul]
            ring
          · simp [compactAmbient, hz]
        rw [he, integral_smul]
        rfl }
  apply L.mkContinuous (∫ z : ℂ, ‖w z‖)
  intro A
  have hwint : Integrable (fun z : ℂ => ‖w z‖) :=
    (hw.integrable_of_hasCompactSupport hc).norm
  have hbound : ∀ z : ℂ, ‖compactAmbient K A z‖ ≤ ‖A‖ := by
    intro z
    by_cases hz : z ∈ K
    · simpa only [compactAmbient, dite_eq_left hz] using A.norm_coe_le_norm ⟨z, hz⟩
    · simp [compactAmbient, hz]
  change ‖∫ z : ℂ, w z * compactAmbient K A z‖ ≤ (∫ z : ℂ, ‖w z‖) * ‖A‖
  calc
    _ ≤ ∫ z : ℂ, ‖w z‖ * ‖A‖ :=
      norm_integral_le_of_norm_le (hwint.mul_const ‖A‖) (Filter.Eventually.of_forall fun z => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hbound z) (norm_nonneg _))
    _ = _ := integral_mul_const _ _

/-- The bounded map equals the literal global integral for every matching ambient function. -/
theorem compactTestIntegral_apply (K : Set ℂ) [CompactSpace K]
    (w : ℂ → ℂ) (hw : Continuous w) (hc : HasCompactSupport w)
    (hWK : tsupport w ⊆ K) (A : C(K, ℂ)) (f : ℂ → ℂ)
    (hmatch : ∀ z : K, A z = f z) :
    compactTestIntegral K w hw hc hWK A = ∫ z : ℂ, w z * f z := by
  change (∫ z : ℂ, w z * compactAmbient K A z) = _
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  by_cases hz : z ∈ K
  · simp only [compactAmbient, dite_eq_left hz, hmatch ⟨z, hz⟩]
  · have hzw : z ∉ tsupport w := fun h => hz (hWK h)
    simp [image_eq_zero_of_notMem_tsupport hzw]

end GapFamily.Analytic.PoincareThresholdWeak
