import GapFamily.Analytic.Spatial.SpatialOrbitContraction
import GapFamily.Analytic.Elliptic.LpUniformBoundedConvergence
import GapFamily.Analytic.Modular.ModularInvariantBCFDensity
import GapFamily.Analytic.Foundation.StrongOperatorDensity

/-! Strong L² approximation to the identity for the actual normalized orbit operators. -/
noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open Set Filter MeasureTheory UpperHalfPlane
open LpUniformBoundedConvergence ModularInvariantBCFDensity StrongOperatorDensity
open scoped Topology BoundedContinuousFunction MatrixGroups

/-- Every invariant bounded continuous modular function has genuine strong-L²
approximation along every sequence of admissible real exponents tending to infinity. -/
theorem normalizedOrbitOperator_tendsto_bounded
    (s : ℕ → ℝ) (hs : ∀ n, 1 < s n) (hslim : Tendsto s atTop atTop)
    (f : UpperHalfPlane →ᵇ ℂ)
    (hmod : ∀ γ : SL(2, ℤ), ∀ w : UpperHalfPlane, f (γ • w) = f w) :
    Tendsto (fun n => normalizedOrbitOperator (s n) (hs n) (modularBoundedEmbedding f))
      atTop (𝓝 (modularBoundedEmbedding f)) := by
  apply tendsto_L2_of_ae_of_uniform_bound _ _ ‖f‖ (norm_nonneg f)
  · intro n
    filter_upwards [normalizedOrbitOperator_bounded_ae (s n) (hs n) f hmod] with z hz
    rw [hz]
    exact norm_pointAverage_le (s n) (hs n) z f
  · filter_upwards [modularBoundedEmbedding_ae f] with z hz
    rw [hz]
    exact f.norm_coe_le_norm z
  · filter_upwards [ae_all_iff.mpr (fun n => normalizedOrbitOperator_bounded_ae (s n) (hs n) f hmod),
      modularBoundedEmbedding_ae f] with z hz hf
    simpa only [hz, hf, Function.comp_def] using (pointAverage_tendsto z f).comp hslim

/-- Actual normalized orbit operators converge strongly to the identity on all
of ModularHilbert. Density and the uniform contraction estimate discharge the extension. -/
theorem normalizedOrbitOperator_tendsto
    (s : ℕ → ℝ) (hs : ∀ n, 1 < s n) (hslim : Tendsto s atTop atTop) (F : ModularHilbert) :
    Tendsto (fun n => normalizedOrbitOperator (s n) (hs n) F) atTop (𝓝 F) := by
  apply tendsto_apply_of_dense_of_opNorm_le_one
    (fun n => normalizedOrbitOperator (s n) (hs n)) atTop (Set.range invariantBCFToLp)
    (fun n => norm_normalizedOrbitOperator_le_one (s n) (hs n))
    invariantBCFToLp_denseRange _ F
  rintro u ⟨f, rfl⟩
  change Tendsto (fun n => normalizedOrbitOperator (s n) (hs n)
      (modularBoundedEmbedding (f : UpperHalfPlane →ᵇ ℂ))) atTop
    (𝓝 (modularBoundedEmbedding (f : UpperHalfPlane →ᵇ ℂ)))
  exact normalizedOrbitOperator_tendsto_bounded s hs hslim f f.property

/-- In particular the literal sequence s=n+2 is a strong approximate identity. -/
theorem normalizedOrbitOperator_nat_add_two_tendsto (F : ModularHilbert) :
    Tendsto (fun n : ℕ => normalizedOrbitOperator ((n : ℝ) + 2)
      (by have h := Nat.cast_nonneg (α := ℝ) n; linarith [h]) F) atTop (𝓝 F) := by
  apply normalizedOrbitOperator_tendsto
  exact tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop

end GapFamily.Analytic.SpatialPoint
