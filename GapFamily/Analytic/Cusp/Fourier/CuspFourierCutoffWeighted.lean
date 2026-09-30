import GapFamily.Analytic.Cusp.Fourier.CuspFourierCutoffForcing

/-! Height weights on the genuine compact Fourier cutoff forcing. -/
noncomputable section
namespace GapFamily.Analytic.CuspFourierCutoff
open Set MeasureTheory
open scoped BoundedContinuousFunction

/-- The actual compact forcing with a real height weight. The bounded logarithm
is used only on the already proved support of the forcing profile. -/
def weightedForcing (J : ℤ) (α : ℝ) (κ : ℂ) : ModularHilbert :=
  BoundedContinuousFunction.toLp 2 modularMeasure ℂ
    (NormedSpace.exp ((α : ℂ) • boundedLogHeight) *
      boundedForcing (boundedConstantProfile J) (boundedLinearProfile J) boundedLogHeight κ)

theorem weightedForcing_analyticAt (J : ℤ) (α : ℝ) (κ : ℂ) :
    AnalyticAt ℂ (weightedForcing J α) κ := by
  exact (ContinuousLinearMap.analyticAt (𝕜 := ℂ)
    (E := UpperHalfPlane →ᵇ ℂ) (F := ModularHilbert)
    (BoundedContinuousFunction.toLp 2 modularMeasure ℂ) _).comp
      (analyticAt_const.mul (boundedForcing_analyticAt _ _ _ κ))

theorem weightedForcing_ae (J : ℤ) (α : ℝ) (κ : ℂ) :
    weightedForcing J α κ =ᵐ[modularMeasure]
      (fun τ : UpperHalfPlane => ((τ.im ^ α : ℝ) : ℂ) *
        (profile κ τ.im * cuspFourierMode J τ.re)) := by
  apply (BoundedContinuousFunction.coeFn_toLp 2 modularMeasure ℂ _).trans
  apply Filter.Eventually.of_forall
  intro τ
  simp only [BoundedContinuousFunction.mul_apply, boundedExp_apply,
    boundedForcing_profile]
  by_cases hτ : τ.im ∈ Icc (2 : ℝ) 3
  · rw [boundedLogHeight_apply_of_mem τ hτ]
    congr 1
    rw [← Complex.ofReal_mul, ← Complex.ofReal_exp,
      Real.rpow_def_of_pos τ.im_pos]
    congr 2
    ring
  · have hz : profile κ τ.im = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hτ (tsupport_profile κ h))
    simp [hz]

/-- With zero weight the new literal construction is the existing genuine forcing. -/
theorem weightedForcing_zero (J : ℤ) (κ : ℂ) :
    weightedForcing J 0 κ = forcing J κ := by
  apply Lp.ext
  filter_upwards [weightedForcing_ae J 0 κ, forcing_ae J κ] with τ hw hf
  simp [hw, hf]

end GapFamily.Analytic.CuspFourierCutoff
