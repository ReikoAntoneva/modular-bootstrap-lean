import GapFamily.Analytic.Modular.Periodization.ModularPeriodizationDensity
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-! A genuine dense family of bounded continuous modular functions.
Boundedness is proved for compact interior periodizations, not for arbitrary
elements of the finite-energy smooth modular core. -/

noncomputable section
namespace GapFamily.Analytic.ModularInvariantBCFDensity

open Set Filter MeasureTheory UpperHalfPlane ModularGradient
open scoped ContDiff MatrixGroups BoundedContinuousFunction

/-- Literal full modular invariance of bounded continuous upper-plane functions. -/
def invariantBCF : Submodule ℂ (UpperHalfPlane →ᵇ ℂ) where
  carrier := {f | ∀ (γ : SL(2, ℤ)) (τ : UpperHalfPlane), f (γ • τ) = f τ}
  zero_mem' := by intro γ τ; rfl
  add_mem' := by
    intro f g hf hg γ τ
    change f (γ • τ) + g (γ • τ) = f τ + g τ
    rw [hf γ τ, hg γ τ]
  smul_mem' := by
    intro c f hf γ τ
    change c • f (γ • τ) = c • f τ
    rw [hf γ τ]

/-- The standard finite-measure BCF-to-L² map, restricted to actual invariants. -/
def invariantBCFToLp : invariantBCF →L[ℂ] ModularHilbert :=
  (BoundedContinuousFunction.toLp 2 modularMeasure ℂ).comp invariantBCF.subtypeL

theorem invariantBCFToLp_ae (f : invariantBCF) :
    invariantBCFToLp f =ᵐ[modularMeasure] (fun τ : UpperHalfPlane => f.val τ) :=
  BoundedContinuousFunction.coeFn_toLp 2 modularMeasure ℂ f.val

/-- Compact interior periodization is globally bounded: move each point to
the closed fundamental domain and use the exact compact-test value there. -/
theorem exists_periodization_bound (φ : ℂ → ℂ) (hφ : Continuous φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ modularInterior) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : UpperHalfPlane, ‖modularPeriodization φ τ‖ ≤ C := by
  obtain ⟨B, hB⟩ := hc.exists_bound_of_continuousOn hφ.continuousOn
  have hbound (z : ℂ) : ‖φ z‖ ≤ max B 0 := by
    by_cases hz : z ∈ tsupport φ
    · exact (hB z hz).trans (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport hz, norm_zero]
      exact le_max_right _ _
  refine ⟨max B 0, le_max_right _ _, fun τ => ?_⟩
  obtain ⟨γ, hγ⟩ := ModularGroup.exists_smul_mem_fd τ
  calc
    ‖modularPeriodization φ τ‖ = ‖modularPeriodization φ (γ • τ : UpperHalfPlane)‖ :=
      congrArg norm (modularPeriodization_invariant φ γ τ).symm
    _ = ‖φ (γ • τ : UpperHalfPlane)‖ := congrArg norm (modularPeriodization_eq_on_fd hs hγ)
    _ ≤ max B 0 := hbound _

/-- The literal normalized periodization as a genuine bounded continuous function. -/
def periodizedBCF (φ : ℂ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ modularInterior) : UpperHalfPlane →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun τ : UpperHalfPlane => modularPeriodization φ τ)
    ((contDiffOn_modularPeriodization hφ hc hs).continuousOn.comp_continuous
      UpperHalfPlane.continuous_coe (fun τ => τ.im_pos))
    (exists_periodization_bound φ hφ.continuous hc hs).choose
    (exists_periodization_bound φ hφ.continuous hc hs).choose_spec.2

@[simp] theorem periodizedBCF_apply (φ : ℂ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ modularInterior) (τ : UpperHalfPlane) :
    periodizedBCF φ hφ hc hs τ = modularPeriodization φ τ := rfl

theorem periodizedBCF_invariant (φ : ℂ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ modularInterior) :
    periodizedBCF φ hφ hc hs ∈ invariantBCF :=
  modularPeriodization_invariant φ

def periodizedInvariantBCF (φ : ℂ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ modularInterior) : invariantBCF :=
  ⟨periodizedBCF φ hφ hc hs, periodizedBCF_invariant φ hφ hc hs⟩

/-- Standard BCF embedding is exactly the value class of this actual periodized core. -/
theorem periodizedBCF_toLp_eq_value (φ : ℂ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ modularInterior) :
    BoundedContinuousFunction.toLp 2 modularMeasure ℂ (periodizedBCF φ hφ hc hs) =
      value (periodizedCore φ hφ hc hs) := by
  apply Lp.ext
  filter_upwards [BoundedContinuousFunction.coeFn_toLp 2 modularMeasure ℂ
    (periodizedBCF φ hφ hc hs), value_ae (periodizedCore φ hφ hc hs)] with τ hbc hv
  exact hbc.trans hv.symm

/-- Every real compact interior test lies in the actual invariant-BCF range. -/
theorem coordinate_test_mem_invariantBCFToLp_range (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ modularInterior) :
    modularCoordinateEquiv (localRealTestL2 modularCoordinateMeasure φ hφ hc) ∈
      invariantBCFToLp.range := by
  have hφC : ContDiff ℝ ∞ (fun z => (φ z : ℂ)) := Complex.ofRealCLM.contDiff.comp hφ
  have hcC : HasCompactSupport (fun z => (φ z : ℂ)) := hc.comp_left Complex.ofReal_zero
  have hsC : tsupport (fun z => (φ z : ℂ)) ⊆ modularInterior :=
    (tsupport_comp_subset Complex.ofReal_zero φ).trans hs
  refine ⟨periodizedInvariantBCF (fun z => (φ z : ℂ)) hφC hcC hsC, ?_⟩
  change BoundedContinuousFunction.toLp 2 modularMeasure ℂ
    (periodizedBCF (fun z => (φ z : ℂ)) hφC hcC hsC) = _
  rw [periodizedBCF_toLp_eq_value]
  apply Lp.ext
  have htest := (ae_modularCoordinate_iff (fun z =>
    localRealTestL2 modularCoordinateMeasure φ hφ hc z = (φ z : ℂ))).mp
      (localRealTestL2_ae (μ := modularCoordinateMeasure) φ hφ hc)
  filter_upwards [value_periodizedCore_ae (fun z => (φ z : ℂ)) hφC hcC hsC,
    modularCoordinateEquiv_apply_ae (localRealTestL2 modularCoordinateMeasure φ hφ hc),
    htest] with τ hvalue hmap ht
  exact hvalue.trans (hmap.trans ht).symm

/-- The standard L² images of actual bounded continuous modular functions are dense. -/
theorem invariantBCFToLp_denseRange : DenseRange invariantBCFToLp := by
  let W : Submodule ℂ ModularCoordinateHilbert :=
    invariantBCFToLp.range.comap modularCoordinateEquiv.toLinearEquiv.toLinearMap
  have hspan : localTestSpan modularCoordinateMeasure modularInterior ≤ W := by
    apply Submodule.span_le.mpr
    rintro f ⟨φ, hφ, hc, hs, rfl⟩
    exact coordinate_test_mem_invariantBCFToLp_range φ hφ hc hs
  have hdense := modularCoordinateEquiv.surjective.denseRange.dense_image
    modularCoordinateEquiv.continuous
    (localTestSpan_dense (μ := modularCoordinateMeasure) isOpen_modularInterior
      ae_mem_modularInterior)
  have hrange : Dense (invariantBCFToLp.range : Set ModularHilbert) := by
    apply hdense.mono
    rintro f ⟨g, hg, rfl⟩
    exact hspan hg
  simpa only [DenseRange, LinearMap.coe_range, ContinuousLinearMap.coe_coe] using hrange

end GapFamily.Analytic.ModularInvariantBCFDensity
