import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Local smooth tests in the gradient Hilbert space

Smooth compactly supported real tests separate complex `L²` vectors on a
full-measure open subset of the complex plane. Their complex linear span is
dense. These are `L²` statements; they do not identify an energy-form core
or impose any boundary condition on an automorphic gradient.
-/

noncomputable section

namespace GapFamily.Analytic

open MeasureTheory Set
open scoped ContDiff

variable {μ : Measure ℂ} [IsLocallyFiniteMeasure μ] {U : Set ℂ}

/-- Open-set distribution uniqueness applied to an actual `L²` function. -/
theorem localTest_ae_eq_zero {f : ℂ → ℂ} (hf : MemLp f 2 μ)
    (hU : IsOpen U) (hfull : ∀ᵐ z ∂μ, z ∈ U)
    (h : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∫ z, φ z • f z ∂μ = 0) : f =ᵐ[μ] 0 := by
  have hz := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    ((hf.locallyIntegrable (by norm_num)).locallyIntegrableOn U) h
  filter_upwards [hz, hfull] with z hz hmem using hz hmem

/-- The same separation statement as equality in the Hilbert space. -/
theorem localTest_L2_eq_zero (f : Lp ℂ 2 μ)
    (hU : IsOpen U) (hfull : ∀ᵐ z ∂μ, z ∈ U)
    (h : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∫ z, φ z • f z ∂μ = 0) : f = 0 := by
  apply Lp.ext
  exact (localTest_ae_eq_zero (Lp.memLp f) hU hfull h).trans
    (Lp.coeFn_zero (E := ℂ) (p := 2) (μ := μ)).symm

/-- A continuous nonvanishing local weight does not change test separation.
The weight need not be bounded globally or preserve `L²`. -/
theorem weightedLocalTest_L2_eq_zero (f : Lp ℂ 2 μ)
    (hU : IsOpen U) (hfull : ∀ᵐ z ∂μ, z ∈ U)
    {w : ℂ → ℝ} (hw : ContinuousOn w U) (hne : ∀ z ∈ U, w z ≠ 0)
    (h : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∫ z, φ z • (w z • f z) ∂μ = 0) : f = 0 := by
  have hf := ((Lp.memLp f).locallyIntegrable (by norm_num)).locallyIntegrableOn U
  have hlocal := hf.continuousOn_smul hU.isLocallyClosed hw
  have hz := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero hlocal h
  apply Lp.ext
  filter_upwards [hz, hfull, Lp.coeFn_zero (E := ℂ) (p := 2) (μ := μ)]
    with z hz hmem hzero
  rw [hzero]
  exact (smul_eq_zero.mp (hz hmem)).resolve_left (hne z hmem)

/-- The `L²` class of a real smooth compact test, regarded as complex-valued. -/
def localRealTestL2 (μ : Measure ℂ) [IsLocallyFiniteMeasure μ]
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) : Lp ℂ 2 μ :=
  ((Complex.continuous_ofReal.comp hφ.continuous).memLp_of_hasCompactSupport
    (hc.comp_left Complex.ofReal_zero)).toLp (fun z => (φ z : ℂ))

theorem localRealTestL2_ae (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) :
    localRealTestL2 μ φ hφ hc =ᵐ[μ] fun z => (φ z : ℂ) :=
  MemLp.coeFn_toLp _

/-- The Hilbert pairing of a real test is its ordinary distribution pairing. -/
theorem localRealTestL2_inner (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (f : Lp ℂ 2 μ) :
    inner ℂ (localRealTestL2 μ φ hφ hc) f = ∫ z, φ z • f z ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [localRealTestL2_ae φ hφ hc] with z hz
  simp [hz, RCLike.inner_apply, Complex.real_smul, mul_comm]

/-- The complex span of real smooth tests supported strictly inside the open set. -/
def localTestSpan (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] (U : Set ℂ) :
    Submodule ℂ (Lp ℂ 2 μ) :=
  Submodule.span ℂ {f | ∃ (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ), tsupport φ ⊆ U ∧ f = localRealTestL2 μ φ hφ hc}

theorem localRealTestL2_mem_span (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U) :
    localRealTestL2 μ φ hφ hc ∈ localTestSpan μ U :=
  Submodule.subset_span ⟨φ, hφ, hc, hs, rfl⟩

/-- Interior test density in the actual `L²` norm, without an energy-core claim. -/
theorem localTestSpan_dense (hU : IsOpen U) (hfull : ∀ᵐ z ∂μ, z ∈ U) :
    Dense (localTestSpan μ U : Set (Lp ℂ 2 μ)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro f hf
  apply localTest_L2_eq_zero f hU hfull
  intro φ hφ hc hs
  rw [← localRealTestL2_inner φ hφ hc f]
  exact (localTestSpan μ U).inner_right_of_mem_orthogonal
    (localRealTestL2_mem_span φ hφ hc hs) hf

end GapFamily.Analytic
