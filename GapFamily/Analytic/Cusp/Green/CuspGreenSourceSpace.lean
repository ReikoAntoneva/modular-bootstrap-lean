import GapFamily.Analytic.Cusp.Green.CuspGreenSmoothSourceDensity
import Mathlib.Topology.Algebra.Support

noncomputable section
namespace GapFamily.Analytic
open MeasureTheory Set
open scoped ContDiff

/-- Literal complex smooth source profiles supported compactly inside the collar. -/
def cuspGreenSourceSpace (T : ℝ) : Submodule ℂ (ℝ → ℂ) where
  carrier := {f | ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ Ioo 0 T}
  zero_mem' := by
    refine ⟨contDiff_const, ?_, ?_⟩
    · simp [HasCompactSupport]
    · simp
  add_mem' := by
    intro f g hf hg
    exact ⟨hf.1.add hg.1, hf.2.1.add hg.2.1,
      (tsupport_add f g).trans (union_subset hf.2.2 hg.2.2)⟩
  smul_mem' := by
    intro c f hf
    refine ⟨hf.1.const_smul c, ?_, ?_⟩
    · exact hf.2.1.smul_left (f := fun _ : ℝ => c)
    · exact (tsupport_smul_subset_right (fun _ : ℝ => c) f).trans hf.2.2

private theorem collarSource_add (T : ℝ) (f g : ℝ → ℂ)
    (hf : Continuous f) (hg : Continuous g) :
    cuspGreenCollarSource 0 T (f + g) (hf.add hg) =
      cuspGreenCollarSource 0 T f hf + cuspGreenCollarSource 0 T g hg := by
  apply Lp.ext
  filter_upwards [cuspGreenCollarSource_coeFn 0 T (f + g) (hf.add hg),
    cuspGreenCollarSource_coeFn 0 T f hf, cuspGreenCollarSource_coeFn 0 T g hg,
    Lp.coeFn_add (cuspGreenCollarSource 0 T f hf) (cuspGreenCollarSource 0 T g hg)]
      with t hfg hf' hg' hadd
  simp only [Pi.add_apply] at hfg hadd
  rw [hfg, hadd, hf', hg']

private theorem collarSource_smul (T : ℝ) (f : ℝ → ℂ)
    (hf : Continuous f) (c : ℂ) :
    cuspGreenCollarSource 0 T (c • f) (hf.const_smul c) =
      c • cuspGreenCollarSource 0 T f hf := by
  apply Lp.ext
  filter_upwards [cuspGreenCollarSource_coeFn 0 T (c • f) (hf.const_smul c),
    cuspGreenCollarSource_coeFn 0 T f hf,
    Lp.coeFn_smul c (cuspGreenCollarSource 0 T f hf)] with t hcf hf' hsmul
  simp only [Pi.smul_apply] at hcf hsmul
  rw [hcf, hsmul, hf']


/-- Actual restriction to the unnormalized collar L² source space. -/
def cuspGreenSourceRestriction (T : ℝ) :
    cuspGreenSourceSpace T →ₗ[ℂ] Lp ℂ 2 (cuspGreenCollarMeasure 0 T) where
  toFun f := cuspGreenCollarSource 0 T f f.property.1.continuous
  map_add' f g := by
    exact collarSource_add T f g f.property.1.continuous g.property.1.continuous
  map_smul' c f := by
    exact collarSource_smul T f f.property.1.continuous c

/-- The restriction uses the literal source values almost everywhere. -/
theorem cuspGreenSourceRestriction_coeFn (T : ℝ) (f : cuspGreenSourceSpace T) :
    cuspGreenSourceRestriction T f =ᵐ[cuspGreenCollarMeasure 0 T]
      (fun t : CuspGreenCollar 0 T => (f : ℝ → ℂ) t) :=
  cuspGreenCollarSource_coeFn 0 T f f.property.1.continuous

/-- The proved dense real test family is contained in the actual complex source range. -/
theorem cuspGreenSmoothRealSource_mem_restriction_range (T : ℝ) (φ : ℝ → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ioo 0 T) :
    cuspGreenSmoothRealSource T φ hφ ∈ (cuspGreenSourceRestriction T).range := by
  have hφC : ContDiff ℝ ∞ (fun t => (φ t : ℂ)) := Complex.ofRealCLM.contDiff.comp hφ
  have hcC : HasCompactSupport (fun t => (φ t : ℂ)) := hc.comp_left Complex.ofReal_zero
  have hsC : tsupport (fun t => (φ t : ℂ)) ⊆ Ioo 0 T :=
    (tsupport_comp_subset Complex.ofReal_zero φ).trans hs
  refine ⟨⟨(fun t => (φ t : ℂ)), hφC, hcC, hsC⟩, ?_⟩
  rfl

/-- Actual smooth compact restriction has dense range in the collar Hilbert space. -/
theorem cuspGreenSourceRestriction_denseRange (T : ℝ) :
    DenseRange (cuspGreenSourceRestriction T) := by
  have hspan : cuspGreenSmoothSourceSpan T ≤ (cuspGreenSourceRestriction T).range := by
    apply Submodule.span_le.mpr
    rintro _ ⟨φ, hφ, hc, hs, rfl⟩
    exact cuspGreenSmoothRealSource_mem_restriction_range T φ hφ hc hs
  exact (cuspGreenSmoothSourceSpan_dense T).mono hspan

end GapFamily.Analytic
