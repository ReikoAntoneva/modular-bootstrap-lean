import GapFamily.Analytic.Poincare.Continuation.PoincareComplementSmooth
import GapFamily.Analytic.Poincare.Continuation.PoincareComplementGradient
import GapFamily.Analytic.Cusp.Fourier.CuspFourierCutoffForcing

noncomputable section
namespace GapFamily.Analytic.PoincareComplement
open Set MeasureTheory UpperHalfPlane
open scoped ContDiff

/-- The actual complement belongs to the smooth automorphic finite-energy core. -/
def smoothCore (J : ℤ) (s : ℂ) (hs : 2 < s.re) : ModularGradient.smoothCore := by
  refine ⟨(fun z : ℂ => series J s (UpperHalfPlane.ofComplex z)),
    contDiffOn_series J (by linarith), ?_, ?_,
    PoincareComplementGradient.directional_series_memLp J hs 1,
    PoincareComplementGradient.directional_series_memLp J hs Complex.I⟩
  · intro γ τ
    simpa only [UpperHalfPlane.ofComplex_apply] using series_smul J s τ γ
  · simpa only [UpperHalfPlane.ofComplex_apply] using series_memLp J hs

@[simp] theorem smoothCore_val (J : ℤ) (s : ℂ) (hs : 2 < s.re) :
    (smoothCore J s hs).val = (fun z : ℂ => series J s (UpperHalfPlane.ofComplex z)) := rfl

@[simp] theorem smoothCore_apply (J : ℤ) (s : ℂ) (hs : 2 < s.re) (τ : UpperHalfPlane) :
    (smoothCore J s hs).val τ = series J s τ := by
  simp only [smoothCore_val, UpperHalfPlane.ofComplex_apply]

/-- The core value class has the literal automorphic complement representative. -/
theorem smoothCore_value_ae (J : ℤ) (s : ℂ) (hs : 2 < s.re) :
    ModularGradient.value (smoothCore J s hs) =ᵐ[modularMeasure] series J s := by
  simpa only [smoothCore_apply] using ModularGradient.value_ae (smoothCore J s hs)

/-- The core's actual L² value is the previously constructed tail plus direct remnant. -/
theorem value_eq_hilbertSum (J : ℤ) (s : ℂ) (hs : 2 < s.re) :
    ModularGradient.value (smoothCore J s hs) =
      cuspWeightedTailAnalytic J 0 (by norm_num) s + cuspPoincareDirectRemnant J 0 s := by
  apply Lp.ext
  exact (smoothCore_value_ae J s hs).trans (hilbert_sum_ae_series J hs).symm

/-- The prescribed shifted, collar, and eigenvalue source is itself an actual smooth core.
This construction asserts neither a differential identity nor operator-domain membership. -/
def laplacianSourceCore (J : ℤ) (s : ℂ) (hs : 2 < s.re) : ModularGradient.smoothCore :=
  (2 * (Real.pi : ℂ) * (J : ℂ)) ^ 2 •
      smoothCore J (s + 2) (by norm_num [Complex.add_re]; linarith) +
    CuspFourierCutoff.forcingCore J (s - 1 / 2) +
    (s * (1 - s)) • smoothCore J s hs

/-- The source core is the literal prescribed ambient function. -/
theorem laplacianSourceCore_val (J : ℤ) (s : ℂ) (hs : 2 < s.re) :
    (laplacianSourceCore J s hs).val = fun z : ℂ =>
      (2 * (Real.pi : ℂ) * (J : ℂ)) ^ 2 *
          series J (s + 2) (UpperHalfPlane.ofComplex z) +
        (CuspFourierCutoff.forcingCore J (s - 1 / 2)).val z +
        s * (1 - s) * series J s (UpperHalfPlane.ofComplex z) := rfl

/-- The source value is expressed entirely by the actual Hilbert vectors. -/
theorem laplacianSourceCore_value (J : ℤ) (s : ℂ) (hs : 2 < s.re) :
    ModularGradient.value (laplacianSourceCore J s hs) =
      (2 * (Real.pi : ℂ) * (J : ℂ)) ^ 2 •
          (cuspWeightedTailAnalytic J 0 (by norm_num) (s + 2) +
            cuspPoincareDirectRemnant J 0 (s + 2)) +
        CuspFourierCutoff.forcing J (s - 1 / 2) +
        (s * (1 - s)) •
          (cuspWeightedTailAnalytic J 0 (by norm_num) s + cuspPoincareDirectRemnant J 0 s) := by
  simp only [laplacianSourceCore, map_add, map_smul, value_eq_hilbertSum,
    CuspFourierCutoff.forcing]

end GapFamily.Analytic.PoincareComplement
