import GapFamily.Analytic.Modular.Elliptic.ModularEllipticChart
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Topology.Algebra.Support

/-!
# Returning an ordinary weak derivative through the centered elliptic chart

This transports an actual weak identity and ordinary L² membership from real
coordinate pairs back to the complex plane. No regularity is assumed or gained.
-/

noncomputable section
namespace GapFamily.Analytic
open Set MeasureTheory
open scoped ContDiff ENNReal

/-- A chart basis direction is the ordinary horizontal or vertical direction. -/
theorem fderiv_comp_ellipticChart_basis (z : ℂ) (φ : ℂ → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (v : Fin 2 → ℝ) (j : Fin 2) :
    fderiv ℝ (fun v => φ (ellipticChart z v)) v (Pi.single j (1 : ℝ)) =
      fderiv ℝ φ (ellipticChart z v) (![1, Complex.I] j) := by
  change fderiv ℝ (φ ∘ ellipticChart z) v (Pi.single j (1 : ℝ)) = _
  rw [fderiv_comp v (hφ.differentiable (by norm_num) _)
    ((ellipticChart_contDiff z).differentiable (by norm_num) _)]
  simp only [ContinuousLinearMap.comp_apply, ellipticChart_fderiv_basis]

/-- The ordinary L² field is returned to exactly the chart-image measure. -/
theorem memLp_ellipticChart_symm_image {E : Type*} [NormedAddCommGroup E]
    (z : ℂ) (V : Set (Fin 2 → ℝ)) (F : (Fin 2 → ℝ) → E) (p : ℝ≥0∞)
    (hF : MemLp F p (volume.restrict V)) :
    MemLp (fun w => F ((ellipticChart z).symm w)) p
      (volume.restrict (ellipticChart z '' V)) := by
  rw [← memLp_comp_ellipticChart_image_iff]
  simpa only [Homeomorph.symm_apply_apply] using hF

/-- A complex weak partial derivative on the coordinate domain is the weak
horizontal/vertical derivative of the actual returned fields on its image. -/
theorem weakPartial_ellipticChart_image (z : ℂ) (V : Set (Fin 2 → ℝ))
    (j : Fin 2) (F G : (Fin 2 → ℝ) → ℂ)
    (hweak : ∀ ψ : (Fin 2 → ℝ) → ℝ,
      ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ V →
      (∫ v in V, F v * (fderiv ℝ ψ v (Pi.single j (1 : ℝ)) : ℂ)) =
        -(∫ v in V, G v * (ψ v : ℂ)))
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ ellipticChart z '' V) :
    (∫ w in ellipticChart z '' V,
      F ((ellipticChart z).symm w) * (fderiv ℝ φ w (![1, Complex.I] j) : ℂ)) =
      -(∫ w in ellipticChart z '' V,
        G ((ellipticChart z).symm w) * (φ w : ℂ)) := by
  have hsupport : tsupport (fun v => φ (ellipticChart z v)) ⊆ V := by
    change tsupport (φ ∘ ellipticChart z) ⊆ V
    rw [tsupport_comp_eq_preimage φ (ellipticChart z)]
    intro v hv
    obtain ⟨w, hw, heq⟩ := hs hv
    exact (ellipticChart z).injective heq ▸ hw
  have h := hweak (fun v => φ (ellipticChart z v))
    (hφ.comp (ellipticChart_contDiff z)) (hc.comp_homeomorph (ellipticChart z)) hsupport
  simp only [fderiv_comp_ellipticChart_basis z φ hφ] at h
  simpa only [integral_ellipticChart_image, Homeomorph.symm_apply_apply] using h

end GapFamily.Analytic
