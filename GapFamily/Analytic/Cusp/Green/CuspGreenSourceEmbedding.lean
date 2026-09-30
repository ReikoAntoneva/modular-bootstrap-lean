import GapFamily.Analytic.Cusp.Green.CuspGreenSourceLift
import GapFamily.Analytic.Cusp.Green.CuspGreenSourceSpace
import Mathlib.Analysis.Normed.Operator.Extend

noncomputable section
namespace GapFamily.Analytic
open Set Filter MeasureTheory ModularGradient
open scoped Topology ContDiff

/-- The already constructed literal modular source on the smooth source subspace. -/
def cuspGreenSmoothSourceValue (T : ℝ) (f : cuspGreenSourceSpace T) : ModularHilbert :=
  cuspGreenSourceLift f f.property.1 f.property.2.1
    (f.property.2.2.trans Ioo_subset_Ioi_self)

theorem cuspGreenSmoothSourceValue_ae (T : ℝ) (f : cuspGreenSourceSpace T) :
    cuspGreenSmoothSourceValue T f =ᵐ[modularMeasure]
      (fun τ : UpperHalfPlane => cuspLift (f : ℝ → ℂ) τ.im) :=
  cuspGreenSourceLift_value_ae _ _ _ _

/-- Actual source lifting is complex linear on the smooth source subspace. -/
def cuspGreenSourceOnSmooth (T : ℝ) : cuspGreenSourceSpace T →ₗ[ℂ] ModularHilbert where
  toFun := cuspGreenSmoothSourceValue T
  map_add' f g := by
    apply Lp.ext
    filter_upwards [cuspGreenSmoothSourceValue_ae T (f + g),
      cuspGreenSmoothSourceValue_ae T f, cuspGreenSmoothSourceValue_ae T g,
      Lp.coeFn_add (cuspGreenSmoothSourceValue T f) (cuspGreenSmoothSourceValue T g)]
      with τ hfg hf hg hadd
    rw [hfg, hadd, Pi.add_apply, hf, hg]
    simp only [cuspLift, Submodule.coe_add, Pi.add_apply, smul_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [cuspGreenSmoothSourceValue_ae T (c • f),
      cuspGreenSmoothSourceValue_ae T f,
      Lp.coeFn_smul c (cuspGreenSmoothSourceValue T f)] with τ hcf hf hsmul
    simp only [RingHom.id_apply]
    rw [hcf, hsmul, Pi.smul_apply, hf]
    simp only [cuspLift, Submodule.coe_smul, Pi.smul_apply]
    exact smul_comm _ _ _

/-- The source norm equality is proved before taking the completion extension. -/
theorem cuspGreenSourceOnSmooth_norm (T : ℝ) (f : cuspGreenSourceSpace T) :
    ‖cuspGreenSourceOnSmooth T f‖ = ‖cuspGreenSourceRestriction T f‖ :=
  cuspGreenSourceLift_collar_norm T f f.property.1 f.property.2.1 f.property.2.2

/-- The genuine all-L² logarithmic source embedding, obtained from the proved
smooth-source isometry and its dense actual collar restriction. -/
def cuspGreenSourceEmbedding (T : ℝ) :
    Lp ℂ 2 (cuspGreenCollarMeasure 0 T) →ₗᵢ[ℂ] ModularHilbert :=
  (cuspGreenSourceOnSmooth T).extendOfIsometry
    (cuspGreenSourceRestriction_denseRange T) (cuspGreenSourceOnSmooth_norm T)

/-- The extended map agrees exactly with the actual modular source on every
smooth compact source supported strictly inside the collar. -/
theorem cuspGreenSourceEmbedding_smooth (T : ℝ) (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ Ioo (0 : ℝ) T) :
    cuspGreenSourceEmbedding T (cuspGreenCollarSource 0 T f hf.continuous) =
      cuspGreenSourceLift f hf hc (hs.trans Ioo_subset_Ioi_self) :=
  (cuspGreenSourceOnSmooth T).extendOfIsometry_eq (cuspGreenSourceRestriction_denseRange T)
    (cuspGreenSourceOnSmooth_norm T) (⟨f, hf, hc, hs⟩ : cuspGreenSourceSpace T)

/-- On those actual smooth sources the extension has the required literal representative. -/
theorem cuspGreenSourceEmbedding_smooth_ae (T : ℝ) (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ Ioo (0 : ℝ) T) :
    cuspGreenSourceEmbedding T (cuspGreenCollarSource 0 T f hf.continuous) =ᵐ[modularMeasure]
      (fun τ : UpperHalfPlane => if 1 < τ.im then
        Real.sqrt τ.im • f (Real.log τ.im) else 0) := by
  rw [cuspGreenSourceEmbedding_smooth T f hf hc hs]
  exact cuspGreenSourceLift_ae _ _ _ _

/-- Every actual collar L² source has exactly its original norm after lifting. -/
theorem cuspGreenSourceEmbedding_norm (T : ℝ)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure 0 T)) :
    ‖cuspGreenSourceEmbedding T f‖ = ‖f‖ :=
  (cuspGreenSourceEmbedding T).norm_map f

/-- The source extension is injective as a map on actual L² equivalence classes. -/
theorem cuspGreenSourceEmbedding_injective (T : ℝ) :
    Function.Injective (cuspGreenSourceEmbedding T) :=
  (cuspGreenSourceEmbedding T).injective

end GapFamily.Analytic
