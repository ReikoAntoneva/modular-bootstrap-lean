import GapFamily.Analytic.Modular.Elliptic.ModularUpperEvaluation
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Local coherence of actual upper-half-plane cutoff values

Hilbert cutoff lifts agree wherever their cutoffs agree. Continuity of
restriction in ordinary L² transfers the literal core identity through the
actual modular value density. The continuous graph representatives therefore
agree pointwise on overlapping open cutoff plateaus.
-/

noncomputable section
namespace GapFamily.Analytic.ModularGradient

open Set Filter MeasureTheory UpperHalfPlane Dirichlet
open scoped ContDiff Topology

variable (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
  (hsχ : tsupport χ ⊆ upperHalfPlaneSet)
  (η : ℂ → ℂ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
  (hsη : tsupport η ⊆ upperHalfPlaneSet)

/-- The actual Hilbert cutoff lifts agree almost everywhere on every measurable
set on which the two cutoffs agree, for every modular Hilbert source. -/
theorem upperCutoffHilbertValueOperator_congr_ae {S : Set ℂ} (hS : MeasurableSet S)
    (hχη : EqOn χ η S) (f : ModularHilbert) :
    upperCutoffHilbertValueOperator χ hχ hcχ hsχ f =ᵐ[volume.restrict S]
      upperCutoffHilbertValueOperator η hη hcη hsη f := by
  let R := LpToLpRestrictCLM ℂ ℂ ℂ (volume : Measure ℂ) 2 S
  have hd : DenseRange value := by
    simpa only [DenseRange, LinearMap.coe_range] using value_dense_range
  have heq : R (upperCutoffHilbertValueOperator χ hχ hcχ hsχ f) =
      R (upperCutoffHilbertValueOperator η hη hcη hsη f) := by
    refine hd.induction_on f ?_ ?_
    · exact isClosed_eq
        (R.continuous.comp (upperCutoffHilbertValueOperator χ hχ hcχ hsχ).continuous)
        (R.continuous.comp (upperCutoffHilbertValueOperator η hη hcη hsη).continuous)
    · intro F
      apply Lp.ext
      filter_upwards [
        LpToLpRestrictCLM_coeFn ℂ S (upperCutoffHilbertValueOperator χ hχ hcχ hsχ (value F)),
        LpToLpRestrictCLM_coeFn ℂ S (upperCutoffHilbertValueOperator η hη hcη hsη (value F)),
        ae_restrict_of_ae (upperCutoffHilbertValueOperator_value_ae χ hχ hcχ hsχ F),
        ae_restrict_of_ae (upperCutoffHilbertValueOperator_value_ae η hη hcη hsη F),
        ae_restrict_mem hS] with z hrχ hrη hFχ hFη hz
      exact hrχ.trans (hFχ.trans ((congrArg (fun c : ℂ => c * F.val z) (hχη hz)).trans
        (hFη.symm.trans hrη.symm)))
  have hrestr : R (upperCutoffHilbertValueOperator χ hχ hcχ hsχ f)
      =ᵐ[volume.restrict S] R (upperCutoffHilbertValueOperator η hη hcη hsη f) := by
    rw [heq]
  exact (LpToLpRestrictCLM_coeFn ℂ S
    (upperCutoffHilbertValueOperator χ hχ hcχ hsχ f)).symm.trans
      (hrestr.trans (LpToLpRestrictCLM_coeFn ℂ S
        (upperCutoffHilbertValueOperator η hη hcη hsη f)))

/-- The actual inverse-height-square source fields have the same locality. -/
theorem upperCutoffSourceField_congr_ae {S : Set ℂ} (hS : MeasurableSet S)
    (hχη : EqOn χ η S) (f : ModularHilbert) :
    upperCutoffSourceField χ hχ hcχ hsχ f =ᵐ[volume.restrict S]
      upperCutoffSourceField η hη hcη hsη f := by
  filter_upwards [upperCutoffHilbertValueOperator_congr_ae
    χ hχ hcχ hsχ η hη hcη hsη hS hχη f] with z hz
  exact congrArg (fun c : ℂ => c / (z.im : ℂ) ^ 2) hz

/-- The actual graph value is independent of a cutoff on every agreement set. -/
theorem laplacianUpperGraphValue_congr_ae {S : Set ℂ} (hS : MeasurableSet S)
    (hχη : EqOn χ η S) (u : LaplacianGraphDomain) :
    laplacianUpperGraphValue χ hχ hcχ hsχ u =ᵐ[volume.restrict S]
      laplacianUpperGraphValue η hη hcη hsη u :=
  upperCutoffHilbertValueOperator_congr_ae
    χ hχ hcχ hsχ η hη hcη hsη hS hχη (gradientEmbedding laplacian u)

/-- The chosen continuous representatives agree at every point of their open
plateau overlap, including modular seams and measure-zero compact subsets. -/
theorem laplacianUpperRepresentative_eqOn_overlap
    (U V : Set ℂ) (hU : IsOpen U) (hV : IsOpen V)
    (hχU : EqOn χ (fun _ => 1) U) (hηV : EqOn η (fun _ => 1) V)
    (u : LaplacianGraphDomain) :
    EqOn (laplacianUpperRepresentative χ hχ hcχ hsχ U hU hχU u)
      (laplacianUpperRepresentative η hη hcη hsη V hV hηV u) (U ∩ V) := by
  have hχη : EqOn χ η (U ∩ V) := by
    intro z hz
    exact (hχU hz.1).trans (hηV hz.2).symm
  have hχae : laplacianUpperRepresentative χ hχ hcχ hsχ U hU hχU u
      =ᵐ[volume.restrict (U ∩ V)] (fun z => laplacianUpperGraphValue χ hχ hcχ hsχ u z) :=
    ae_restrict_of_ae_restrict_of_subset (show U ∩ V ⊆ U from inter_subset_left)
      (laplacianUpperRepresentative_ae χ hχ hcχ hsχ U hU hχU u)
  have hηae : laplacianUpperRepresentative η hη hcη hsη V hV hηV u
      =ᵐ[volume.restrict (U ∩ V)] (fun z => laplacianUpperGraphValue η hη hcη hsη u z) :=
    ae_restrict_of_ae_restrict_of_subset (show U ∩ V ⊆ V from inter_subset_right)
      (laplacianUpperRepresentative_ae η hη hcη hsη V hV hηV u)
  have hfield := laplacianUpperGraphValue_congr_ae χ hχ hcχ hsχ η hη hcη hsη
    (hU.inter hV).measurableSet hχη u
  exact Measure.eqOn_open_of_ae_eq (μ := volume) (hχae.trans (hfield.trans hηae.symm))
    (hU.inter hV)
    ((laplacianUpperRepresentative_continuousOn χ hχ hcχ hsχ U hU hχU u).mono
      inter_subset_left)
    ((laplacianUpperRepresentative_continuousOn η hη hcη hsη V hV hηV u).mono
      inter_subset_right)

end GapFamily.Analytic.ModularGradient
