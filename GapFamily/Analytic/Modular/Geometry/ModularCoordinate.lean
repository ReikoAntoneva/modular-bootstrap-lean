import GapFamily.Analytic.Modular.ModularBoundary
import GapFamily.Analytic.Elliptic.GradientLocalHyperbolic
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Complex coordinates for the actual modular measure

The boundary-null fundamental-domain measure is transported to the open
complex region, with the literal inverse-square hyperbolic density. Integral,
integrability and `Lp` statements therefore use the same measure in both
representations.
-/

noncomputable section

namespace GapFamily.Analytic

open Set MeasureTheory
open scoped ENNReal NNReal

/-- The open modular fundamental region in complex coordinates. -/
def modularInterior : Set ℂ := UpperHalfPlane.coe '' ModularGroup.fdo

theorem isOpen_modularInterior : IsOpen modularInterior :=
  UpperHalfPlane.isOpenEmbedding_coe.isOpenMap _ ModularGroup.isOpen_fdo

theorem measurableSet_modularInterior : MeasurableSet modularInterior :=
  isOpen_modularInterior.measurableSet

theorem im_pos_of_mem_modularInterior {z : ℂ} (hz : z ∈ modularInterior) : 0 < z.im := by
  obtain ⟨τ, _, rfl⟩ := hz
  exact τ.im_pos

/-- The literal complex-coordinate measure used in local integration by parts. -/
def modularCoordinateMeasure : Measure ℂ := Dirichlet.localHyperbolicMeasure modularInterior

theorem hyperbolicDensity_eq (z : ℂ) :
    (↑((1 / ‖z.im‖₊) ^ 2 : NNReal) : ENNReal) =
      ENNReal.ofReal (1 / z.im ^ 2) := by
  rw [← ENNReal.ofReal_coe_nnreal]
  congr 1
  simp [NNReal.coe_pow, Real.norm_eq_abs, sq_abs]

/-- The actual modular measure is exactly the inverse-square coordinate measure. -/
theorem map_coe_modularMeasure :
    Measure.map UpperHalfPlane.coe modularMeasure = modularCoordinateMeasure := by
  ext s hs
  rw [Measure.map_apply UpperHalfPlane.measurable_coe hs,
    modularMeasure_eq_restrict_fdo, Measure.restrict_apply
      (UpperHalfPlane.measurable_coe hs), UpperHalfPlane.volume_eq_lintegral]
  have himage : UpperHalfPlane.coe '' (UpperHalfPlane.coe ⁻¹' s ∩ ModularGroup.fdo) =
      s ∩ modularInterior := by
    ext z
    constructor
    · rintro ⟨τ, ⟨hτs, hτf⟩, rfl⟩
      exact ⟨hτs, τ, hτf, rfl⟩
    · rintro ⟨hzs, τ, hτf, rfl⟩
      exact ⟨τ, ⟨hzs, hτf⟩, rfl⟩
  rw [himage, modularCoordinateMeasure, Dirichlet.localHyperbolicMeasure,
    withDensity_apply _ hs, Measure.restrict_restrict hs]
  exact lintegral_congr (hyperbolicDensity_eq)

theorem measurePreserving_modularCoordinate :
    MeasurePreserving UpperHalfPlane.coe modularMeasure modularCoordinateMeasure :=
  ⟨UpperHalfPlane.measurable_coe, map_coe_modularMeasure⟩

instance : IsFiniteMeasure modularCoordinateMeasure := by
  rw [← map_coe_modularMeasure]
  infer_instance

/-- Arbitrary almost-everywhere assertions transport through the measurable embedding. -/
theorem ae_modularCoordinate_iff (p : ℂ → Prop) :
    (∀ᵐ z ∂modularCoordinateMeasure, p z) ↔
      ∀ᵐ τ ∂modularMeasure, p (UpperHalfPlane.coe τ) := by
  rw [← map_coe_modularMeasure]
  exact UpperHalfPlane.measurableEmbedding_coe.ae_map_iff

theorem ae_mem_modularInterior : ∀ᵐ z ∂modularCoordinateMeasure, z ∈ modularInterior := by
  rw [ae_modularCoordinate_iff]
  filter_upwards [ae_mem_fdo] with τ hτ
  exact ⟨τ, hτ, rfl⟩

/-- Equality of the actual extended `Lp` norms, without a measurability premise. -/
theorem eLpNorm_modularCoordinate {E : Type*} [NormedAddCommGroup E]
    (f : ℂ → E) (p : ℝ≥0∞) :
    eLpNorm f p modularCoordinateMeasure =
      eLpNorm (fun τ : UpperHalfPlane => f τ) p modularMeasure := by
  rw [← map_coe_modularMeasure]
  exact UpperHalfPlane.measurableEmbedding_coe.eLpNorm_map_measure

theorem memLp_modularCoordinate_iff {E : Type*} [NormedAddCommGroup E]
    (f : ℂ → E) (p : ℝ≥0∞) :
    MemLp f p modularCoordinateMeasure ↔
      MemLp (fun τ : UpperHalfPlane => f τ) p modularMeasure := by
  rw [← map_coe_modularMeasure]
  exact UpperHalfPlane.measurableEmbedding_coe.memLp_map_measure_iff

/-- Ordinary integrability is equivalent in the two actual coordinate measures. -/
theorem integrable_modularCoordinate_iff {E : Type*} [NormedAddCommGroup E]
    (f : ℂ → E) :
    Integrable f modularCoordinateMeasure ↔
      Integrable (fun τ : UpperHalfPlane => f τ) modularMeasure := by
  rw [← map_coe_modularMeasure]
  exact UpperHalfPlane.measurableEmbedding_coe.integrable_map_iff

theorem integral_modularCoordinate {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℂ → E) :
    (∫ z, f z ∂modularCoordinateMeasure) =
      ∫ τ : UpperHalfPlane, f τ ∂modularMeasure := by
  rw [← map_coe_modularMeasure]
  exact UpperHalfPlane.measurableEmbedding_coe.integral_map f

/-- The same actual Hilbert space in complex coordinates. -/
abbrev ModularCoordinateHilbert := Lp ℂ 2 modularCoordinateMeasure

/-- Coordinate restriction is a complex linear isometry of the actual `L²` spaces. -/
def modularCoordinatePullback : ModularCoordinateHilbert →ₗᵢ[ℂ] ModularHilbert :=
  Lp.compMeasurePreservingₗᵢ ℂ UpperHalfPlane.coe measurePreserving_modularCoordinate

theorem modularCoordinatePullback_ae (f : ModularCoordinateHilbert) :
    modularCoordinatePullback f =ᵐ[modularMeasure] fun τ : UpperHalfPlane => f τ :=
  Lp.coeFn_compMeasurePreserving f measurePreserving_modularCoordinate

/-- Every modular vector has a genuine coordinate representative; values outside
the upper half-plane are irrelevant to the transported measure. -/
theorem modularCoordinatePullback_surjective : Function.Surjective modularCoordinatePullback := by
  intro f
  let F : ℂ → ℂ := fun z => f (UpperHalfPlane.ofComplex z)
  have hF : MemLp F 2 modularCoordinateMeasure := by
    rw [memLp_modularCoordinate_iff]
    simpa only [F, UpperHalfPlane.ofComplex_apply] using Lp.memLp f
  refine ⟨hF.toLp F, ?_⟩
  apply Lp.ext
  have hrep := (ae_modularCoordinate_iff (fun z => hF.toLp F z = F z)).mp hF.coeFn_toLp
  filter_upwards [modularCoordinatePullback_ae (hF.toLp F), hrep] with τ hτ hFτ
  simpa only [F, UpperHalfPlane.ofComplex_apply] using hτ.trans hFτ

/-- An actual unitary coordinate equivalence, constructed from restriction and extension. -/
def modularCoordinateEquiv : ModularCoordinateHilbert ≃ₗᵢ[ℂ] ModularHilbert :=
  LinearIsometryEquiv.ofSurjective modularCoordinatePullback modularCoordinatePullback_surjective

theorem modularCoordinateEquiv_apply_ae (f : ModularCoordinateHilbert) :
    modularCoordinateEquiv f =ᵐ[modularMeasure] fun τ : UpperHalfPlane => f τ :=
  modularCoordinatePullback_ae f

theorem modularCoordinateEquiv_symm_ae (f : ModularHilbert) :
    modularCoordinateEquiv.symm f =ᵐ[modularCoordinateMeasure]
      fun z => f (UpperHalfPlane.ofComplex z) := by
  change ∀ᵐ z ∂modularCoordinateMeasure,
    modularCoordinateEquiv.symm f z = f (UpperHalfPlane.ofComplex z)
  rw [ae_modularCoordinate_iff]
  have h := modularCoordinateEquiv_apply_ae (modularCoordinateEquiv.symm f)
  filter_upwards [h] with τ hτ
  simpa only [LinearIsometryEquiv.apply_symm_apply, UpperHalfPlane.ofComplex_apply] using hτ.symm

/-- On the actual open region the hyperbolic density and Lebesgue measure
have precisely the same null sets. -/
theorem ae_modularCoordinate_iff_restrict (p : ℂ → Prop) :
    (∀ᵐ z ∂modularCoordinateMeasure, p z) ↔ ∀ᵐ z ∂volume.restrict modularInterior, p z := by
  rw [modularCoordinateMeasure, Dirichlet.localHyperbolicMeasure,
    ae_withDensity_iff (by fun_prop : Measurable (fun z : ℂ => ENNReal.ofReal (1 / z.im ^ 2)))]
  constructor
  · intro h
    filter_upwards [h, ae_restrict_mem measurableSet_modularInterior] with z hz hmem
    exact hz (ne_of_gt (ENNReal.ofReal_pos.mpr (one_div_pos.mpr
      (sq_pos_of_pos (im_pos_of_mem_modularInterior hmem)))))
  · intro h
    filter_upwards [h] with z hz using fun _ => hz

/-- Equal `L²` representatives which are continuous in the interior agree
pointwise there, so local differential expressions are independent of the representative. -/
theorem eqOn_modularInterior_of_ae_eq {E : Type*} [TopologicalSpace E] [T2Space E]
    {f g : ℂ → E} (hf : ContinuousOn f modularInterior) (hg : ContinuousOn g modularInterior)
    (hfg : (fun τ : UpperHalfPlane => f τ) =ᵐ[modularMeasure]
      (fun τ : UpperHalfPlane => g τ)) : EqOn f g modularInterior := by
  have hcoord := (ae_modularCoordinate_iff (fun z => f z = g z)).mpr hfg
  have hvol := (ae_modularCoordinate_iff_restrict (fun z => f z = g z)).mp hcoord
  exact MeasureTheory.Measure.eqOn_open_of_ae_eq hvol isOpen_modularInterior hf hg

/-- Hyperbolic directional derivatives of continuous equal representatives
are equal almost everywhere in the actual fundamental-domain measure. -/
theorem modularDirectional_ae_eq {f g : ℂ → ℂ}
    (hf : ContinuousOn f modularInterior) (hg : ContinuousOn g modularInterior)
    (hfg : (fun τ : UpperHalfPlane => f τ) =ᵐ[modularMeasure]
      (fun τ : UpperHalfPlane => g τ)) (v : ℂ) :
    (fun τ : UpperHalfPlane => (τ.im : ℂ) * fderiv ℝ f τ v) =ᵐ[modularMeasure]
      (fun τ : UpperHalfPlane => (τ.im : ℂ) * fderiv ℝ g τ v) := by
  have heq := eqOn_modularInterior_of_ae_eq hf hg hfg
  filter_upwards [ae_mem_fdo] with τ hτ
  have hgerm : f =ᶠ[nhds (τ : ℂ)] g := by
    filter_upwards [isOpen_modularInterior.mem_nhds (show (τ : ℂ) ∈ modularInterior from
      ⟨τ, hτ, rfl⟩)] with z hz
    exact heq hz
  rw [hgerm.fderiv_eq]

end GapFamily.Analytic
