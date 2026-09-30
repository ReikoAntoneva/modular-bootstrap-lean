import GapFamily.Analytic.Foundation.ThresholdAnchorBandMeasure
import GapFamily.Analytic.Foundation.SignedDensityPairing
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Function.L2Space

/-!
# The ordinary high-band part of a threshold anchor

The scalar threshold response is an explicit real function `ζ`. Its positive
square mass is a hypothesis here; the actual inverse and propagation argument
must establish that hypothesis before these formulas give an anchor.
The numerator and its ordinary signed measure are separate objects.
-/

noncomputable section

open MeasureTheory Set

namespace GapFamily.Analytic

/-- The square mass of the actual scalar response on the high band. -/
def scalarAnchorSquareMass (B : ℝ) (ζ : ℝ → ℝ) : ℝ :=
  ∫ E, ζ E ^ 2 ∂scalarAnchorReference B

/-- The normalized scalar response, before extending by zero outside the band. -/
def scalarAnchorBandDensity (B : ℝ) (ζ : ℝ → ℝ) (E : ℝ) : ℝ :=
  ζ E / scalarAnchorSquareMass B ζ

/-- The ordinary scalar numerator on the full reference half-line. -/
def scalarAnchorNumerator (B : ℝ) (ζ : ℝ → ℝ) : ℝ → ℝ :=
  (scalarAnchorBand B).indicator (scalarAnchorBandDensity B ζ)

theorem scalarAnchorSquareMass_nonneg (B : ℝ) (ζ : ℝ → ℝ) :
    0 ≤ scalarAnchorSquareMass B ζ := integral_nonneg (fun _ => sq_nonneg _)

theorem scalarAnchorBandDensity_integrable (B : ℝ) (hB : 0 < B)
    (ζ : ℝ → ℝ) (hζ : ContinuousOn ζ (scalarAnchorBand B)) :
    Integrable (scalarAnchorBandDensity B ζ) (scalarAnchorReference B) :=
  scalarAnchorReference_continuousOn_integrable B hB
    (hζ.div_const (scalarAnchorSquareMass B ζ))

/-- The numerator is genuinely ordinarily integrable against `dE/E`. -/
theorem scalarAnchorNumerator_integrable (B : ℝ) (hB : 0 < B)
    (ζ : ℝ → ℝ) (hζ : ContinuousOn ζ (scalarAnchorBand B)) :
    Integrable (scalarAnchorNumerator B ζ) (referenceMeasure 0) := by
  apply (integrable_indicator_iff (show MeasurableSet (scalarAnchorBand B) from
    measurableSet_Icc)).mpr
  exact scalarAnchorBandDensity_integrable B hB ζ hζ

/-- Hilbert membership follows from actual square integrability on the finite band. -/
theorem scalarAnchorBandDensity_memLp (B : ℝ) (hB : 0 < B)
    (ζ : ℝ → ℝ) (hζ : ContinuousOn ζ (scalarAnchorBand B)) :
    MemLp (scalarAnchorBandDensity B ζ) 2 (scalarAnchorReference B) := by
  apply (memLp_two_iff_integrable_sq
    (scalarAnchorBandDensity_integrable B hB ζ hζ).aestronglyMeasurable).mpr
  exact scalarAnchorReference_continuousOn_integrable B hB
    ((hζ.div_const (scalarAnchorSquareMass B ζ)).pow 2)

/-- Zero extension gives a scalar Hilbert numerator on the full physical row. -/
theorem scalarAnchorNumerator_memLp (B : ℝ) (hB : 0 < B)
    (ζ : ℝ → ℝ) (hζ : ContinuousOn ζ (scalarAnchorBand B)) :
    MemLp (scalarAnchorNumerator B ζ) 2 (referenceMeasure 0) := by
  simpa only [scalarAnchorNumerator] using!
    (memLp_indicator_iff_restrict (measurableSet_scalarAnchorBand B)).mpr
      (scalarAnchorBandDensity_memLp B hB ζ hζ)

/-- The Hilbert square mass of the normalized numerator is exactly `1/I_B`. -/
theorem integral_sq_scalarAnchorBandDensity (B : ℝ) (ζ : ℝ → ℝ)
    (hI : 0 < scalarAnchorSquareMass B ζ) :
    (∫ E, scalarAnchorBandDensity B ζ E ^ 2 ∂scalarAnchorReference B) =
      1 / scalarAnchorSquareMass B ζ := by
  simp only [scalarAnchorBandDensity, div_pow]
  rw [integral_div]
  change scalarAnchorSquareMass B ζ / scalarAnchorSquareMass B ζ ^ 2 = _
  field_simp [hI.ne']

/-- The ordinary signed high-band seed, formed with its proved integrable density. -/
def scalarAnchorBandMeasure (B : ℝ) (_hB : 0 < B)
    (ζ : ℝ → ℝ) (_hζ : ContinuousOn ζ (scalarAnchorBand B)) : SignedMeasure ℝ :=
  (scalarAnchorReference B).withDensityᵥ (scalarAnchorBandDensity B ζ)

/-- Every measurable set has the literal ordinary density integral as its mass. -/
theorem scalarAnchorBandMeasure_apply (B : ℝ) (hB : 0 < B)
    (ζ : ℝ → ℝ) (hζ : ContinuousOn ζ (scalarAnchorBand B))
    (s : Set ℝ) (hs : MeasurableSet s) :
    scalarAnchorBandMeasure B hB ζ hζ s =
      ∫ E in s, scalarAnchorBandDensity B ζ E ∂scalarAnchorReference B := by
  exact withDensityᵥ_apply (scalarAnchorBandDensity_integrable B hB ζ hζ) hs

/-- The band measure is precisely the ordinary measure of the zero-extended
numerator against the original physical reference measure. -/
theorem scalarAnchorBandMeasure_eq_referenceDensity (B : ℝ) (hB : 0 < B)
    (ζ : ℝ → ℝ) (hζ : ContinuousOn ζ (scalarAnchorBand B)) :
    scalarAnchorBandMeasure B hB ζ hζ =
      (referenceMeasure 0).withDensityᵥ (scalarAnchorNumerator B ζ) := by
  ext s hs
  rw [scalarAnchorBandMeasure_apply B hB ζ hζ s hs,
    withDensityᵥ_apply (scalarAnchorNumerator_integrable B hB ζ hζ) hs,
    scalarAnchorNumerator, integral_indicator (measurableSet_scalarAnchorBand B),
    scalarAnchorReference, Measure.restrict_restrict hs,
    Measure.restrict_restrict (measurableSet_scalarAnchorBand B), inter_comm s]

/-- The raw scalar mass is kept distinct from the normalized response pairing. -/
theorem scalarAnchorBandMeasure_univ (B : ℝ) (hB : 0 < B)
    (ζ : ℝ → ℝ) (hζ : ContinuousOn ζ (scalarAnchorBand B)) :
    scalarAnchorBandMeasure B hB ζ hζ univ =
      (∫ E, ζ E ∂scalarAnchorReference B) / scalarAnchorSquareMass B ζ := by
  rw [scalarAnchorBandMeasure_apply B hB ζ hζ univ MeasurableSet.univ,
    Measure.restrict_univ]
  exact integral_div _ _

/-- The signed seed has no point atoms, including band endpoints and the scalar origin. -/
@[simp] theorem scalarAnchorBandMeasure_singleton (B : ℝ) (hB : 0 < B)
    (ζ : ℝ → ℝ) (hζ : ContinuousOn ζ (scalarAnchorBand B)) (E : ℝ) :
    scalarAnchorBandMeasure B hB ζ hζ {E} = 0 := by
  rw [scalarAnchorBandMeasure_apply B hB ζ hζ _ (measurableSet_singleton E)]
  simp

/-- The ordinary measure is supported on the prescribed high band. -/
theorem scalarAnchorBandMeasure_eq_zero_of_disjoint (B : ℝ) (hB : 0 < B)
    (ζ : ℝ → ℝ) (hζ : ContinuousOn ζ (scalarAnchorBand B))
    (s : Set ℝ) (hs : MeasurableSet s) (hdis : Disjoint s (scalarAnchorBand B)) :
    scalarAnchorBandMeasure B hB ζ hζ s = 0 := by
  rw [scalarAnchorBandMeasure_apply B hB ζ hζ s hs, scalarAnchorReference,
    Measure.restrict_restrict hs, hdis.inter_eq, Measure.restrict_empty,
    integral_zero_measure]

/-- Every continuous test on the high band has an ordinary signed integral,
equal to the normalized weighted reference integral. -/
theorem scalarAnchorBandMeasure_integral_continuousOn (B : ℝ) (hB : 0 < B)
    (ζ : ℝ → ℝ) (hζ : ContinuousOn ζ (scalarAnchorBand B))
    (f : ℝ → ℝ) (hf : ContinuousOn f (scalarAnchorBand B)) :
    (scalarAnchorBandMeasure B hB ζ hζ).Integrable f ∧
      (∫ᵛ E, f E ∂<•scalarAnchorBandMeasure B hB ζ hζ) =
        (∫ E, ζ E * f E ∂scalarAnchorReference B) / scalarAnchorSquareMass B ζ := by
  obtain ⟨M, hM⟩ := (isCompact_scalarAnchorBand B).exists_bound_of_continuousOn hf
  have hb : ∀ᵐ E ∂scalarAnchorReference B, ‖f E‖ ≤ M := by
    filter_upwards [scalarAnchorReference_ae_mem B] with E hE
    exact hM E hE
  obtain ⟨hi, _, heq⟩ := signedDensity_pairing_of_norm_bdd
    (scalarAnchorBandDensity_integrable B hB ζ hζ)
    (scalarAnchorReference_continuousOn_aestronglyMeasurable B hB hf) hb
  refine ⟨hi, ?_⟩
  rw [show scalarAnchorBandMeasure B hB ζ hζ =
    (scalarAnchorReference B).withDensityᵥ (scalarAnchorBandDensity B ζ) from rfl, heq]
  have hfun : (fun E => scalarAnchorBandDensity B ζ E * f E) =
      (fun E => (ζ E * f E) / scalarAnchorSquareMass B ζ) := by
    funext E
    simp only [scalarAnchorBandDensity]
    ring
  rw [hfun, integral_div]

/-- The exact normalization is an ordinary signed integral, not a formal pairing. -/
theorem scalarAnchorBandMeasure_pairing (B : ℝ) (hB : 0 < B)
    (ζ : ℝ → ℝ) (hζ : ContinuousOn ζ (scalarAnchorBand B))
    (hI : 0 < scalarAnchorSquareMass B ζ) :
    (scalarAnchorBandMeasure B hB ζ hζ).Integrable ζ ∧
      (∫ᵛ E, ζ E ∂<•scalarAnchorBandMeasure B hB ζ hζ) = 1 := by
  obtain ⟨hi, heq⟩ := scalarAnchorBandMeasure_integral_continuousOn B hB ζ hζ ζ hζ
  refine ⟨hi, ?_⟩
  rw [heq]
  simp only [← sq]
  exact div_self hI.ne'

end GapFamily.Analytic
