import GapFamily.Analytic.Modular.Geometry.ModularSeamCoordinateMeasure

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open MeasureTheory Set UpperHalfPlane

private theorem upperHalfPlane_density_cancel (f : ℂ → ℂ) (τ : UpperHalfPlane) :
    τ.im ^ 2 • (f τ / (((τ : ℂ).im : ℂ) ^ 2)) = f τ := by
  rw [Complex.real_smul, Complex.ofReal_pow]
  change (τ.im : ℂ) ^ 2 * (f τ / (τ.im : ℂ) ^ 2) = f τ
  field_simp [Complex.ofReal_ne_zero.mpr τ.im_pos.ne']

private theorem preimage_upperHalfPlaneSet_eq_univ :
    UpperHalfPlane.coe ⁻¹' upperHalfPlaneSet = univ := by
  ext τ
  exact iff_true_intro τ.im_pos

/-- Hyperbolic integrability is exactly Euclidean integrability with the actual inverse-square
height density, for a complex function vanishing outside the upper half-plane. -/
theorem integrable_upperHalfPlane_iff_complex_density (f : ℂ → ℂ)
    (hfzero : ∀ z ∉ upperHalfPlaneSet, f z = 0) :
    Integrable (fun τ : UpperHalfPlane => f τ) volume ↔
      Integrable (fun z : ℂ => f z / (z.im : ℂ) ^ 2) volume := by
  have hsupport : Function.support (fun z : ℂ => f z / (z.im : ℂ) ^ 2) ⊆
      upperHalfPlaneSet := by
    intro z hz
    by_contra hnot
    exact hz (by simp [hfzero z hnot])
  have h := integrableOn_upperHalfPlane_im_sq_smul_iff
    isOpen_upperHalfPlaneSet.measurableSet (fun _ hz => hz)
    (fun z : ℂ => f z / (z.im : ℂ) ^ 2)
  rw [preimage_upperHalfPlaneSet_eq_univ, integrableOn_univ] at h
  simpa only [upperHalfPlane_density_cancel] using
    h.trans (integrableOn_iff_integrable_of_support_subset hsupport)

/-- Exact coordinate transfer of the full hyperbolic integral. No integrability assumption is
needed for this identity; the preceding equivalence supplies genuine convergence independently. -/
theorem integral_upperHalfPlane_eq_complex_density (f : ℂ → ℂ)
    (hfzero : ∀ z ∉ upperHalfPlaneSet, f z = 0) :
    (∫ τ : UpperHalfPlane, f τ) = ∫ z : ℂ, f z / (z.im : ℂ) ^ 2 := by
  have h := setIntegral_eq_upperHalfPlane_im_sq_smul
    isOpen_upperHalfPlaneSet.measurableSet (fun _ hz => hz)
    (fun z : ℂ => f z / (z.im : ℂ) ^ 2)
  rw [preimage_upperHalfPlaneSet_eq_univ, setIntegral_univ] at h
  have hset : (∫ z in upperHalfPlaneSet, f z / (z.im : ℂ) ^ 2) =
      ∫ z : ℂ, f z / (z.im : ℂ) ^ 2 :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
      rw [hfzero z hz, zero_div])
  simpa only [upperHalfPlane_density_cancel] using h.symm.trans hset

end GapFamily.Analytic.SpatialPoint
