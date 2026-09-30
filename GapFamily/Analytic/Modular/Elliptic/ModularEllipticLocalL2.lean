import GapFamily.Analytic.Modular.ModularLaplacianDistribution

/-!
# Ordinary local L² bounds for actual modular operator coordinates

The inverse-square hyperbolic density is canceled on each compact interior set.
Bounded continuous height factors give local L² for the actual value, weak
Euclidean derivatives, and divided operator source.
-/

noncomputable section

namespace GapFamily.Analytic

open Set MeasureTheory

/-- An actual modular Hilbert vector is ordinarily square-integrable on each compact interior set. -/
theorem modularCoordinate_memLp_on_compact (f : ModularCoordinateHilbert)
    {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ modularInterior) :
    MemLp (fun z => f z) 2 (volume.restrict K) := by
  have hflocal := modularCoordinate_integrableOn_compact f hK hKU
  apply (memLp_two_iff_integrable_sq_norm hflocal.aestronglyMeasurable).mpr
  have hf : Integrable (fun z => ‖f z‖ ^ 2) modularCoordinateMeasure :=
    (memLp_two_iff_integrable_sq_norm (Lp.memLp f).aestronglyMeasurable).mp (Lp.memLp f)
  have hw : IntegrableOn (fun z => z.im ^ 2 * ‖f z‖ ^ 2) K modularCoordinateMeasure :=
    hf.integrableOn.continuousOn_mul (by fun_prop) hK
  rw [IntegrableOn, restrict_modularCoordinateMeasure hK.measurableSet hKU,
    Dirichlet.localHyperbolicMeasure,
    integrable_withDensity_iff_integrable_smul'
      (by fun_prop : Measurable (fun z : ℂ => ENNReal.ofReal (1 / z.im ^ 2)))
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))] at hw
  apply hw.congr
  filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
  rw [ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
  have hn : z.im ≠ 0 := (im_pos_of_mem_modularInterior (hKU hz)).ne'
  field_simp

/-- A continuous multiplier is bounded on the compact chart and preserves ordinary L². -/
theorem memLp_mul_continuousOn_compact {f c : ℂ → ℂ} {K : Set ℂ}
    (hK : IsCompact K) (hf : MemLp f 2 (volume.restrict K))
    (hc : ContinuousOn c K) :
    MemLp (fun z => f z * c z) 2 (volume.restrict K) := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc
  apply hf.of_le_mul (c := C) (hf.aestronglyMeasurable.mul
    (hc.aestronglyMeasurable hK.measurableSet))
  filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
  rw [Pi.mul_apply, norm_mul]
  exact (mul_le_mul_of_nonneg_left (hC z hz) (norm_nonneg _)).trans_eq (mul_comm _ _)

/-- Any fixed inverse height power preserves local square integrability strictly inside the chart. -/
theorem modularCoordinate_div_im_pow_memLp_on_compact
    (f : ModularCoordinateHilbert) (n : ℕ)
    {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ modularInterior) :
    MemLp (fun z => f z / (z.im : ℂ) ^ n) 2 (volume.restrict K) := by
  have hc : ContinuousOn (fun z : ℂ => ((z.im : ℂ) ^ n)⁻¹) K := by
    apply ContinuousOn.inv₀
    · fun_prop
    · intro z hz
      exact pow_ne_zero _ (by exact_mod_cast (im_pos_of_mem_modularInterior (hKU hz)).ne')
  simpa only [div_eq_mul_inv] using
    memLp_mul_continuousOn_compact hK (modularCoordinate_memLp_on_compact f hK hKU) hc

namespace ModularGradient

/-- All four actual fields needed by local weak-Poisson regularity belong to ordinary local L². -/
theorem laplacian_coordinate_fields_memLp_on_compact (u : laplacian.domain)
    {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ modularInterior) :
    MemLp (fun z => coordinateValue ⟨u, laplacian_domain_le u.property⟩ z) 2 (volume.restrict K) ∧
    MemLp (coordinateDx ⟨u, laplacian_domain_le u.property⟩) 2 (volume.restrict K) ∧
    MemLp (coordinateDy ⟨u, laplacian_domain_le u.property⟩) 2 (volume.restrict K) ∧
    MemLp (coordinateSource u) 2 (volume.restrict K) := by
  refine ⟨modularCoordinate_memLp_on_compact _ hK hKU, ?_, ?_, ?_⟩
  · convert modularCoordinate_div_im_pow_memLp_on_compact
        (modularCoordinateEquiv.symm ((WithLp.ofLp
          (closedGradient ⟨u, laplacian_domain_le u.property⟩)).1)) 1 hK hKU using 1
    ext z
    simp [coordinateDx]
  · convert modularCoordinate_div_im_pow_memLp_on_compact
        (modularCoordinateEquiv.symm ((WithLp.ofLp
          (closedGradient ⟨u, laplacian_domain_le u.property⟩)).2)) 1 hK hKU using 1
    ext z
    simp [coordinateDy]
  · exact modularCoordinate_div_im_pow_memLp_on_compact _ 2 hK hKU

end ModularGradient

end GapFamily.Analytic
