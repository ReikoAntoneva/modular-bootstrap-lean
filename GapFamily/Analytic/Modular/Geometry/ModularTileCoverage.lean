import GapFamily.Analytic.Modular.Geometry.ModularSeamMeasure
import GapFamily.Analytic.Modular.ModularBoundary
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Basic.Countable.Basic
import GapFamily.Analytic.Modular.Geometry.ModularTilePairCount

noncomputable section
namespace GapFamily.Analytic
open Set MeasureTheory Filter UpperHalfPlane
open scoped MatrixGroups Pointwise ENNReal Classical

private theorem modularGroup_countable : Countable SL(2, ℤ) := by
  have : Countable (Matrix (Fin 2) (Fin 2) ℤ) := by
    change Countable (Fin 2 → Fin 2 → ℤ)
    infer_instance
  change Countable {A : Matrix (Fin 2) (Fin 2) ℤ // A.det = 1}
  infer_instance

/-- Away from the countable orbit of the null boundary, one translate lies in the open tile. -/
theorem ae_exists_modular_smul_mem_fdo :
    ∀ᵐ τ : UpperHalfPlane ∂volume, ∃ γ : SL(2, ℤ), γ • τ ∈ ModularGroup.fdo := by
  have : Countable SL(2, ℤ) := modularGroup_countable
  have hγ (γ : SL(2, ℤ)) : ∀ᵐ τ : UpperHalfPlane ∂volume,
      γ • τ ∈ ModularGroup.fd → γ • τ ∈ ModularGroup.fdo := by
    filter_upwards [(measurePreserving_modularAction γ).quasiMeasurePreserving.ae fd_ae_eq_fdo]
      with τ hτ hmem
    exact hτ ▸ hmem
  filter_upwards [ae_all_iff.mpr hγ] with τ hτ
  obtain ⟨γ, hγ⟩ := ModularGroup.exists_smul_mem_fd τ
  exact ⟨γ, hτ γ hγ⟩

/-- Full matrix-group translates count every ordinary point twice almost everywhere. -/
theorem ae_modular_fd_indicator_tsum_eq_two :
    ∀ᵐ τ : UpperHalfPlane ∂volume,
      (∑' γ : SL(2, ℤ), if γ • τ ∈ ModularGroup.fd then (1 : ℝ≥0∞) else 0) = 2 := by
  filter_upwards [ae_exists_modular_smul_mem_fdo] with τ hτ
  obtain ⟨γ, hγ⟩ := hτ
  exact modularAction_fd_indicator_tsum_eq_two hγ

/-- The same exact multiplicity in the image-tile convention. -/
theorem ae_modular_tile_indicator_tsum_eq_two :
    ∀ᵐ τ : UpperHalfPlane ∂volume,
      (∑' γ : SL(2, ℤ), (γ • ModularGroup.fd).indicator (fun _ => (1 : ℝ≥0∞)) τ) = 2 := by
  filter_upwards [ae_modular_fd_indicator_tsum_eq_two] with τ hτ
  calc
    _ = ∑' γ : SL(2, ℤ), if γ⁻¹ • τ ∈ ModularGroup.fd then (1 : ℝ≥0∞) else 0 := by
      apply tsum_congr
      intro γ
      simp only [Set.indicator_apply, Set.mem_smul_set_iff_inv_smul_mem]
    _ = ∑' γ : SL(2, ℤ), if γ • τ ∈ ModularGroup.fd then (1 : ℝ≥0∞) else 0 :=
      (Equiv.inv (SL(2, ℤ))).tsum_eq
        (fun γ : SL(2, ℤ) => if γ • τ ∈ ModularGroup.fd then (1 : ℝ≥0∞) else 0)
    _ = 2 := hτ

/-- Exact measure-level twofold tiling for the full matrix group. -/
theorem sum_restrict_modular_tiles_eq_two_smul_volume :
    (Measure.sum fun γ : SL(2, ℤ) =>
      (volume : Measure UpperHalfPlane).restrict (γ • ModularGroup.fd)) =
      (2 : ℝ≥0∞) • (volume : Measure UpperHalfPlane) := by
  have : Countable SL(2, ℤ) := modularGroup_countable
  have hm (γ : SL(2, ℤ)) : MeasurableSet (γ • ModularGroup.fd) := by
    rw [← Set.image_smul]
    exact (measurableEmbedding_modularAction γ).measurableSet_image.mpr
      ModularGroup.isClosed_fd.measurableSet
  calc
    _ = Measure.sum (fun γ : SL(2, ℤ) =>
        (volume : Measure UpperHalfPlane).withDensity
          ((γ • ModularGroup.fd).indicator (fun _ => (1 : ℝ≥0∞)))) := by
      congr 1
      funext γ
      exact (withDensity_indicator_one (hm γ)).symm
    _ = (volume : Measure UpperHalfPlane).withDensity
        (∑' γ : SL(2, ℤ), (γ • ModularGroup.fd).indicator (fun _ => (1 : ℝ≥0∞))) := by
      symm
      exact withDensity_tsum (fun γ => measurable_const.indicator (hm γ))
    _ = (volume : Measure UpperHalfPlane).withDensity (fun _ => (2 : ℝ≥0∞)) := by
      apply withDensity_congr_ae
      filter_upwards [ae_modular_tile_indicator_tsum_eq_two] with τ hτ
      rw [Pi.tsum_apply (Pi.summable.2 (fun _ => ENNReal.summable))]
      exact hτ
    _ = _ := withDensity_const _

end GapFamily.Analytic
