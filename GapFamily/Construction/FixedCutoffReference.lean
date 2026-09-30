import GapFamily.Construction.MarkerReferenceOutputSupport
import GapFamily.Construction.FixedCutoffMarkerRepair

/-!
# A reference with independent cutoff and prescribed gap

The vacuum reference is initialized at `B`, while the exact modular transfer
places its sole primary atom at any `δ ∈ [0,B]`. These are signed reference
outputs: positivity of the continuum and its subsequent integer discretization
are separate construction steps.
-/

noncomputable section

open MeasureTheory Set UpperHalfPlane
open scoped Classical BigOperators MatrixGroups

namespace GapFamily.Construction

open Analytic PoincareEnergyContinuation PoincareEnergyFourier PoincareFourier

variable (a B δ : ℝ) (ha : 2 ≤ a) (hB : 1 ≤ B) (hδ : 0 ≤ δ) (hδB : δ ≤ B)

/-- The actual modular reference with cutoff and marker location separated. -/
def fixedCutoffReferenceSeed (τ : UpperHalfPlane) : ℂ :=
  canonicalMarkerReferenceSeed a B ha hB τ +
    fixedCutoffMarkerRepairSeed B δ hB hδ hδB τ

theorem fixedCutoffReferenceSeed_smul (τ : UpperHalfPlane) (g : SL(2, ℤ)) :
    fixedCutoffReferenceSeed a B δ ha hB hδ hδB (g • τ) =
      fixedCutoffReferenceSeed a B δ ha hB hδ hδB τ := by
  simp only [fixedCutoffReferenceSeed, canonicalMarkerReferenceSeed_smul,
    fixedCutoffMarkerRepairSeed_smul]

/-- Ordinary signed primary output of precisely the same modular reference. -/
def fixedCutoffReferenceThermalMeasure (j : ℤ) (t : ℝ) : SignedMeasure ℝ :=
  canonicalMarkerReferenceThermalMeasure a B ha hB j t +
    fixedCutoffMarkerRepairThermalMeasure B δ hB hδ hδB j t

/-- The reference has exactly one scalar unit atom at the prescribed location,
including a unit scalar threshold atom when `δ = 0`. -/
theorem fixedCutoffReferenceThermalMeasure_singleton (j : ℤ)
    {t : ℝ} (ht : 0 < t) (e : ℝ) :
    fixedCutoffReferenceThermalMeasure a B δ ha hB hδ hδB j t {e} =
      if j = 0 ∧ e = δ then Real.exp (-t * e) else 0 := by
  unfold fixedCutoffReferenceThermalMeasure
  rw [_root_.add_apply, canonicalMarkerReferenceThermalMeasure_singleton a B ha hB j ht e,
    fixedCutoffMarkerRepairThermalMeasure_singleton B δ hB hδ hδB j ht e]
  ring

/-- In particular the endpoint is established directly, without a limit in `δ`. -/
theorem fixedCutoffReferenceThermalMeasure_zero_gap (j : ℤ) {t : ℝ} (ht : 0 < t) :
    fixedCutoffReferenceThermalMeasure a B 0 ha hB le_rfl
      (by linarith) j t {0} = if j = 0 then 1 else 0 := by
  rw [fixedCutoffReferenceThermalMeasure_singleton a B 0 ha hB le_rfl
    (by linarith) j ht 0]
  simp

/-- The complete Fourier–Laplace series reconstructs the actual modular seed. -/
theorem hasSum_fixedCutoffReferenceSeed_thermalMeasure
    (y : ℝ) (hy : 0 < y) (x : ℝ) :
    HasSum (fun j : ℤ => (Real.sqrt y : ℂ) *
      (fixedCutoffReferenceThermalMeasure a B δ ha hB hδ hδB j
        (2 * Real.pi * y) univ : ℂ) * cuspFourierMode j x)
      (fixedCutoffReferenceSeed a B δ ha hB hδ hδB (rowPoint y hy x) -
        vacuumDirectRow a y x) := by
  have h := (hasSum_canonicalMarkerReferenceSeed_thermalMeasure a B ha hB y hy x).add
    (hasSum_fixedCutoffMarkerRepairSeed_output B δ hB hδ hδB y hy x)
  convert h using 1
  · funext j
    simp only [fixedCutoffReferenceThermalMeasure, _root_.add_apply, Complex.ofReal_add]
    ring
  · unfold fixedCutoffReferenceSeed
    ring

/-- The Fourier series of this same ordinary output is absolutely convergent. -/
theorem summable_norm_fixedCutoffReferenceSeed_thermalMeasure
    (y : ℝ) (hy : 0 < y) (x : ℝ) :
    Summable (fun j : ℤ => ‖(Real.sqrt y : ℂ) *
      (fixedCutoffReferenceThermalMeasure a B δ ha hB hδ hδB j
        (2 * Real.pi * y) univ : ℂ) * cuspFourierMode j x‖) :=
  (hasSum_fixedCutoffReferenceSeed_thermalMeasure a B δ ha hB hδ hδB y hy x).summable.norm

/-- The complete modular output retains the inherited single direct vacuum. -/
theorem fixedCutoffReferenceSeed_eq_full_output (y : ℝ) (hy : 0 < y) (x : ℝ) :
    fixedCutoffReferenceSeed a B δ ha hB hδ hδB (rowPoint y hy x) =
      vacuumDirectRow a y x + ∑' j : ℤ, (Real.sqrt y : ℂ) *
        (fixedCutoffReferenceThermalMeasure a B δ ha hB hδ hδB j
          (2 * Real.pi * y) univ : ℂ) * cuspFourierMode j x := by
  rw [(hasSum_fixedCutoffReferenceSeed_thermalMeasure a B δ ha hB hδ hδB y hy x).tsum_eq]
  ring

end GapFamily.Construction
