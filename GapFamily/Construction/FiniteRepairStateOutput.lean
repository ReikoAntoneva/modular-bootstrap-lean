import GapFamily.Construction.FiniteRepairState
import GapFamily.Construction.FiniteRepairHistoryRegularity

/-! The modular seed and its Fourier output computed from a concrete finite
repair state. The atom and continuum identity is a measure invariant, while
modularity and ordinary Fourier convergence follow from the actual history. -/

noncomputable section
namespace GapFamily.Construction.FiniteRepairState

open Set MeasureTheory UpperHalfPlane
open Analytic PoincareEnergyContinuation PoincareEnergyFourier PoincareFourier
open scoped MatrixGroups

/-- The actual marker reference plus the state's literal canonical repair history. -/
def seed (s : FiniteRepairState) (a b : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b) :
    UpperHalfPlane → ℂ :=
  finiteRepairHistorySeed a b ha hb s.history

/-- The ordinary signed thermal measure of that same modular seed. -/
def thermalOutput (s : FiniteRepairState) (a b : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b)
    (j : ℤ) (t : ℝ) : SignedMeasure ℝ :=
  finiteRepairHistoryThermalMeasure a b ha hb s.history j t

/-- The literal history output agrees with the retained atoms and stored
ordinary continuum. This does not assume modularity or Fourier reconstruction. -/
def HasThermalOutput (s : FiniteRepairState) (a b : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b) : Prop :=
  ∀ (j : ℤ) (t : ℝ), 0 < t →
    s.thermalOutput a b ha hb j t = s.atomicThermalOutput b j t + s.continuumThermalOutput j t

theorem seed_smul (s : FiniteRepairState) (a b : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b)
    (τ : UpperHalfPlane) (g : SL(2, ℤ)) :
    s.seed a b ha hb (g • τ) = s.seed a b ha hb τ :=
  finiteRepairHistorySeed_smul a b ha hb s.history τ g

theorem continuous_seed (s : FiniteRepairState) (a b : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b) :
    Continuous (s.seed a b ha hb) :=
  continuous_finiteRepairHistorySeed a b ha hb s.history

theorem summable_thermalOutput_totalVariation (s : FiniteRepairState)
    (a b : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b) {t : ℝ} (ht : 0 < t) :
    Summable (fun j : ℤ => (s.thermalOutput a b ha hb j t).variation.real univ) :=
  summable_finiteRepairHistoryThermalMeasure_totalVariation a b ha hb s.history ht

theorem thermalOutput_ae_physical (s : FiniteRepairState)
    (a b : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b) (j : ℤ) {t : ℝ} (ht : 0 < t) :
    ∀ᵐ E ∂(s.thermalOutput a b ha hb j t).variation, |(j : ℝ)| ≤ E :=
  finiteRepairHistoryThermalMeasure_ae_physical a b ha hb s.history j ht

theorem thermalOutput_singleton (s : FiniteRepairState)
    (a b : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b) (j : ℤ) {t : ℝ} (ht : 0 < t) (e : ℝ) :
    s.thermalOutput a b ha hb j t {e} = Real.exp (-t * e) *
      ((if j = 0 ∧ e = b then 1 else 0) + repairHistoryRawInput s.history j {e}) :=
  finiteRepairHistoryThermalMeasure_singleton a b ha hb s.history j ht e

/-- The ordinary convergent Fourier series is supplied by the constructed
canonical seed itself, without a reconstruction premise on the state. -/
theorem hasSum_seed_output (s : FiniteRepairState)
    (a b : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b) (y : ℝ) (hy : 0 < y) (x : ℝ) :
    HasSum (fun j : ℤ => (Real.sqrt y : ℂ) *
      (s.thermalOutput a b ha hb j (2 * Real.pi * y) univ : ℂ) * cuspFourierMode j x)
      (s.seed a b ha hb (rowPoint y hy x) - vacuumDirectRow a y x) :=
  hasSum_finiteRepairHistorySeed_output a b ha hb s.history y hy x

/-- The actual state measure invariant yields the atom-plus-continuum Fourier
output of the same modular seed. -/
theorem hasSum_seed_atomic_continuum (s : FiniteRepairState)
    (a b : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b) (ho : s.HasThermalOutput a b ha hb)
    (y : ℝ) (hy : 0 < y) (x : ℝ) :
    HasSum (fun j : ℤ => (Real.sqrt y : ℂ) *
      ((s.atomicThermalOutput b j (2 * Real.pi * y) univ +
        s.continuumThermalOutput j (2 * Real.pi * y) univ : ℝ) : ℂ) * cuspFourierMode j x)
      (s.seed a b ha hb (rowPoint y hy x) - vacuumDirectRow a y x) := by
  have ht : 0 < 2 * Real.pi * y := mul_pos (mul_pos (by norm_num) Real.pi_pos) hy
  have h := s.hasSum_seed_output a b ha hb y hy x
  simp only [ho _ _ ht, _root_.add_apply] at h
  exact h

theorem seed_eq_atomic_continuum_output (s : FiniteRepairState)
    (a b : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b) (ho : s.HasThermalOutput a b ha hb)
    (y : ℝ) (hy : 0 < y) (x : ℝ) :
    s.seed a b ha hb (rowPoint y hy x) = vacuumDirectRow a y x +
      ∑' j : ℤ, (Real.sqrt y : ℂ) *
        ((s.atomicThermalOutput b j (2 * Real.pi * y) univ +
          s.continuumThermalOutput j (2 * Real.pi * y) univ : ℝ) : ℂ) * cuspFourierMode j x := by
  rw [(s.hasSum_seed_atomic_continuum a b ha hb ho y hy x).tsum_eq]
  ring

end GapFamily.Construction.FiniteRepairState
