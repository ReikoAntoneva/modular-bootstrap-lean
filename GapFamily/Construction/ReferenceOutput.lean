import GapFamily.Construction.FiniteRepairState
import GapFamily.Construction.FiniteRepairHistory

/-! A modular reference and its actual ordinary Fourier output, independent
of the eventual marker location. In particular a threshold marker is allowed. -/

noncomputable section
namespace GapFamily.Construction

open Set MeasureTheory UpperHalfPlane
open Analytic PoincareEnergyContinuation PoincareEnergyFourier PoincareFourier
open scoped MatrixGroups

/-- An actual modular seed with the prescribed vacuum and a proved ordinary
Fourier expansion of its nonvacuum thermal measures. -/
structure ReferenceOutput (a : ℝ) where
  seed : UpperHalfPlane → ℂ
  thermalOutput : ℤ → ℝ → SignedMeasure ℝ
  seed_smul : ∀ (τ : UpperHalfPlane) (g : SL(2, ℤ)), seed (g • τ) = seed τ
  hasSum_seed_output : ∀ (y : ℝ) (hy : 0 < y) (x : ℝ),
    HasSum (fun j : ℤ => (Real.sqrt y : ℂ) *
      (thermalOutput j (2 * Real.pi * y) univ : ℂ) * cuspFourierMode j x)
      (seed (rowPoint y hy x) - vacuumDirectRow a y x)

namespace ReferenceOutput

/-- The inherited positive marker reference is one concrete instance. -/
def canonicalMarker (a b : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b) : ReferenceOutput a where
  seed := canonicalMarkerReferenceSeed a b ha hb
  thermalOutput := canonicalMarkerReferenceThermalMeasure a b ha hb
  seed_smul := canonicalMarkerReferenceSeed_smul a b ha hb
  hasSum_seed_output := hasSum_canonicalMarkerReferenceSeed_thermalMeasure a b ha hb

end ReferenceOutput

namespace FiniteRepairState

/-- The reference plus the literal finite list of canonical repairs. -/
def referenceSeed {a : ℝ} (s : FiniteRepairState) (ref : ReferenceOutput a)
    (τ : UpperHalfPlane) : ℂ := ref.seed τ + repairHistorySeed s.history τ

/-- The ordinary thermal output of that same function. -/
def referenceThermalOutput {a : ℝ} (s : FiniteRepairState) (ref : ReferenceOutput a)
    (j : ℤ) (t : ℝ) : SignedMeasure ℝ :=
  ref.thermalOutput j t + repairHistoryThermalOutput s.history j t

/-- The retained marker and nodes, plus the stored continuum, agree with
the ordinary output of the actual reference and repair history. -/
def HasReferenceOutput {a : ℝ} (s : FiniteRepairState) (ref : ReferenceOutput a)
    (δ : ℝ) : Prop :=
  ∀ (j : ℤ) (t : ℝ), 0 < t → s.referenceThermalOutput ref j t =
    s.atomicThermalOutput δ j t + s.continuumThermalOutput j t

theorem referenceSeed_smul {a : ℝ} (s : FiniteRepairState) (ref : ReferenceOutput a)
    (τ : UpperHalfPlane) (g : SL(2, ℤ)) :
    s.referenceSeed ref (g • τ) = s.referenceSeed ref τ := by
  simp only [referenceSeed, ref.seed_smul, repairHistorySeed_smul]

theorem hasSum_referenceSeed_output {a : ℝ} (s : FiniteRepairState)
    (ref : ReferenceOutput a) (y : ℝ) (hy : 0 < y) (x : ℝ) :
    HasSum (fun j : ℤ => (Real.sqrt y : ℂ) *
      (s.referenceThermalOutput ref j (2 * Real.pi * y) univ : ℂ) * cuspFourierMode j x)
      (s.referenceSeed ref (rowPoint y hy x) - vacuumDirectRow a y x) := by
  convert (ref.hasSum_seed_output y hy x).add
    (hasSum_repairHistorySeed_output s.history y hy x) using 1
  · funext j
    simp only [referenceThermalOutput, _root_.add_apply, Complex.ofReal_add,
      mul_add, add_mul]
  · unfold referenceSeed
    ring

theorem hasSum_referenceSeed_atomic_continuum {a : ℝ} (s : FiniteRepairState)
    (ref : ReferenceOutput a) (δ : ℝ) (ho : s.HasReferenceOutput ref δ)
    (y : ℝ) (hy : 0 < y) (x : ℝ) :
    HasSum (fun j : ℤ => (Real.sqrt y : ℂ) *
      ((s.atomicThermalOutput δ j (2 * Real.pi * y) univ +
        s.continuumThermalOutput j (2 * Real.pi * y) univ : ℝ) : ℂ) * cuspFourierMode j x)
      (s.referenceSeed ref (rowPoint y hy x) - vacuumDirectRow a y x) := by
  have ht : 0 < 2 * Real.pi * y := mul_pos (mul_pos (by norm_num) Real.pi_pos) hy
  have h := s.hasSum_referenceSeed_output ref y hy x
  simp only [ho _ _ ht, _root_.add_apply] at h
  exact h

end FiniteRepairState
end GapFamily.Construction
