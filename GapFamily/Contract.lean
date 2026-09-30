import Mathlib.NumberTheory.ModularForms.DedekindEta
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith

/-!
# Spectral class and character expansion

The support is a set of distinct weight pairs; multiplicities are natural
numbers required to be positive on that support. The vacuum is the separate
single character product in `partitionFunction`.
-/

noncomputable section

open scoped UpperHalfPlane

namespace GapFamily

/-- The shift for equal left and right central charges `c`. -/
def shift (c : ℝ) : ℝ := (c - 1) / 12

/-- The total dimension of a weight pair. -/
def dimension (p : ℝ × ℝ) : ℝ := p.1 + p.2

/-- The spin of a weight pair. -/
def spin (p : ℝ × ℝ) : ℝ := p.1 - p.2

/-- The energy above the character threshold. -/
def energy (c : ℝ) (p : ℝ × ℝ) : ℝ := dimension p - shift c

/-- A spectrum is a set of distinct nonvacuum weight pairs with multiplicity. -/
structure Spectrum where
  support : Set (ℝ × ℝ)
  multiplicity : (ℝ × ℝ) → ℕ

/-- Real powers of `q` use the exponential, not a branch of complex powers. -/
def qPower (r : ℝ) (τ : ℍ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (r : ℂ) * (τ : ℂ))

/-- The prescribed nondegenerate Virasoro character. -/
def primaryCharacter (c h : ℝ) (τ : ℍ) : ℂ :=
  qPower (h - shift c / 2) τ / ModularForm.eta τ

/-- The prescribed vacuum character, with its null descendant removed. -/
def vacuumCharacter (c : ℝ) (τ : ℍ) : ℂ :=
  qPower (-shift c / 2) τ * (1 - qPower 1 τ) / ModularForm.eta τ

/-- The character expansion of the same partition function used in crossing. -/
def partitionFunction (c : ℝ) (s : Spectrum) (τ : ℍ) : ℂ :=
  vacuumCharacter c τ * star (vacuumCharacter c τ) +
    ∑' p : s.support, (s.multiplicity p : ℂ) *
      primaryCharacter c p.val.1 τ * star (primaryCharacter c p.val.2 τ)

/-- The complete discrete integer torus conditions, including full S and T. -/
structure TorusAdmissible (c : ℝ) (s : Spectrum) : Prop where
  charge_gt_one : 1 < c
  weight_pos : ∀ p ∈ s.support, 0 < p.1 ∧ 0 < p.2
  multiplicity_pos : ∀ p ∈ s.support, 0 < s.multiplicity p
  spin_integral : ∀ p ∈ s.support, ∃ j : ℤ, spin p = (j : ℝ)
  locally_finite : ∀ D : ℝ, {p ∈ s.support | dimension p ≤ D}.Finite
  thermal_summable : ∀ y : ℝ, 0 < y →
    Summable (fun p : s.support =>
      (s.multiplicity p : ℝ) * Real.exp (-2 * Real.pi * y * dimension p))
  invariant_S : ∀ τ : ℍ,
    partitionFunction c s (ModularGroup.S • τ) = partitionFunction c s τ
  invariant_T : ∀ τ : ℍ,
    partitionFunction c s (ModularGroup.T • τ) = partitionFunction c s τ

/-- The pure condition is inclusive and constrains only nonvacuum primaries. -/
def PureAdmissible (c : ℝ) (s : Spectrum) : Prop :=
  TorusAdmissible c s ∧
    ∀ p ∈ s.support, shift c / 2 ≤ p.1 ∧ shift c / 2 ≤ p.2

/-- An attained minimum, with no convention silently inserted for empty spectra. -/
def HasGap (s : Spectrum) (g : ℝ) : Prop :=
  (∀ p ∈ s.support, g ≤ dimension p) ∧
    ∃ p ∈ s.support, dimension p = g

/-- The source's least dimension whenever an attained minimum exists. -/
def firstDimension (s : Spectrum) : ℝ := sInf (dimension '' s.support)

theorem eta_ne_zero (τ : ℍ) : ModularForm.eta τ ≠ 0 :=
  ModularForm.eta_ne_zero τ.2

/-- This equivalence includes the boundary `E = J = 0`. -/
theorem pure_bound_iff_energy_ge_abs_spin (c : ℝ) (p : ℝ × ℝ) :
    (shift c / 2 ≤ p.1 ∧ shift c / 2 ≤ p.2) ↔ |spin p| ≤ energy c p := by
  rw [abs_le]
  dsimp [spin, energy, dimension]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

theorem HasGap.isLeast {s : Spectrum} {g : ℝ} (h : HasGap s g) :
    IsLeast (dimension '' s.support) g := by
  constructor
  · rcases h.2 with ⟨p, hp, hg⟩
    exact ⟨p, hp, hg⟩
  · rintro d ⟨p, hp, rfl⟩
    exact h.1 p hp

theorem hasGap_iff_isLeast (s : Spectrum) (g : ℝ) :
    HasGap s g ↔ IsLeast (dimension '' s.support) g := by
  constructor
  · exact HasGap.isLeast
  · intro h
    refine ⟨?_, ?_⟩
    · intro p hp
      exact h.2 ⟨p, hp, rfl⟩
    · exact h.1

theorem HasGap.firstDimension_eq {s : Spectrum} {g : ℝ} (h : HasGap s g) :
    firstDimension s = g := h.isLeast.csInf_eq

theorem HasGap.unique {s : Spectrum} {g g' : ℝ}
    (h : HasGap s g) (h' : HasGap s g') : g = g' :=
  h.firstDimension_eq.symm.trans h'.firstDimension_eq

/-- Local finiteness supplies an attained minimum after any primary is given. -/
theorem exists_hasGap_of_locally_finite {s : Spectrum}
    (hloc : ∀ D : ℝ, {p ∈ s.support | dimension p ≤ D}.Finite)
    (hne : s.support.Nonempty) : ∃ g : ℝ, HasGap s g := by
  obtain ⟨p₀, hp₀⟩ := hne
  obtain ⟨p, hp, hmin⟩ := Set.exists_min_image
    {q ∈ s.support | dimension q ≤ dimension p₀} dimension
    (hloc (dimension p₀)) ⟨p₀, hp₀, le_rfl⟩
  refine ⟨dimension p, ?_, p, hp.1, rfl⟩
  intro q hq
  by_cases hle : dimension q ≤ dimension p₀
  · exact hmin q ⟨hq, hle⟩
  · exact hp.2.trans (le_of_not_ge hle)

theorem TorusAdmissible.hasGap_firstDimension {c : ℝ} {s : Spectrum}
    (h : TorusAdmissible c s) (hne : s.support.Nonempty) :
    HasGap s (firstDimension s) := by
  obtain ⟨g, hg⟩ := exists_hasGap_of_locally_finite h.locally_finite hne
  simpa only [hg.firstDimension_eq] using hg

end GapFamily
