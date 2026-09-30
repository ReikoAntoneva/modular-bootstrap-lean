import GapFamily.Contract
import GapFamily.Regrouping
import Mathlib.Tactic.Ring

/-!
# Unit nodes and the public spectrum

Repeated unit nodes are merged into distinct weight pairs using the cardinality
of each finite nonempty fibre. Every analytic and modular hypothesis below is
explicit: this bridge does not assert existence of a modular node family.
-/

noncomputable section

open scoped UpperHalfPlane

namespace GapFamily

variable {ι : Type*}

/-- The spectrum of distinct coordinates, with their actual node counts. -/
def coordinateSpectrum (coordinate : ι → ℝ × ℝ) : Spectrum := by
  classical
  exact {
    support := Set.range coordinate
    multiplicity := fun p => if hp : p ∈ Set.range coordinate then
      Regrouping.multiplicity coordinate ⟨p, hp⟩ else 0 }

@[simp]
theorem coordinateSpectrum_support (coordinate : ι → ℝ × ℝ) :
    (coordinateSpectrum coordinate).support = Set.range coordinate := rfl

@[simp]
theorem coordinateSpectrum_multiplicity (coordinate : ι → ℝ × ℝ)
    (p : Set.range coordinate) :
    (coordinateSpectrum coordinate).multiplicity p =
      Regrouping.multiplicity coordinate p := by
  simp only [coordinateSpectrum, dite_eq_left p.property]

theorem coordinateSpectrum_multiplicity_pos {coordinate : ι → ℝ × ℝ}
    (hlocal : Regrouping.LocallyFinite coordinate dimension)
    (p : ℝ × ℝ) (hp : p ∈ (coordinateSpectrum coordinate).support) :
    0 < (coordinateSpectrum coordinate).multiplicity p := by
  exact (coordinateSpectrum_multiplicity coordinate ⟨p, hp⟩).symm ▸
    Regrouping.multiplicity_pos hlocal ⟨p, hp⟩

theorem coordinateSpectrum_locally_finite {coordinate : ι → ℝ × ℝ}
    (hlocal : Regrouping.LocallyFinite coordinate dimension) (D : ℝ) :
    {p ∈ (coordinateSpectrum coordinate).support | dimension p ≤ D}.Finite := by
  have heq : {p ∈ (coordinateSpectrum coordinate).support | dimension p ≤ D} =
      coordinate '' {i | dimension (coordinate i) ≤ D} := by
    ext p
    constructor
    · rintro ⟨⟨i, rfl⟩, hi⟩
      exact ⟨i, hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, rfl⟩, hi⟩
  rw [heq]
  exact (hlocal D).image coordinate

section RegroupedSum

variable {A : Type*} [NormedAddCommGroup A] [CompleteSpace A]

/-- Every summable coordinate-dependent node series remains summable. -/
theorem coordinateSpectrum_summable {coordinate : ι → ℝ × ℝ}
    (hlocal : Regrouping.LocallyFinite coordinate dimension) (term : (ℝ × ℝ) → A)
    (hsum : Summable (fun i => term (coordinate i))) :
    Summable (fun p : (coordinateSpectrum coordinate).support =>
      (coordinateSpectrum coordinate).multiplicity p • term p.val) := by
  simpa only [coordinateSpectrum_support, coordinateSpectrum_multiplicity] using
    Regrouping.summable_regroup hlocal term hsum

/-- The complex character series, or any summable coordinate series, is preserved. -/
theorem coordinateSpectrum_tsum {coordinate : ι → ℝ × ℝ}
    (hlocal : Regrouping.LocallyFinite coordinate dimension) (term : (ℝ × ℝ) → A)
    (hsum : Summable (fun i => term (coordinate i))) :
    (∑' p : (coordinateSpectrum coordinate).support,
      (coordinateSpectrum coordinate).multiplicity p • term p.val) =
      ∑' i, term (coordinate i) := by
  simpa only [coordinateSpectrum_support, coordinateSpectrum_multiplicity] using
    Regrouping.tsum_regroup hlocal term hsum

end RegroupedSum

/-- Coordinates reconstructed from energy and integer spin. -/
def nodeCoordinate (c : ℝ) (E : ι → ℝ) (J : ι → ℤ) (i : ι) : ℝ × ℝ :=
  ((shift c + E i + (J i : ℝ)) / 2, (shift c + E i - (J i : ℝ)) / 2)

def nodeSpectrum (c : ℝ) (E : ι → ℝ) (J : ι → ℤ) : Spectrum :=
  coordinateSpectrum (nodeCoordinate c E J)

@[simp]
theorem dimension_nodeCoordinate (c : ℝ) (E : ι → ℝ) (J : ι → ℤ) (i : ι) :
    dimension (nodeCoordinate c E J i) = shift c + E i := by
  dsimp [dimension, nodeCoordinate]
  ring

@[simp]
theorem energy_nodeCoordinate (c : ℝ) (E : ι → ℝ) (J : ι → ℤ) (i : ι) :
    energy c (nodeCoordinate c E J i) = E i := by
  simp [energy]

@[simp]
theorem spin_nodeCoordinate (c : ℝ) (E : ι → ℝ) (J : ι → ℤ) (i : ι) :
    spin (nodeCoordinate c E J i) = (J i : ℝ) := by
  dsimp [spin, nodeCoordinate]
  ring

theorem nodeCoordinate_locallyFinite (c : ℝ) (E : ι → ℝ) (J : ι → ℤ)
    (hlocal : ∀ B : ℝ, {i | E i ≤ B}.Finite) :
    Regrouping.LocallyFinite (nodeCoordinate c E J) dimension := by
  intro D
  have heq : {i | dimension (nodeCoordinate c E J i) ≤ D} =
      {i | E i ≤ D - shift c} := by
    ext i
    simp only [Set.mem_ofPred_eq, dimension_nodeCoordinate]
    constructor <;> intro h <;> linarith
  rw [heq]
  exact hlocal (D - shift c)

theorem nodeSpectrum_pure_bound (c : ℝ) (E : ι → ℝ) (J : ι → ℤ)
    (hcone : ∀ i, |(J i : ℝ)| ≤ E i) :
    ∀ p ∈ (nodeSpectrum c E J).support,
      shift c / 2 ≤ p.1 ∧ shift c / 2 ≤ p.2 := by
  rintro p ⟨i, rfl⟩
  apply (pure_bound_iff_energy_ge_abs_spin _ _).mpr
  simpa using hcone i

theorem nodeSpectrum_weight_pos {c : ℝ} (hc : 1 < c) (E : ι → ℝ) (J : ι → ℤ)
    (hcone : ∀ i, |(J i : ℝ)| ≤ E i) :
    ∀ p ∈ (nodeSpectrum c E J).support, 0 < p.1 ∧ 0 < p.2 := by
  intro p hp
  have h := nodeSpectrum_pure_bound c E J hcone p hp
  have hshift : 0 < shift c / 2 := by dsimp [shift]; linarith
  exact ⟨hshift.trans_le h.1, hshift.trans_le h.2⟩

theorem nodeSpectrum_spin_integral (c : ℝ) (E : ι → ℝ) (J : ι → ℤ) :
    ∀ p ∈ (nodeSpectrum c E J).support, ∃ j : ℤ, spin p = (j : ℝ) := by
  rintro p ⟨i, rfl⟩
  exact ⟨J i, spin_nodeCoordinate c E J i⟩

theorem nodeCoordinate_thermal_summable (c : ℝ) (E : ι → ℝ) (J : ι → ℤ)
    (y : ℝ) (hsum : Summable (fun i => Real.exp (-2 * Real.pi * y * E i))) :
    Summable (fun i => Real.exp (-2 * Real.pi * y *
      dimension (nodeCoordinate c E J i))) := by
  simp_rw [dimension_nodeCoordinate, mul_add, Real.exp_add]
  exact hsum.mul_left _

theorem nodeSpectrum_thermal_summable (c : ℝ) (E : ι → ℝ) (J : ι → ℤ)
    (hlocal : ∀ B : ℝ, {i | E i ≤ B}.Finite)
    (y : ℝ) (hsum : Summable (fun i => Real.exp (-2 * Real.pi * y * E i))) :
    Summable (fun p : (nodeSpectrum c E J).support =>
      ((nodeSpectrum c E J).multiplicity p : ℝ) *
        Real.exp (-2 * Real.pi * y * dimension p)) := by
  have h := Regrouping.summable_regroup (nodeCoordinate_locallyFinite c E J hlocal)
    (fun p => Real.exp (-2 * Real.pi * y * dimension p))
    (nodeCoordinate_thermal_summable c E J y hsum)
  simpa only [nodeSpectrum, coordinateSpectrum_support,
    coordinateSpectrum_multiplicity, nsmul_eq_mul] using h

/-- The thermal sum is preserved, including the common dimension shift. -/
theorem nodeSpectrum_thermal_tsum (c : ℝ) (E : ι → ℝ) (J : ι → ℤ)
    (hlocal : ∀ B : ℝ, {i | E i ≤ B}.Finite)
    (y : ℝ) (hsum : Summable (fun i => Real.exp (-2 * Real.pi * y * E i))) :
    (∑' p : (nodeSpectrum c E J).support,
      ((nodeSpectrum c E J).multiplicity p : ℝ) *
        Real.exp (-2 * Real.pi * y * dimension p)) =
      ∑' i, Real.exp (-2 * Real.pi * y * (shift c + E i)) := by
  have h := Regrouping.tsum_regroup (nodeCoordinate_locallyFinite c E J hlocal)
    (fun p => Real.exp (-2 * Real.pi * y * dimension p))
    (nodeCoordinate_thermal_summable c E J y hsum)
  simpa only [nodeSpectrum, coordinateSpectrum_support, coordinateSpectrum_multiplicity, nsmul_eq_mul,
    dimension_nodeCoordinate] using h

/-- The spectrum is fully admissible provided its actual character sum is modular. -/
theorem nodeSpectrum_pureAdmissible {c : ℝ} (hc : 1 < c)
    (E : ι → ℝ) (J : ι → ℤ)
    (hcone : ∀ i, |(J i : ℝ)| ≤ E i)
    (hlocal : ∀ B : ℝ, {i | E i ≤ B}.Finite)
    (hthermal : ∀ y : ℝ, 0 < y → Summable (fun i => Real.exp (-2 * Real.pi * y * E i)))
    (hS : ∀ τ : ℍ, partitionFunction c (nodeSpectrum c E J) (ModularGroup.S • τ) =
      partitionFunction c (nodeSpectrum c E J) τ)
    (hT : ∀ τ : ℍ, partitionFunction c (nodeSpectrum c E J) (ModularGroup.T • τ) =
      partitionFunction c (nodeSpectrum c E J) τ) :
    PureAdmissible c (nodeSpectrum c E J) := by
  refine ⟨⟨hc, nodeSpectrum_weight_pos hc E J hcone, ?_,
    nodeSpectrum_spin_integral c E J, ?_, ?_, hS, hT⟩,
    nodeSpectrum_pure_bound c E J hcone⟩
  · exact coordinateSpectrum_multiplicity_pos (nodeCoordinate_locallyFinite c E J hlocal)
  · exact coordinateSpectrum_locally_finite (nodeCoordinate_locallyFinite c E J hlocal)
  · intro y hy
    exact nodeSpectrum_thermal_summable c E J hlocal y (hthermal y hy)

/-- An energy lower bound and an actual marker give the exact public dimension gap. -/
theorem nodeSpectrum_hasGap (c : ℝ) (E : ι → ℝ) (J : ι → ℤ)
    (b : ℝ) (hlower : ∀ i, b ≤ E i) (hmarker : ∃ i, E i = b) :
    HasGap (nodeSpectrum c E J) (shift c + b) := by
  constructor
  · rintro p ⟨i, rfl⟩
    rw [dimension_nodeCoordinate]
    linarith [hlower i]
  · obtain ⟨i, hi⟩ := hmarker
    exact ⟨nodeCoordinate c E J i, ⟨i, rfl⟩, by simp [hi]⟩

end GapFamily
